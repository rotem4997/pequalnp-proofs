import PEqualNP.Defs

/- Adapted from the checked live-circuit normalization and search in L-meta-6349. -/

namespace PEqualNP.Outside.L_meta_8971

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

theorem build_mono {ops : α → α → Finset α} {goal : α} {k : ℕ} {s t : Finset α}
    (hsub : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hsub h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a, hsub ha, b, hsub hb, hab, z, hz, ih (Finset.insert_subset_insert z hsub) tail⟩

def liveChain (ops : α → α → Finset α) (goal : α) : List (α × α × α) → Finset α → Prop
  | [], s => s = {goal}
  | (a, b, z) :: gs, s =>
    a ∈ s ∧ b ∈ s ∧ a ≠ b ∧ z ∈ ops a b ∧ z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ liveChain ops goal gs (insert z rest)

theorem compress_chain {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) :
    ∃ gs : List (α × α × α), gs.length ≤ k ∧ ∃ s ⊆ available, liveChain ops goal gs s := by
  induction k generalizing available with
  | zero =>
    exact ⟨[], Nat.le_refl 0, {goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨gs, hlen, s, hs, hrun⟩ := ih skip
      exact ⟨gs, Nat.le_succ_of_le hlen, s, hs, hrun⟩
    · obtain ⟨gs, hlen, t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨gs, Nat.le_succ_of_le hlen, t, sub, hrun⟩
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
        refine ⟨(a, b, z) :: gs, Nat.succ_le_succ hlen, s, hs,
          by simp [s], by simp [s], hab, hz, fun h => hzout (hs h), rest, rfl, ?_⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem chain_to_build {ops : α → α → Finset α} {goal : α} {gs : List (α × α × α)} {s : Finset α}
    (h : liveChain ops goal gs s) : build ops goal gs.length s := by
  induction gs generalizing s with
  | nil => change s = {goal} at h; simp [build, h]
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨ha, hb, hab, hz, _, rest, hs, tail⟩
    refine Or.inr ⟨a, ha, b, hb, hab, z, hz, build_mono ?_ (ih tail)⟩
    intro u hu
    rw [hs]
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.mem_insert_self u _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))

theorem chain_card {ops : α → α → Finset α} {goal : α} {gs : List (α × α × α)} {s : Finset α}
    (h : liveChain ops goal gs s) : s.card ≤ gs.length + 1 := by
  induction gs generalizing s with
  | nil => change s = {goal} at h; simp [h]
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨_, _, _, _, hout, rest, rfl, tail⟩
    have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
    have htail := ih tail
    rw [Finset.card_insert_of_notMem hzrest] at htail
    have h₁ := Finset.card_insert_le a (insert b rest)
    have h₂ := Finset.card_insert_le b rest
    simp only [List.length_cons]
    omega

theorem chain_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {gs : List (α × α × α)} {s : Finset α} (h : liveChain ops goal gs s) : ∃ w ∈ s, D w := by
  induction gs generalizing s with
  | nil => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨ha, hb, _, hz, _, rest, rfl, tail⟩
    obtain ⟨w, hw, hD⟩ := ih tail
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rcases hops a b w hz hD with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    · exact ⟨w, by simp [hw], hD⟩

theorem swap_two {ops : α → α → Finset α} {goal : α}
    {g₁ g₂ : α × α × α} {gs : List (α × α × α)} {s₀ : Finset α}
    (h : liveChain ops goal (g₁ :: g₂ :: gs) s₀)
    (h1 : g₂.1 ≠ g₁.2.2) (h2 : g₂.2.1 ≠ g₁.2.2) :
    liveChain ops goal (g₂ :: g₁ :: gs) s₀ ∨ build ops goal (gs.length + 1) s₀ := by
  rcases g₁ with ⟨a₁, b₁, z₁⟩
  rcases g₂ with ⟨a₂, b₂, z₂⟩
  rcases h with ⟨ha₁, hb₁, hab₁, hz₁, hout₁, rest₁, hs₀,
                 ha₂, hb₂, hab₂, hz₂, hout₂, rest₂, hs₁, tail⟩
  dsimp only at h1 h2
  have hz₁_r₂ : z₁ ∈ rest₂ := by
    have hm : z₁ ∈ insert a₂ (insert b₂ rest₂) := hs₁ ▸ Finset.mem_insert_self z₁ rest₁
    rcases Finset.mem_insert.mp hm with h | hm
    · exact absurd h.symm h1
    · rcases Finset.mem_insert.mp hm with h | hm
      · exact absurd h.symm h2
      · exact hm
  let core := rest₂.erase z₁
  have hcore_eq : insert z₁ core = rest₂ := Finset.insert_erase hz₁_r₂
  have hz₁_core : z₁ ∉ core := Finset.notMem_erase z₁ rest₂
  have hz₁_r₁ : z₁ ∉ rest₁ := fun hm => hout₁ (hs₀ ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hr₁ : rest₁ = insert a₂ (insert b₂ core) := by
    ext u
    by_cases hu : u = z₁
    · subst hu
      simp [hz₁_r₁, h1.symm, h2.symm, hz₁_core]
    · have hmem : u ∈ insert z₁ rest₁ ↔ u ∈ insert a₂ (insert b₂ (insert z₁ core)) := by
        rw [hcore_eq, hs₁]
      simp [hu] at hmem
      simpa using hmem
  by_cases hz₂_s₀ : z₂ ∈ s₀
  · right
    refine Or.inr ⟨a₁, ha₁, b₁, hb₁, hab₁, z₁, hz₁, build_mono ?_ (chain_to_build tail)⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.mem_insert_of_mem hz₂_s₀
    · rw [← hcore_eq] at hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_insert_self u s₀
      · rw [hs₀, hr₁]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))))
  · left
    have hs₀' : s₀ = insert a₂ (insert b₂ (insert a₁ (insert b₁ core))) := by
      rw [hs₀, hr₁]
      ext u; simp [or_left_comm]
    have ha₂_s₀ : a₂ ∈ s₀ := by rw [hs₀']; simp
    have hb₂_s₀ : b₂ ∈ s₀ := by rw [hs₀']; simp
    have hz₁_ne_z₂ : z₁ ≠ z₂ := fun heq => hout₂ (heq ▸ Finset.mem_insert_self z₁ rest₁)
    have hs₁' : insert z₂ (insert a₁ (insert b₁ core)) = insert a₁ (insert b₁ (insert z₂ core)) := by
      ext u; simp [or_left_comm]
    have hz₁_out' : z₁ ∉ insert z₂ (insert a₁ (insert b₁ core)) := by
      intro hm
      rcases Finset.mem_insert.mp hm with h | hm
      · exact hz₁_ne_z₂ h
      · exact hout₁ (hs₀' ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    refine ⟨ha₂_s₀, hb₂_s₀, hab₂, hz₂, hz₂_s₀, insert a₁ (insert b₁ core), hs₀',
            by rw [hs₁']; simp, by rw [hs₁']; simp, hab₁, hz₁, hz₁_out', insert z₂ core, hs₁', ?_⟩
    have hs₂' : insert z₁ (insert z₂ core) = insert z₂ rest₂ := by
      rw [← hcore_eq, Finset.insert_comm]
    simpa only [hs₂'] using tail

def chainOrd (key : α → ℕ) : ℕ → List (α × α × α) → Prop
  | _, [] => True
  | last, (a, b, z) :: gs =>
    (key a = last ∨ key b = last ∨ last ≤ key z) ∧ chainOrd key (key z) gs

theorem swap_in_chain {ops : α → α → Finset α} {goal : α}
    (pre : List (α × α × α)) (g₁ g₂ : α × α × α) (suf : List (α × α × α)) {s : Finset α}
    (h : liveChain ops goal (pre ++ g₁ :: g₂ :: suf) s)
    (h1 : g₂.1 ≠ g₁.2.2) (h2 : g₂.2.1 ≠ g₁.2.2) :
    liveChain ops goal (pre ++ g₂ :: g₁ :: suf) s ∨ build ops goal (pre.length + suf.length + 1) s := by
  induction pre generalizing s with
  | nil =>
    simpa using swap_two h h1 h2
  | cons g pre ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨ha, hb, hab, hz, hout, rest, hs, tail⟩
    rcases ih tail with hswap | hshort
    · exact Or.inl ⟨ha, hb, hab, hz, hout, rest, hs, hswap⟩
    · right
      have hlen : ((a, b, z) :: pre).length + suf.length + 1 = (pre.length + suf.length + 1) + 1 := by
        simp; omega
      rw [hlen]
      refine Or.inr ⟨a, ha, b, hb, hab, z, hz, build_mono ?_ hshort⟩
      intro u hu
      rw [hs]
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_insert_self u _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))

omit [DecidableEq α] in
theorem find_violation (key : α → ℕ) (last : ℕ) (gs : List (α × α × α))
    (hstart : ∀ g gs', gs = g :: gs' → key g.1 = last ∨ key g.2.1 = last ∨ last ≤ key g.2.2) :
    chainOrd key last gs ∨
    ∃ pre g₁ g₂ suf, gs = pre ++ g₁ :: g₂ :: suf ∧
      key g₂.1 ≠ key g₁.2.2 ∧ key g₂.2.1 ≠ key g₁.2.2 ∧ key g₂.2.2 < key g₁.2.2 := by
  induction gs generalizing last with
  | nil => exact Or.inl trivial
  | cons g₁ rest ih =>
    have hg₁ := hstart g₁ rest rfl
    cases rest with
    | nil => exact Or.inl ⟨hg₁, trivial⟩
    | cons g₂ suf =>
      by_cases hok : key g₂.1 = key g₁.2.2 ∨ key g₂.2.1 = key g₁.2.2 ∨ key g₁.2.2 ≤ key g₂.2.2
      · rcases ih (key g₁.2.2) (fun g gs' heq => by cases heq; exact hok) with hord | ⟨pre, a, b, s', heq, h1, h2, hlt⟩
        · exact Or.inl ⟨hg₁, hord⟩
        · exact Or.inr ⟨g₁ :: pre, a, b, s', by simp [heq], h1, h2, hlt⟩
      · push_neg at hok
        exact Or.inr ⟨[], g₁, g₂, suf, rfl, hok.1, hok.2.1, hok.2.2⟩

end Live

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y].filter (fun z => z != 0 && z != BitVec.allOnes 128)

def sep (x : W) : BitVec 64 := ((x >>> 64) &&& ~~~x).setWidth 64

def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]

def inputs : List W := rawInputs

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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz.1 with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (64 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (64 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 64, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 128 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {gs : List (W × W × W)} {ws : List W} (h : liveChain basicOps goal gs ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := chain_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
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

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 128 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 128, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 128 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · by_cases h0 : x &&& y = 0
      · exact .inl h0
      · by_cases h1 : x &&& y = BitVec.allOnes 128
        · exact .inr (.inl h1)
        · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by
            simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons,
              List.not_mem_nil, or_false, Bool.and_eq_true, bne_iff_ne]
            exact ⟨by simp, h0, h1⟩⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · by_cases h0 : x ||| y = 0
      · exact .inl h0
      · by_cases h1 : x ||| y = BitVec.allOnes 128
        · exact .inr (.inl h1)
        · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by
            simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons,
              List.not_mem_nil, or_false, Bool.and_eq_true, bne_iff_ne]
            exact ⟨by simp, h0, h1⟩⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 128) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra last : ℕ) (next : ℕ → ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    if w == a || w == b || r.elem w || (a.toNat != last && b.toNat != last && w.toNat < last) then false
    else
      let v := sep w ||| base
      let wn := w.toNat
      ((v == -1) && next extra wn (w :: r)) ||
      ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) wn (w :: a :: r)) ||
                         ((v ||| sep b == -1) && next (extra - 1) wn (w :: b :: r)))) ||
      ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) wn (w :: a :: b :: r))

def optimized : ℕ → ℕ → ℕ → List W → Bool
  | 0, _, _, ws => ws == [goal]
  | 1, _, _, [a] => a == goal
  | 1, _, _, [a, b] => (a &&& b == goal) || (a ||| b == goal)
  | 1, _, _, _ => false
  | 2, _, _, [a] => a == goal
  | 2, _, _, [a, b] => a == goal || b == goal || (a &&& b == goal) || (a ||| b == goal)
  | 2, _, _, [a, b, c] =>
    (a &&& b &&& c == goal) || (a ||| b ||| c == goal) ||
    ((a &&& b) ||| c == goal) || ((a ||| b) &&& c == goal) ||
    ((a &&& c) ||| b == goal) || ((a ||| c) &&& b == goal) ||
    ((b &&& c) ||| a == goal) || ((b ||| c) &&& a == goal)
  | 2, _, _, _ => false
  | k + 3, extra, last, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra last (optimized (k + 2)) a b r)

theorem dispatch_complete {k extra last : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hna : z ≠ a) (hnb : z ≠ b) (hnr : z ∉ r)
    (hord : a.toNat = last ∨ b.toNat = last ∨ last ≤ z.toNat)
    (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) z.toNat (z :: kept) = true) :
    dispatch extra last next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  have hordb : (a.toNat != last && b.toNat != last && decide (z.toNat < last)) = false := by
    rcases hord with h | h | h
    · simp [h]
    · simp [h]
    · have : ¬ (z.toNat < last) := by omega
      simp [this]
  have hcond : (z == a || z == b || r.elem z || (a.toNat != last && b.toNat != last && decide (z.toNat < last))) = false := by
    simp [hna, hnb, hnr, hordb]
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem chain_one_pair {a b : W} {gs : List (W × W × W)}
    (h : liveChain basicOps goal gs {a, b}) (hab : a ≠ b) (hlen : gs.length ≤ 1) :
    goal ∈ basicOps a b := by
  cases gs with
  | nil =>
    change ({a, b} : Finset W) = {goal} at h
    have hc := congrArg Finset.card h
    rw [Finset.card_pair hab, Finset.card_singleton] at hc
    omega
  | cons g gs' =>
    cases gs' with
    | cons => simp at hlen
    | nil =>
      rcases g with ⟨x, y, z⟩
      rcases h with ⟨hx, hy, hxy, hz, hout, rest, hs, tail⟩
      change insert z rest = {goal} at tail
      have hzg : z = goal := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_self z rest)
      have hxy_ab : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨rfl, rfl⟩
        · exact absurd rfl hxy
      rcases hxy_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hzg ▸ hz
      · rw [ops_swap]; exact hzg ▸ hz

theorem optimized_one {ws : List W} {extra last : ℕ} {gs : List (W × W × W)}
    (hn : ws.Nodup) (hlen : gs.length ≤ 1) (h : liveChain basicOps goal gs ws.toFinset) :
    optimized 1 extra last ws = true := by
  have hc := chain_card h
  rw [List.toFinset_card_of_nodup hn] at hc
  match ws, hn, hc, h with
  | [], _, _, h =>
    cases gs with
    | nil => change ∅ = {goal} at h; simp at h
    | cons g _ => rcases g with ⟨a, _, _⟩; exact absurd h.1 (by simp)
  | [a], hn, _, h =>
    cases gs with
    | nil =>
      have : a = goal := by
        have hm : a ∈ ({goal} : Finset W) := h ▸ Finset.mem_singleton_self a
        exact Finset.mem_singleton.mp hm
      simp [optimized, this]
    | cons g _ =>
      rcases g with ⟨x, y, _⟩
      rcases h with ⟨hx, hy, hxy, _⟩
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  | [a, b], hn, _, h =>
    have hab : a ≠ b := (List.nodup_cons.mp hn).1 ∘ List.mem_singleton.mpr
    have hset : ([a, b] : List W).toFinset = {a, b} := by simp
    rw [hset] at h
    have hzg := chain_one_pair h hab hlen
    simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hzg
    simp only [optimized, Bool.or_eq_true, beq_iff_eq]
    exact hzg.1.imp Eq.symm Eq.symm
  | _ :: _ :: _ :: _, _, hc, _ => simp at hc; omega

theorem abs_ops {a b z : W} (hz : z ∈ basicOps a b) (w : W) (hw : w ∈ basicOps z a ∨ w ∈ basicOps z b) :
    w = a ∨ w = b ∨ w = (a &&& b) ∨ w = (a ||| b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz hw
  rcases hz.1 with rfl | rfl <;> rcases hw with (⟨rfl | rfl, _⟩) | (⟨rfl | rfl, _⟩)
  · right; right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; right; right; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; right; right; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)

theorem optimized_two {ws : List W} {extra last : ℕ} {gs : List (W × W × W)}
    (hn : ws.Nodup) (hlen : gs.length ≤ 2) (h : liveChain basicOps goal gs ws.toFinset) :
    optimized 2 extra last ws = true := by
  have hc := chain_card h
  rw [List.toFinset_card_of_nodup hn] at hc
  match ws, hn, hc, h with
  | [], _, _, h =>
    cases gs with
    | nil => change ∅ = {goal} at h; simp at h
    | cons g _ => rcases g with ⟨a, _, _⟩; exact absurd h.1 (by simp)
  | [a], hn, _, h =>
    cases gs with
    | nil =>
      have : a = goal := Finset.mem_singleton.mp (h ▸ Finset.mem_singleton_self a)
      simp [optimized, this]
    | cons g _ =>
      rcases g with ⟨x, y, _⟩
      rcases h with ⟨hx, hy, hxy, _⟩
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  | [a, b], hn, _, h =>
    have hab : a ≠ b := (List.nodup_cons.mp hn).1 ∘ List.mem_singleton.mpr
    have hset : ([a, b] : List W).toFinset = {a, b} := by simp
    rw [hset] at h
    cases gs with
    | nil =>
      change ({a, b} : Finset W) = {goal} at h
      have hcard := congrArg Finset.card h
      rw [Finset.card_pair hab, Finset.card_singleton] at hcard
      omega
    | cons g gs' =>
      rcases g with ⟨x, y, z⟩
      rcases h with ⟨hx, hy, hxy, hz, hout, rest, hs, tail⟩
      have hxy_ab : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨rfl, rfl⟩
        · exact absurd rfl hxy
      have hz_ab : z ∈ basicOps a b := by
        rcases hxy_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hz
        · rw [ops_swap]; exact hz
      cases gs' with
      | nil =>
        change insert z rest = {goal} at tail
        have hzg : z = goal := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_self z rest)
        have hmem : goal ∈ basicOps a b := hzg ▸ hz_ab
        simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [optimized, Bool.or_eq_true, beq_iff_eq]
        rcases hmem.1 with h1 | h2
        · left; right; exact h1.symm
        · right; exact h2.symm
      | cons g2 gs'' =>
        cases gs'' with
        | cons => simp at hlen
        | nil =>
          have hsub : rest ⊆ {a, b} := by
            intro u hu; rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
          have hcard2 := chain_card tail
          have hzrest : z ∉ rest := fun hm => hout (hsub hm)
          rw [Finset.card_insert_of_notMem hzrest] at hcard2
          simp only [List.length_singleton] at hcard2
          have hrest1 : rest.card = 1 := by
            by_cases he : rest = ∅
            · subst he
              rcases g2 with ⟨u, v, _⟩
              rcases tail with ⟨hu, hv, huv, _⟩
              simp at hu hv
              exact absurd (hu.trans hv.symm) huv
            · have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he); omega
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hrest1
          rw [hw] at tail hsub
          have hw_ab : w = a ∨ w = b := by
            have := hsub (Finset.mem_singleton_self w); simpa using this
          have hzw : z ≠ w := fun heq => hout (heq ▸ hsub (Finset.mem_singleton_self w))
          have hzg := chain_one_pair (by simpa [insert_empty_eq] using tail) hzw (by simp)
          have hres := abs_ops hz_ab goal (hw_ab.elim (fun h => .inl (h ▸ hzg)) (fun h => .inr (h ▸ hzg)))
          simp only [optimized, Bool.or_eq_true, beq_iff_eq]
          rcases hres with h1 | h2 | h3 | h4
          · left; left; left; exact h1.symm
          · left; left; right; exact h2.symm
          · left; right; exact h3.symm
          · right; exact h4.symm
  | [a, b, c], hn, _, h =>
    have hnd1 := List.nodup_cons.mp hn
    have hnd2 := List.nodup_cons.mp hnd1.2
    have hab : a ≠ b := fun heq => hnd1.1 (by simp [heq])
    have hac : a ≠ c := fun heq => hnd1.1 (by simp [heq])
    have hbc : b ≠ c := fun heq => hnd2.1 (by simp [heq])
    have hlen2 : gs.length = 2 := by
      have hc' := chain_card h
      rw [List.toFinset_card_of_nodup hn] at hc'
      simp at hc'; omega
    match gs, hlen2, h with
    | [(x, y, z), g2], _, h =>
      rcases h with ⟨hx, hy, hxy, hz, hout, rest, hs, tail⟩
      have hcard2 := chain_card tail
      have hzrest : z ∉ rest := fun hm => hout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
      rw [Finset.card_insert_of_notMem hzrest] at hcard2
      simp only [List.length_singleton] at hcard2
      have hset3 : ([a, b, c] : List W).toFinset = {a, b, c} := by simp
      rw [hset3] at hs hx hy hout
      have hcard3 : ({a, b, c} : Finset W).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
      have hrest1 : rest.card = 1 := by
        have h1 := Finset.card_insert_le x (insert y rest)
        have h2 := Finset.card_insert_le y rest
        rw [← hs, hcard3] at h1
        omega
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hrest1
      rw [hw] at hs tail
      have hzw : z ≠ w := fun heq => hout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (heq ▸ Finset.mem_singleton_self w)))
      have hzg := chain_one_pair (by simpa [insert_empty_eq] using tail) hzw (by simp)
      have htri : (z ∈ basicOps a b ∧ w = c) ∨ (z ∈ basicOps a c ∧ w = b) ∨ (z ∈ basicOps b c ∧ w = a) := by
        have hwx : w ≠ x := by
          intro heq; subst heq
          have : (insert w (insert y ({w} : Finset W))).card ≤ 2 := by
            rw [Finset.insert_comm, show insert w ({w} : Finset W) = {w} by simp]
            exact Finset.card_insert_le y {w}
          rw [← hs, hcard3] at this; omega
        have hwy : w ≠ y := by
          intro heq; subst heq
          have : (insert x (insert w ({w} : Finset W))).card ≤ 2 := by
            rw [show insert w ({w} : Finset W) = {w} by simp]
            exact Finset.card_insert_le x {w}
          rw [← hs, hcard3] at this; omega
        have hwm : w ∈ ({a, b, c} : Finset W) := hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hwm
        rcases hwm with rfl | rfl | rfl
        · rcases hx with rfl | rfl | rfl
          · exact absurd rfl hwx
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hwy
            · exact absurd rfl hxy
            · exact .inr (.inr ⟨hz, rfl⟩)
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hwy
            · exact .inr (.inr ⟨ops_swap _ _ ▸ hz, rfl⟩)
            · exact absurd rfl hxy
        · rcases hx with rfl | rfl | rfl
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hxy
            · exact absurd rfl hwy
            · exact .inr (.inl ⟨hz, rfl⟩)
          · exact absurd rfl hwx
          · rcases hy with rfl | rfl | rfl
            · exact .inr (.inl ⟨ops_swap _ _ ▸ hz, rfl⟩)
            · exact absurd rfl hwy
            · exact absurd rfl hxy
        · rcases hx with rfl | rfl | rfl
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hxy
            · exact .inl ⟨hz, rfl⟩
            · exact absurd rfl hwy
          · rcases hy with rfl | rfl | rfl
            · exact .inl ⟨ops_swap _ _ ▸ hz, rfl⟩
            · exact absurd rfl hxy
            · exact absurd rfl hwy
          · exact absurd rfl hwx
      simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at htri hzg
      simp only [optimized, Bool.or_eq_true, beq_iff_eq]
      rcases htri with ⟨⟨hz1 | hz1, _⟩, rfl⟩ | ⟨⟨hz1 | hz1, _⟩, rfl⟩ | ⟨⟨hz1 | hz1, _⟩, rfl⟩ <;>
        (subst hz1; rcases hzg.1 with hzg | hzg)
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl hzg.symm))))))
      · exact .inl (.inl (.inl (.inl (.inl (.inr hzg.symm)))))
      · exact .inl (.inl (.inl (.inl (.inr hzg.symm))))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr hzg.symm))))))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (by rw [hzg]; ac_rfl)))))))
      · exact .inl (.inl (.inl (.inr hzg.symm)))
      · exact .inl (.inl (.inr hzg.symm))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr (by rw [hzg]; ac_rfl)))))))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (by rw [hzg]; ac_rfl)))))))
      · exact .inl (.inr hzg.symm)
      · exact .inr hzg.symm
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr (by rw [hzg]; ac_rfl)))))))
  | _ :: _ :: _ :: _ :: _, _, hc, _ => simp at hc; omega

theorem optimized_complete (n : ℕ) (ws : List W) (extra last : ℕ) (gs : List (W × W × W))
    (hn : ws.Nodup) (hlen : gs.length ≤ n)
    (room : extra + ws.length = n + 1)
    (hord : chainOrd BitVec.toNat last gs)
    (h : liveChain basicOps goal gs ws.toFinset) :
    optimized n extra last ws = true := by
  induction n generalizing ws extra last gs with
  | zero =>
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hnil
    simp [optimized, singleton_list hn h]
  | succ k ih =>
    cases k with
    | zero => exact optimized_one hn hlen h
    | succ m =>
      cases m with
      | zero => exact optimized_two hn hlen h
      | succ p =>
        cases gs with
        | nil => simp [optimized, singleton_list hn h]
        | cons g gs' =>
          rcases g with ⟨a, b, z⟩
          rcases h with ⟨ha, hb, hab, hz, hout, needed, hs, tail⟩
          rcases hord with ⟨hg_ord, hgs_ord⟩
          obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
          have go {a b : W} (perm : ws.Perm (a :: b :: r))
              (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b)
              (hord' : a.toNat = last ∨ b.toNat = last ∨ last ≤ z.toNat) :
              dispatch extra last (optimized (p + 2)) a b r = true := by
            obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
            have hzws : z ∉ a :: b :: r := fun hu => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hu))
            have hna : z ≠ a := fun h => hzws (h ▸ List.mem_cons_self)
            have hnb : z ≠ b := fun h => hzws (List.mem_cons_of_mem _ (h ▸ List.mem_cons_self))
            have hnr : z ∉ r := fun h => hzws (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
            have hznew : z ∉ kept := by
              intro hu
              apply hout
              rw [hset]
              exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
            have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
            have hl : liveChain basicOps goal gs' (z :: kept).toFinset := by
              simpa [hfin] using tail
            have hlen' : gs'.length ≤ p + 2 := by simp at hlen; omega
            have hc := chain_card hl
            rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
            have len := perm.length_eq
            simp only [List.length_cons] at len
            apply dispatch_complete (k := p + 2) (extra := extra) (last := last) (optimized (p + 2))
              hop hna hnb hnr hord' hk (by omega) (by omega) (cuts_full hl)
            apply ih _ _ _ gs' hnd hlen' _ hgs_ord hl
            simp; omega
          simp only [optimized, Bool.or_eq_true, List.any_eq_true]
          right
          rcases hm with direct | swap
          · exact ⟨(a, b, r), direct, go hp hs hz hg_ord⟩
          · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
              (ops_swap a b ▸ hz) (by rcases hg_ord with h | h | h; exact .inr (.inl h); exact .inl h; exact .inr (.inr h))⟩

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (13740 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) := [(0, 2), (0, 3), (1, 1), (1, 3), (2, 0), (2, 2), (3, 0), (3, 1)]

def negL : List (Fin 4 × Fin 4) := [(0, 0), (0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 3)]

def samp (k : Fin 128) : Fin 4 × Fin 4 :=
  if k.val < 64 then negL.getD (k.val % 8) (0, 0) else posL.getD (((k.val - 64) / 8) % 8) (0, 0)

theorem input_rows : ∀ k : Fin 128,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 128, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 128) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem inputs_nodup : inputs.Nodup := by decide +kernel



set_option maxRecDepth 16000 in
def orders : Array Nat := #[0xffef7cefae78df6d74cf2c70beeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040, 0x7dd79b7196983cd38b309288bedbabb29aa81c5183101080ffdfbbf39eb85d5593511490df5db3d31cb09e59a39218a0, 0xdb7cf2d74c31fbfefaf7ce3979f6da75c6195974d2554411bafaeab6ca299a78e29648211870c214400138f2ca34c209, 0xbabbedaa8b291831c508010179b7dd69871938b3cd288309db3df5cb0d319a39e58a0921fbbffdeb8f395935d5490511, 0xb6cbeea68aea9649e68608e2f7cffee78efad74df6c70cf234c3ce2482ca1441c60400c275c7de6586da5545d64504d2, 0x34f30938b20a75f71979b61af7ff39fbbe3a557511593412b6fb29baba2a1471011830029679219a3822d77d31db3c32, 0x6da79f61975c4d2597411554cf2db7c31d74efafbfe39f7c0c21870011442ca38f20934caeabafa29b6c8e29a7821964, 0xc60801c5044aeeaa8beda6ccf6cb0df5c748e68a09e58646de6987dd65c2ce2883cd24c4d64905d5454efeeb8ffde7c, 0x9258609e68a3b2da68beeaab30d2483ce28b1050401c6083f3de78ffeebbd35c70df6cb35154505d649371d6587de69b, 0xf39f7fe3afbb51155741259330934f20a38b71975f61a79b9219678229a3d31d77c32db3b29b6fa2abab101147002183, 0x49341159751569b61979f71d08300118710528b20938f30dcb3c31db7d35ebbe39fbff3d8a38219a7925aaba29bafb2d, 0xcb0cf6c74df58a08e68649e50800c60441c5aa8aeea6cbed4904d64545d5eb8efee7cffd6986de65c7dd2882ce24c3cd, 0x24830d28b3ce0401050831c68609258a39e6a68b2daabbee4505154935d665871d69b7dee78f3debbffec70d35cb3df6, 0x4544125574d6e7ce3af7fefe8648229678e6c74c32d77cf624c20a34f2ce65c61a75f6de0440021470c6a6ca2ab6faee, 0x108310518720928b30d38f41149351559761969b71d79f8218a39259a7a29aabb2dbafc31cb3d35db7e39ebbf3dfbf, 0x8228648e6967c32c74cf6d774124544d6557e3ae7cefef7f0020440c6147a2aa6caeeb6f20a24c2ce34f61a65c6de75f]

set_option maxRecDepth 16000 in
def invNumbers : Array (Fin 16) := #[0, 1, 2, 5, 4, 3, 8, 7, 6, 9, 10, 13, 12, 11, 14, 15]

set_option maxRecDepth 16000 in
def invSym (g : Fin 16) : Fin 16 := invNumbers[g.val]?.getD 0

set_option maxRecDepth 16000 in
def slot (g : Fin 16) (k : Fin 128) : Fin 128 :=
  let off := (orders[g.val]?.getD 0 >>> (6 * (k.val % 64))) % 64
  ⟨if k.val < 64 then off else 64 + off, by dsimp [off]; split <;> omega⟩

set_option maxRecDepth 16000 in
def aut (g : Fin 16) (x : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun k : Fin 128 => x.getLsbD (slot g k).val)).cast List.length_ofFn

set_option maxRecDepth 16000 in
theorem aut_bit (g : Fin 16) (x : W) (k : Fin 128) :
    (aut g x).getLsbD k.val = x.getLsbD (slot g k).val := by
  simp only [aut, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using k.isLt), List.getElem_ofFn]

set_option maxRecDepth 16000 in
theorem slot_inv : ∀ (g : Fin 16) (k : Fin 128), slot g (slot (invSym g) k) = k := by
  decide +kernel

set_option maxRecDepth 16000 in
theorem aut_left (g : Fin 16) (x : W) : aut (invSym g) (aut g x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := aut_bit (invSym g) (aut g x) ⟨i, hi⟩
  exact hh.trans ((aut_bit g x (slot (invSym g) ⟨i,hi⟩)).trans (by rw [slot_inv]))

set_option maxRecDepth 16000 in
theorem aut_inj (g : Fin 16) : Function.Injective (aut g) := by
  intro x y h
  simpa only [aut_left] using congrArg (aut (invSym g)) h

set_option maxRecDepth 16000 in
theorem aut_goal : ∀ g : Fin 16, aut g goal = goal := by
  decide +kernel

set_option maxRecDepth 16000 in
theorem aut_inputs : ∀ g : Fin 16, inputs.all (fun x => (inputs.elem (aut g x))) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
theorem aut_and (g : Fin 16) (a b : W) : aut g (a &&& b) = aut g a &&& aut g b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa only [BitVec.getLsbD_and] using
    (aut_bit g (a &&& b) ⟨i,hi⟩).trans (by rw [BitVec.getLsbD_and, ← aut_bit, ← aut_bit])

set_option maxRecDepth 16000 in
theorem aut_or (g : Fin 16) (a b : W) : aut g (a ||| b) = aut g a ||| aut g b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa only [BitVec.getLsbD_or] using
    (aut_bit g (a ||| b) ⟨i,hi⟩).trans (by rw [BitVec.getLsbD_or, ← aut_bit, ← aut_bit])

set_option maxRecDepth 16000 in
theorem aut_zero (g : Fin 16) : aut g 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa using aut_bit g 0 ⟨i,hi⟩

set_option maxRecDepth 16000 in
theorem aut_ones (g : Fin 16) : aut g (BitVec.allOnes 128) = BitVec.allOnes 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (aut g (BitVec.allOnes 128)).getLsbD i = _ from aut_bit g _ ⟨i,hi⟩, BitVec.getLsbD_eq_getElem (slot g ⟨i,hi⟩).isLt, BitVec.getLsbD_eq_getElem hi, BitVec.getElem_allOnes, BitVec.getElem_allOnes]

set_option maxRecDepth 16000 in
theorem aut_ops (g : Fin 16) {a b z : W} (hz : z ∈ basicOps a b) :
    aut g z ∈ basicOps (aut g a) (aut g b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil,
    or_false, Bool.and_eq_true, bne_iff_ne] at hz ⊢
  refine ⟨?_, fun h => hz.2.1 (aut_inj g (h.trans (aut_zero g).symm)),
    fun h => hz.2.2 (aut_inj g (h.trans (aut_ones g).symm))⟩
  rcases hz.1 with rfl | rfl
  · exact .inl (aut_and g a b)
  · exact .inr (aut_or g a b)

set_option maxRecDepth 16000 in
abbrev WGate := W × W × W

set_option maxRecDepth 16000 in
def moveGate (g : Fin 16) (v : WGate) : WGate := (aut g v.1, aut g v.2.1, aut g v.2.2)

set_option maxRecDepth 16000 in
theorem move_chain (g : Fin 16) {gs : List WGate} {s : Finset W}
    (h : liveChain basicOps goal gs s) :
    liveChain basicOps goal (gs.map (moveGate g)) (s.image (aut g)) := by
  induction gs generalizing s with
  | nil =>
    change s = {goal} at h
    change s.image (aut g) = {goal}
    simp [h, aut_goal]
  | cons v gs ih =>
    rcases v with ⟨a,b,z⟩
    rcases h with ⟨ha,hb,hab,hz,hn,rest,hs,ht⟩
    refine ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb,
      fun eq => hab (aut_inj g eq), aut_ops g hz, ?_, rest.image (aut g), ?_, ?_⟩
    · intro hm
      obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp hm
      have hux : u = z := aut_inj g eq
      exact hn (hux ▸ hu)
    · rw [hs, Finset.image_insert, Finset.image_insert]
    · simpa only [Finset.image_insert] using ih ht

set_option maxRecDepth 16000 in
def gateKeys (gs : List WGate) : List ℕ := gs.map (fun v => v.2.2.toNat)

set_option maxRecDepth 16000 in
def canonical : List W → List WGate → Prop
  | _, [] => True
  | rev, v :: vs =>
    (∀ g : Fin 16, (∀ w ∈ rev, aut g w = w) → v.2.2.toNat ≤ (aut g v.2.2).toNat) ∧
    canonical (v.2.2 :: rev) vs

set_option maxRecDepth 16000 in
theorem canon_of_lex (gs : List WGate) (rev : List W)
    (hm : ∀ g : Fin 16, (∀ w ∈ rev, aut g w = w) →
      ¬ List.Lex (· < ·) (gateKeys (gs.map (moveGate g))) (gateKeys gs)) : canonical rev gs := by
  induction gs generalizing rev with
  | nil => trivial
  | cons v vs ih =>
    constructor
    · intro g hf
      exact le_of_not_gt (fun hl => hm g hf (.rel hl))
    · apply ih
      intro g hf hl
      have hv := hf v.2.2 (List.mem_cons_self)
      apply hm g (fun w hw => hf w (List.mem_cons_of_mem _ hw))
      change List.Lex (· < ·) ((aut g v.2.2).toNat :: _) (v.2.2.toNat :: _)
      rw [hv]
      exact .cons hl

set_option maxRecDepth 16000 in
private theorem min_keys (n : ℕ) (P : List ℕ → Prop)
    (h : ∃ v, P v ∧ v.length = n) :
    ∃ v, P v ∧ v.length = n ∧ ∀ u, P u → u.length = n → ¬ List.Lex (· < ·) u v := by
  classical
  induction n generalizing P with
  | zero =>
    obtain ⟨v,hv,hlen⟩ := h
    have e : v = [] := List.eq_nil_of_length_eq_zero hlen
    subst v
    exact ⟨[],hv,rfl,fun u _ hu hlex => by
      have := List.eq_nil_of_length_eq_zero hu
      subst u
      cases hlex⟩
  | succ n ih =>
    let has (x : ℕ) := ∃ us : List ℕ, P (x :: us) ∧ us.length = n
    have hh : ∃ x, has x := by
      obtain ⟨v,hv,hlen⟩ := h
      cases v with
      | nil => simp at hlen
      | cons x us => exact ⟨x,us,hv,by simpa using hlen⟩
    let x := Nat.find hh
    obtain ⟨us,hp,hlen,hmin⟩ := ih (fun t => P (x :: t)) (Nat.find_spec hh)
    refine ⟨x :: us,hp,by simp [hlen],?_⟩
    intro v hv hvlen hlex
    cases v with
    | nil => simp at hvlen
    | cons y vs =>
      have hvlen' : vs.length = n := by simpa using hvlen
      have hxy : x ≤ y := Nat.find_min' hh ⟨vs,hv,hvlen'⟩
      cases hlex with
      | rel e => omega
      | cons e => exact hmin _ hv hvlen' e

set_option maxRecDepth 16000 in
theorem canonComplete {k : ℕ} (hb : build basicOps goal k inputs.toFinset) :
    ∃ gs : List WGate, gs.length ≤ k ∧ chainOrd BitVec.toNat 0 gs ∧ canonical [] gs ∧
      ∃ s ⊆ inputs.toFinset, liveChain basicOps goal gs s := by
  classical
  let Good (gs : List WGate) := ∃ s ⊆ inputs.toFinset, liveChain basicOps goal gs s
  let Has (n : ℕ) := ∃ gs : List WGate, Good gs ∧ gs.length = n
  obtain ⟨init,hinit,si,hsi,hi⟩ := compress_chain hb
  have H : ∃ n, Has n := ⟨init.length,init,⟨si,hsi,hi⟩,rfl⟩
  let m := Nat.find H
  have eqm : Has m := Nat.find_spec H
  let P (keys : List ℕ) := ∃ gs : List WGate, Good gs ∧ gateKeys gs = keys
  obtain ⟨g0,h0,hlen0⟩ := eqm
  have hkeys : ∃ keys, P keys ∧ keys.length = m :=
    ⟨gateKeys g0,⟨g0,h0,rfl⟩,by simpa [gateKeys] using hlen0⟩
  obtain ⟨keys,⟨gs,hg,rfl⟩,hklen,minimal⟩ := min_keys m P hkeys
  have len : gs.length = m := by simpa [gateKeys] using hklen
  have least (ts : List WGate) (ht : Good ts) : gs.length ≤ ts.length := by
    rw [len]
    exact Nat.find_min' H ⟨ts,ht,rfl⟩
  have minlex (ts : List WGate) (ht : Good ts) (hl : ts.length = gs.length) :
      ¬ List.Lex (· < ·) (gateKeys ts) (gateKeys gs) :=
    minimal _ ⟨ts,ht,rfl⟩ (by simpa only [gateKeys, List.length_map, hl] using len)
  obtain ⟨s,hs,hlive⟩ := hg
  refine ⟨gs,(least init ⟨si,hsi,hi⟩).trans hinit,?_,?_,s,hs,hlive⟩
  · rcases find_violation BitVec.toNat 0 gs (fun _ _ _ => .inr (.inr (Nat.zero_le _))) with
      ok | ⟨pre,g₁,g₂,suf,heq,h1,h2,hinv⟩
    · exact ok
    · obtain hswap | hshort := swap_in_chain pre g₁ g₂ suf (heq ▸ hlive)
        (fun e => h1 (congrArg BitVec.toNat e)) (fun e => h2 (congrArg BitVec.toNat e))
      · exfalso
        apply minlex (pre ++ g₂ :: g₁ :: suf) ⟨s,hs,hswap⟩ (by simp [heq])
        simp only [heq,gateKeys,List.map_append,List.map_cons]
        exact List.Lex.append_left _ (.rel hinv) _
      · obtain ⟨short,hlen,s',hsub,hl⟩ := compress_chain (build_mono hs hshort)
        have hbad := least short ⟨s',hsub,hl⟩
        simp only [heq,List.length_append,List.length_cons] at hbad
        omega
  · apply canon_of_lex
    intro g _
    apply minlex _ ?_ (List.length_map ..)
    refine ⟨s.image (aut g),?_,move_chain g hlive⟩
    intro x hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
    apply List.mem_toFinset.mpr
    simpa only [List.elem_eq_mem, decide_eq_true_eq] using
      (List.all_eq_true.mp (aut_inputs g) w (List.mem_toFinset.mp (hs hw)))

section SymmetrySearch
variable (allowed : List W → W → Bool)

set_option maxRecDepth 16000 in
def symSearch : ℕ → ℕ → List W → ℕ → ℕ → List W → Bool
  | 0, k, _, extra, last, ws => optimized k extra last ws
  | m + 1, k, rev, extra, last, ws => ws == [goal] || (pairs ws).any fun (a, b, r) =>
      dispatch extra last (fun e w ts => allowed rev (BitVec.ofNat 128 w) &&
        symSearch m k (BitVec.ofNat 128 w :: rev) e w ts) a b r

variable (allowed_of_min : ∀ (rev : List W) (z : W),
  (∀ i : Fin 16, (∀ w ∈ rev, aut i w = w) → z.toNat ≤ (aut i z).toNat) → allowed rev z = true)

include allowed_of_min in
set_option maxRecDepth 16000 in
theorem symComplete (m k : ℕ) (rev ws : List W) (extra last : ℕ) (gs : List WGate)
    (hn : ws.Nodup) (hlen : gs.length ≤ m+k) (room : extra+ws.length = m+k+1)
    (hord : chainOrd BitVec.toNat last gs) (hc : canonical rev gs)
    (h : liveChain basicOps goal gs ws.toFinset) :
    symSearch allowed m k rev extra last ws = true := by
  induction m generalizing rev ws extra last gs with
  | zero =>
    exact optimized_complete k ws extra last gs hn (by omega) (by omega) hord h
  | succ m ih =>
    cases gs with
    | nil => simp [symSearch, singleton_list hn h]
    | cons g gs' =>
      rcases g with ⟨a,b,z⟩
      rcases hc with ⟨hgate,hcan⟩
      rcases h with ⟨ha,hb,hab,hz,hout,needed,hs,tail⟩
      rcases hord with ⟨hg_ord,hgs_ord⟩
      obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      let next (e w : ℕ) (ts : List W) := allowed rev (BitVec.ofNat 128 w) &&
        symSearch allowed m k (BitVec.ofNat 128 w :: rev) e w ts
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b)
          (hord' : a.toNat = last ∨ b.toNat = last ∨ last ≤ z.toNat) :
          dispatch extra last next a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hzws : z ∉ a :: b :: r := fun hu => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hu))
        have hna : z ≠ a := fun hh => hzws (hh ▸ List.mem_cons_self)
        have hnb : z ≠ b := fun hh => hzws (List.mem_cons_of_mem _ (hh ▸ List.mem_cons_self))
        have hnr : z ∉ r := fun hu => hzws (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu))
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : liveChain basicOps goal gs' (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hlen' : gs'.length ≤ m + k := by simp at hlen; omega
        have hcard := chain_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hcard
        have hperm := perm.length_eq
        simp only [List.length_cons] at hperm
        apply dispatch_complete (k := m+k) (extra := extra) (last := last) next hop
          hna hnb hnr hord' hk (by omega) (by omega) (cuts_full hl)
        have hword : BitVec.ofNat 128 z.toNat = z := by simp
        simp only [next, hword, allowed_of_min rev z hgate, Bool.true_and]
        apply ih _ _ _ _ gs' hnd hlen' _ hgs_ord hcan hl
        simp; omega
      simp only [symSearch, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r),direct,go hp hs hz hg_ord⟩
      · exact ⟨(b,a,r),swap,go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm])
          (ops_swap a b ▸ hz) (by rcases hg_ord with h | h | h; exact .inr (.inl h); exact .inl h; exact .inr (.inr h))⟩

end SymmetrySearch

-- Every discarded (history, value) has a specific symmetry witness.
set_option maxRecDepth 16000 in
structure RejectedWord where
  rev : List W
  val : W
  g : Fin 16
  fixes : ∀ w ∈ rev, aut g w = w
  lower : (aut g val).toNat < val.toNat

set_option maxRecDepth 16000 in
def makeRejected (rev : List W) (val : W) (g : Fin 16)
    (fixes : rev.all (fun w => aut g w == w) = true)
    (lower : (aut g val).toNat < val.toNat) : RejectedWord :=
  ⟨rev, val, g, fun w hw => beq_iff_eq.mp (List.all_eq_true.mp fixes w hw), lower⟩

set_option maxRecDepth 16000 in
def rejectKey (rev : List W) (z : W) : Nat :=
  rev.foldl (fun h w => (h * 65599 + w.toNat % 1000003) % 4294967291) (z.toNat % 4294967291)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_1 : aut 1 (0x101010101010101 : W) = (0x101010101010101 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_16 : aut 1 (0x404040404040404 : W) = (0x202020202020202 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_256 : aut 1 (0xff000000000000000000000000 : W) = (0xff0000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_512 : aut 1 (0x1010101010101010 : W) = (0x808080808080808 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_3841 : aut 1 (0xffff000000003131313131313131 : W) = (0xff00000000ff4949494949494949 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_4096 : aut 1 (0xff0000000000000000000000000000 : W) = (0xff000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_4383 : aut 1 (0xff00ff0000ffff0707070707070707 : W) = (0xff00ff0000ffff0707070707070707 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_7953 : aut 1 (0xffffff000000003535353535353535 : W) = (0xff000000ffff4b4b4b4b4b4b4b4b : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_8192 : aut 1 (0xff000000000000000000000000000000 : W) = (0xff0000000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_8739 : aut 1 (0xff00000000ff00001313131313131313 : W) = (0xffff00000d0d0d0d0d0d0d0d : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_8751 : aut 1 (0xff00000000ffffff1313131313131313 : W) = (0xff00ffffff00000d0d0d0d0d0d0d0d : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_12066 : aut 1 (0xff00ffff00ff00003232323232323232 : W) = (0xff00ffff00ff4c4c4c4c4c4c4c4c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_13107 : aut 1 (0xffff00ff00ff00001717171717171717 : W) = (0xffffffff0f0f0f0f0f0f0f0f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_16384 : aut 1 (0x4040404040404040 : W) = (0x2020202020202020 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_21845 : aut 1 (0xffffff000000ff4d4d4d4d4d4d4d4d : W) = (0xffff0000ffff3333333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_26214 : aut 1 (0xff00ff0000ff00ff5a5a5a5a5a5a5a5a : W) = (0xffffffff00003c3c3c3c3c3c3c3c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61441 : aut 1 (0xffff000000000000c1c1c1c1c1c1c1c1 : W) = (0xff00ff00a1a1a1a1a1a1a1a1 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61455 : aut 1 (0xffff00000000ffffc3c3c3c3c3c3c3c3 : W) = (0xff00ffff00ff00a5a5a5a5a5a5a5a5 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61680 : aut 1 (0xffff0000ffff0000cccccccccccccccc : W) = (0xff000000ffffff00b2b2b2b2b2b2b2b2 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61713 : aut 1 (0xffff00ff00000000c5c5c5c5c5c5c5c5 : W) = (0xff00ffffa3a3a3a3a3a3a3a3 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61986 : aut 1 (0xffff000000ff0000d2d2d2d2d2d2d2d2 : W) = (0xffffff00acacacacacacacac : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_62532 : aut 1 (0xffffff00000000ffc8c8c8c8c8c8c8c8 : W) = (0xffffff00ff00b0b0b0b0b0b0b0b0 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_63624 : aut 1 (0xffff0000ff00ff00e0e0e0e0e0e0e0e0 : W) = (0xffff0000ff00ff00e0e0e0e0e0e0e0e0 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_65280 : aut 1 (0xffffffff00000000f0f0f0f0f0f0f0f0 : W) = (0xff00ff00ffffe8e8e8e8e8e8e8e8 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_2 : aut 2 (0x202020202020202 : W) = (0x101010101010101 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_8 : aut 2 (0xff000000000000000000 : W) = (0xff0000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_272 : aut 2 (0xff000000000404040404040404 : W) = (0xff00001010101010101010 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_1024 : aut 2 (0xff00000000000000000000000000 : W) = (0xff0000000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_1088 : aut 2 (0xff00000000000808080808080808 : W) = (0xff0000002020202020202020 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_1092 : aut 2 (0xff00000000ff0808080808080808 : W) = (0xff00ff002020202020202020 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_2048 : aut 2 (0x2020202020202020 : W) = (0x808080808080808 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_3855 : aut 2 (0xffff0000ffff3333333333333333 : W) = (0xffffffff0f0f0f0f0f0f0f0f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_4080 : aut 2 (0xffffffff00003c3c3c3c3c3c3c3c : W) = (0xffffffff00003c3c3c3c3c3c3c3c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_4095 : aut 2 (0xffffffffffff3f3f3f3f3f3f3f3f : W) = (0xffffffffffff3f3f3f3f3f3f3f3f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_8751 : aut 2 (0xff00000000ffffff1313131313131313 : W) = (0xff00ff0000ffff0707070707070707 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_8946 : aut 2 (0xff000000ffff00001e1e1e1e1e1e1e1e : W) = (0xffffff000000003535353535353535 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_12066 : aut 2 (0xff00ffff00ff00003232323232323232 : W) = (0xff00ffffff00000d0d0d0d0d0d0d0d : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_12274 : aut 2 (0xff00ffffffff00003e3e3e3e3e3e3e3e : W) = (0xffffffffff00003d3d3d3d3d3d3d3d : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_17487 : aut 2 (0xff000000ffff4b4b4b4b4b4b4b4b : W) = (0xff00ffffa3a3a3a3a3a3a3a3 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_20292 : aut 2 (0xffff000000ff7878787878787878 : W) = (0xffffff00acacacacacacacac : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_32768 : aut 2 (0x8080808080808080 : W) = (0x4040404040404040 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_36744 : aut 2 (0xffffff00ff00b0b0b0b0b0b0b0b0 : W) = (0xff00ffff00ff4c4c4c4c4c4c4c4c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_36856 : aut 2 (0xffffffffff00bcbcbcbcbcbcbcbc : W) = (0xffffffff00ff7c7c7c7c7c7c7c7c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_43690 : aut 2 (0xff000000ffffff00b2b2b2b2b2b2b2b2 : W) = (0xffffff000000ff4d4d4d4d4d4d4d4d : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_62532 : aut 2 (0xffffff00000000ffc8c8c8c8c8c8c8c8 : W) = (0xffff0000ff00ff00e0e0e0e0e0e0e0e0 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_65280 : aut 2 (0xffffffff00000000f0f0f0f0f0f0f0f0 : W) = (0xffff0000ffff0000cccccccccccccccc : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_32 : aut 3 (0xff00000000000000000000 : W) = (0xff0000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_4593 : aut 3 (0xff00ffffff00000d0d0d0d0d0d0d0d : W) = (0xff00ffff00ff4c4c4c4c4c4c4c4c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_39321 : aut 3 (0xff00ffff00ff00a5a5a5a5a5a5a5a5 : W) = (0xffffffff00003c3c3c3c3c3c3c3c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_63624 : aut 3 (0xffff0000ff00ff00e0e0e0e0e0e0e0e0 : W) = (0xffffff00ff00b0b0b0b0b0b0b0b0 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_17 : aut 4 (0x505050505050505 : W) = (0x505050505050505 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_34 : aut 4 (0xff00000202020202020202 : W) = (0xff0808080808080808 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_64 : aut 4 (0x808080808080808 : W) = (0x202020202020202 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_128 : aut 4 (0xff0000000000000000000000 : W) = (0xff000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_136 : aut 4 (0xff00ff000000000000000000 : W) = (0xff00ff000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_241 : aut 4 (0xffff00000d0d0d0d0d0d0d0d : W) = (0xffff0707070707070707 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_248 : aut 4 (0xffffff000c0c0c0c0c0c0c0c : W) = (0xff00ffff0303030303030303 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_255 : aut 4 (0xffffffff0f0f0f0f0f0f0f0f : W) = (0xffffffff0f0f0f0f0f0f0f0f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_4505 : aut 4 (0xff00ffff00ff000505050505050505 : W) = (0xff00ffff00ff000505050505050505 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_4593 : aut 4 (0xff00ffffff00000d0d0d0d0d0d0d0d : W) = (0xff00ff0000ffff0707070707070707 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_4601 : aut 4 (0xff00ffffffff000d0d0d0d0d0d0d0d : W) = (0xff00ffff00ffff0707070707070707 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_4607 : aut 4 (0xff00ffffffffff0f0f0f0f0f0f0f0f : W) = (0xff00ffffffffff0f0f0f0f0f0f0f0f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_8751 : aut 4 (0xff00000000ffffff1313131313131313 : W) = (0xff00ffff00ff4c4c4c4c4c4c4c4c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_8874 : aut 4 (0xff000000ffffff001212121212121212 : W) = (0xff00ff00ffff4848484848484848 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_8959 : aut 4 (0xff000000ffffffff1f1f1f1f1f1f1f1f : W) = (0xff00ffffffff4f4f4f4f4f4f4f4f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_35064 : aut 4 (0xffffff00acacacacacacacac : W) = (0xff00ffffa3a3a3a3a3a3a3a3 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_35071 : aut 4 (0xffffffffafafafafafafafaf : W) = (0xffffffffafafafafafafafaf : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_61455 : aut 4 (0xffff00000000ffffc3c3c3c3c3c3c3c3 : W) = (0xffffffff00003c3c3c3c3c3c3c3c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_61576 : aut 4 (0xffff0000ff00ff00c0c0c0c0c0c0c0c0 : W) = (0xffffff00ff003030303030303030 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_61680 : aut 4 (0xffff0000ffff0000cccccccccccccccc : W) = (0xffff0000ffff3333333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_61695 : aut 4 (0xffff0000ffffffffcfcfcfcfcfcfcfcf : W) = (0xffffffffffff3f3f3f3f3f3f3f3f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_62532 : aut 4 (0xffffff00000000ffc8c8c8c8c8c8c8c8 : W) = (0xff00ffff00ff00003232323232323232 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_63624 : aut 4 (0xffff0000ff00ff00e0e0e0e0e0e0e0e0 : W) = (0xffffff00ff00b0b0b0b0b0b0b0b0 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct6_4383 : aut 6 (0xff00ff0000ffff0707070707070707 : W) = (0xff00ffff00ff4c4c4c4c4c4c4c4c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_4 : aut 9 (0xff0000000000000000 : W) = (0xff0000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_1024 : aut 9 (0xff00000000000000000000000000 : W) = (0xff000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_1028 : aut 9 (0xff00000000ff0000000000000000 : W) = (0xffff0000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_3844 : aut 9 (0xffff000000ff3030303030303030 : W) = (0xff00ffffa0a0a0a0a0a0a0a0 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_4373 : aut 9 (0xff00ff000000ff0505050505050505 : W) = (0xffff00ff0c0c0c0c0c0c0c0c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_4383 : aut 9 (0xff00ff0000ffff0707070707070707 : W) = (0xff00ffff00ff4c4c4c4c4c4c4c4c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_4593 : aut 9 (0xff00ffffff00000d0d0d0d0d0d0d0d : W) = (0xff00ffffff00000d0d0d0d0d0d0d0d : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_4597 : aut 9 (0xff00ffffff00ff0d0d0d0d0d0d0d0d : W) = (0xff00ffffff00ff0d0d0d0d0d0d0d0d : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_17487 : aut 9 (0xff000000ffff4b4b4b4b4b4b4b4b : W) = (0xff000000ffff4b4b4b4b4b4b4b4b : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_21845 : aut 9 (0xffffff000000ff4d4d4d4d4d4d4d4d : W) = (0xffffffff0f0f0f0f0f0f0f0f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_21855 : aut 9 (0xffffff0000ffff4f4f4f4f4f4f4f4f : W) = (0xff00ffffffff4f4f4f4f4f4f4f4f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_22005 : aut 9 (0xffffffffff00ff4d4d4d4d4d4d4d4d : W) = (0xff00ffffffffff0f0f0f0f0f0f0f0f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_36744 : aut 9 (0xffffff00ff00b0b0b0b0b0b0b0b0 : W) = (0xffffff00ff00b0b0b0b0b0b0b0b0 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_36748 : aut 9 (0xffffff00ffffb0b0b0b0b0b0b0b0 : W) = (0xffffff00ffffb0b0b0b0b0b0b0b0 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_61444 : aut 9 (0xffff0000000000ffc0c0c0c0c0c0c0c0 : W) = (0xff00000000ff00ff1212121212121212 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_62532 : aut 9 (0xffffff00000000ffc8c8c8c8c8c8c8c8 : W) = (0xff00000000ffffff1313131313131313 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_63624 : aut 9 (0xffff0000ff00ff00e0e0e0e0e0e0e0e0 : W) = (0xff00ffff00ff00003232323232323232 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_2176 : aut 12 (0xff0000002020202020202020 : W) = (0xff00001010101010101010 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_4080 : aut 12 (0xffffffff00003c3c3c3c3c3c3c3c : W) = (0xffffffff00003c3c3c3c3c3c3c3c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_4593 : aut 12 (0xff00ffffff00000d0d0d0d0d0d0d0d : W) = (0xff00ffff00ff4c4c4c4c4c4c4c4c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_8177 : aut 12 (0xffffffffff00003d3d3d3d3d3d3d3d : W) = (0xffffffff00ff7c7c7c7c7c7c7c7c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_61680 : aut 12 (0xffff0000ffff0000cccccccccccccccc : W) = (0xffffffff0f0f0f0f0f0f0f0f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_63624 : aut 12 (0xffff0000ff00ff00e0e0e0e0e0e0e0e0 : W) = (0xff00000000ffffff1313131313131313 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_65520 : aut 12 (0xffffffffffff0000fcfcfcfcfcfcfcfc : W) = (0xffffffffffff3f3f3f3f3f3f3f3f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct13_52428 : aut 13 (0xff00ff00ffffe8e8e8e8e8e8e8e8 : W) = (0xffffffff0f0f0f0f0f0f0f0f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_128 : aut 15 (0xff0000000000000000000000 : W) = (0xff0000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_132 : aut 15 (0xff0000ff0000000000000000 : W) = (0xff0000ff0000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_1024 : aut 15 (0xff00000000000000000000000000 : W) = (0xff00000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_1028 : aut 15 (0xff00000000ff0000000000000000 : W) = (0xffff00000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_1056 : aut 15 (0xff0000ff00000000000000000000 : W) = (0xff0000ff00000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_1264 : aut 15 (0xff00ffff00000c0c0c0c0c0c0c0c : W) = (0xff0000ff00ff4848484848484848 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_2048 : aut 15 (0x2020202020202020 : W) = (0x202020202020202 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_2050 : aut 15 (0x2222222222222222 : W) = (0x2222222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_2176 : aut 15 (0xff0000002020202020202020 : W) = (0xff0202020202020202 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_4096 : aut 15 (0xff0000000000000000000000000000 : W) = (0xff0000000000000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_8192 : aut 15 (0xff000000000000000000000000000000 : W) = (0xff000000000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_8224 : aut 15 (0xff00000000ff00000000000000000000 : W) = (0xffff000000000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_8751 : aut 15 (0xff00000000ffffff1313131313131313 : W) = (0xffffff00ff00b0b0b0b0b0b0b0b0 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_8870 : aut 15 (0xff000000ffff00ff1212121212121212 : W) = (0xffffff0000ff3030303030303030 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_8946 : aut 15 (0xff000000ffff00001e1e1e1e1e1e1e1e : W) = (0xffff000000ff7878787878787878 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_9762 : aut 15 (0xff00ff0000ff00001212121212121212 : W) = (0xffff00ff00003030303030303030 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_12066 : aut 15 (0xff00ffff00ff00003232323232323232 : W) = (0xff00ffff00ff00003232323232323232 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_12274 : aut 15 (0xff00ffffffff00003e3e3e3e3e3e3e3e : W) = (0xff00ffff00ff00ff7a7a7a7a7a7a7a7a : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_12834 : aut 15 (0xffff000000ff00001212121212121212 : W) = (0xffffff000000003030303030303030 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_16384 : aut 15 (0x4040404040404040 : W) = (0x404040404040404 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_16400 : aut 15 (0x4444444444444444 : W) = (0x4444444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_17487 : aut 15 (0xff000000ffff4b4b4b4b4b4b4b4b : W) = (0xffffff00acacacacacacacac : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_17652 : aut 15 (0xff00ffff00ff4c4c4c4c4c4c4c4c : W) = (0xff00ffff00ff4c4c4c4c4c4c4c4c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_21572 : aut 15 (0xffff00000000ff4848484848484848 : W) = (0xff0000ffff00000c0c0c0c0c0c0c0c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_21748 : aut 15 (0xffff00ffff00ff4c4c4c4c4c4c4c4c : W) = (0xffff00ffff00ff4c4c4c4c4c4c4c4c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_24576 : aut 15 (0xff000000000000004040404040404040 : W) = (0xff000000000404040404040404 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_26214 : aut 15 (0xff00ff0000ff00ff5a5a5a5a5a5a5a5a : W) = (0xffffffff00003c3c3c3c3c3c3c3c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_26358 : aut 15 (0xff00ff00ffff00ff5e5e5e5e5e5e5e5e : W) = (0xffffffff00ff7c7c7c7c7c7c7c7c : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_28662 : aut 15 (0xff00ffffffff00ff7e7e7e7e7e7e7e7e : W) = (0xff00ffffffff00ff7e7e7e7e7e7e7e7e : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_32768 : aut 15 (0x8080808080808080 : W) = (0x101010101010101 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_34956 : aut 15 (0xff00ffffa0a0a0a0a0a0a0a0 : W) = (0xff00ffff0303030303030303 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_34959 : aut 15 (0xff00ffffa3a3a3a3a3a3a3a3 : W) = (0xff00ffffa3a3a3a3a3a3a3a3 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_36008 : aut 15 (0xff00ffffff00a0a0a0a0a0a0a0a0 : W) = (0xff0000ffffff0303030303030303 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_39048 : aut 15 (0xff0000ff00ff00a0a0a0a0a0a0a0a0 : W) = (0xff00000000ffff0303030303030303 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_43690 : aut 15 (0xff000000ffffff00b2b2b2b2b2b2b2b2 : W) = (0xffff0000ffff3333333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_43695 : aut 15 (0xff000000ffffffffb3b3b3b3b3b3b3b3 : W) = (0xffffff00ffffb3b3b3b3b3b3b3b3 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_44970 : aut 15 (0xff00ffffffffff00b2b2b2b2b2b2b2b2 : W) = (0xff00ffff00ffffff3333333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_44975 : aut 15 (0xff00ffffffffffffb3b3b3b3b3b3b3b3 : W) = (0xff00ffffffffffffb3b3b3b3b3b3b3b3 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_52428 : aut 15 (0xff00ff00ffffe8e8e8e8e8e8e8e8 : W) = (0xffffffff0f0f0f0f0f0f0f0f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_52431 : aut 15 (0xff00ff00ffffebebebebebebebeb : W) = (0xffffffffafafafafafafafaf : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_52476 : aut 15 (0xff00ffffffffecececececececec : W) = (0xff00ffffffff4f4f4f4f4f4f4f4f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_52479 : aut 15 (0xff00ffffffffefefefefefefefef : W) = (0xff00ffffffffefefefefefefefef : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_61438 : aut 15 (0xff00fffffffffffffefefefefefefefe : W) = (0xff00ffffffffffff7f7f7f7f7f7f7f7f : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_61455 : aut 15 (0xffff00000000ffffc3c3c3c3c3c3c3c3 : W) = (0xff00ffff00ff00a5a5a5a5a5a5a5a5 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_61572 : aut 15 (0xffff0000ff0000ffc0c0c0c0c0c0c0c0 : W) = (0xff00ffff0000ff0505050505050505 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_61680 : aut 15 (0xffff0000ffff0000cccccccccccccccc : W) = (0xffffff000000ff4d4d4d4d4d4d4d4d : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_61713 : aut 15 (0xffff00ff00000000c5c5c5c5c5c5c5c5 : W) = (0xffff00ff00000000c5c5c5c5c5c5c5c5 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_61986 : aut 15 (0xffff000000ff0000d2d2d2d2d2d2d2d2 : W) = (0xffffff000000003535353535353535 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_62496 : aut 15 (0xffffff0000ff0000c0c0c0c0c0c0c0c0 : W) = (0xffffff00ff00000505050505050505 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_62532 : aut 15 (0xffffff00000000ffc8c8c8c8c8c8c8c8 : W) = (0xff00ffffff00000d0d0d0d0d0d0d0d : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_62708 : aut 15 (0xffffff00ffff00ffcccccccccccccccc : W) = (0xffffffffff00ff4d4d4d4d4d4d4d4d : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_62805 : aut 15 (0xffffffff000000ffcdcdcdcdcdcdcdcd : W) = (0xffff00ffffff0000cdcdcdcdcdcdcdcd : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_62965 : aut 15 (0xffffffffffff00ffcdcdcdcdcdcdcdcd : W) = (0xffffffffffff00ffcdcdcdcdcdcdcdcd : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_63624 : aut 15 (0xffff0000ff00ff00e0e0e0e0e0e0e0e0 : W) = (0xff00ff0000ffff0707070707070707 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_63631 : aut 15 (0xffff0000ff00ffffe3e3e3e3e3e3e3e3 : W) = (0xff00ffff00ffffa7a7a7a7a7a7a7a7 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_63897 : aut 15 (0xffff00ffff00ff00e5e5e5e5e5e5e5e5 : W) = (0xffff00ff0000ffffc7c7c7c7c7c7c7c7 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_65280 : aut 15 (0xffffffff00000000f0f0f0f0f0f0f0f0 : W) = (0xffff00ff00ff00001717171717171717 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_65297 : aut 15 (0xffffffff00000000f5f5f5f5f5f5f5f5 : W) = (0xffff00ff00ff0000d7d7d7d7d7d7d7d7 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_65314 : aut 15 (0xffffffff00ff0000f2f2f2f2f2f2f2f2 : W) = (0xffffffff00ff00003737373737373737 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_65526 : aut 15 (0xffffffffffff00fffefefefefefefefe : W) = (0xffffffffffff00ff7f7f7f7f7f7f7f7f : W) := by decide +kernel

set_option maxRecDepth 16000 in
def rejectWord0 : RejectedWord := makeRejected [] 0x202020202020202 2 (by rfl) (by rw [certAct2_2]; decide)
set_option maxRecDepth 16000 in
def rejectWord1 : RejectedWord := makeRejected [] 0xff000000000000000000 2 (by rfl) (by rw [certAct2_8]; decide)
set_option maxRecDepth 16000 in
def rejectWord2 : RejectedWord := makeRejected [] 0x404040404040404 1 (by rfl) (by rw [certAct1_16]; decide)
set_option maxRecDepth 16000 in
def rejectWord3 : RejectedWord := makeRejected [] 0xff00000000000000000000 3 (by rfl) (by rw [certAct3_32]; decide)
set_option maxRecDepth 16000 in
def rejectWord4 : RejectedWord := makeRejected [] 0x808080808080808 4 (by rfl) (by rw [certAct4_64]; decide)
set_option maxRecDepth 16000 in
def rejectWord5 : RejectedWord := makeRejected [] 0xff0000000000000000000000 4 (by rfl) (by rw [certAct4_128]; decide)
set_option maxRecDepth 16000 in
def rejectWord6 : RejectedWord := makeRejected [] 0xff000000000000000000000000 1 (by rfl) (by rw [certAct1_256]; decide)
set_option maxRecDepth 16000 in
def rejectWord7 : RejectedWord := makeRejected [] 0x1010101010101010 1 (by rfl) (by rw [certAct1_512]; decide)
set_option maxRecDepth 16000 in
def rejectWord8 : RejectedWord := makeRejected [] 0xff00000000000000000000000000 2 (by rfl) (by rw [certAct2_1024]; decide)
set_option maxRecDepth 16000 in
def rejectWord9 : RejectedWord := makeRejected [] 0x2020202020202020 2 (by rfl) (by rw [certAct2_2048]; decide)
set_option maxRecDepth 16000 in
def rejectWord10 : RejectedWord := makeRejected [] 0xffff0000ffff3333333333333333 2 (by rfl) (by rw [certAct2_3855]; decide)
set_option maxRecDepth 16000 in
def rejectWord11 : RejectedWord := makeRejected [] 0xff0000000000000000000000000000 1 (by rfl) (by rw [certAct1_4096]; decide)
set_option maxRecDepth 16000 in
def rejectWord12 : RejectedWord := makeRejected [] 0xff00ff0000ffff0707070707070707 6 (by rfl) (by rw [certAct6_4383]; decide)
set_option maxRecDepth 16000 in
def rejectWord13 : RejectedWord := makeRejected [] 0xff00ffffff00000d0d0d0d0d0d0d0d 3 (by rfl) (by rw [certAct3_4593]; decide)
set_option maxRecDepth 16000 in
def rejectWord14 : RejectedWord := makeRejected [] 0xffffff000000003535353535353535 1 (by rfl) (by rw [certAct1_7953]; decide)
set_option maxRecDepth 16000 in
def rejectWord15 : RejectedWord := makeRejected [] 0xff000000000000000000000000000000 1 (by rfl) (by rw [certAct1_8192]; decide)
set_option maxRecDepth 16000 in
def rejectWord16 : RejectedWord := makeRejected [] 0xff00000000ffffff1313131313131313 1 (by rfl) (by rw [certAct1_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord17 : RejectedWord := makeRejected [] 0xff000000ffff00001e1e1e1e1e1e1e1e 2 (by rfl) (by rw [certAct2_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord18 : RejectedWord := makeRejected [] 0xff00ffff00ff00003232323232323232 1 (by rfl) (by rw [certAct1_12066]; decide)
set_option maxRecDepth 16000 in
def rejectWord19 : RejectedWord := makeRejected [] 0xffff00ff00ff00001717171717171717 1 (by rfl) (by rw [certAct1_13107]; decide)
set_option maxRecDepth 16000 in
def rejectWord20 : RejectedWord := makeRejected [] 0x4040404040404040 1 (by rfl) (by rw [certAct1_16384]; decide)
set_option maxRecDepth 16000 in
def rejectWord21 : RejectedWord := makeRejected [] 0xff000000ffff4b4b4b4b4b4b4b4b 2 (by rfl) (by rw [certAct2_17487]; decide)
set_option maxRecDepth 16000 in
def rejectWord22 : RejectedWord := makeRejected [] 0xffff000000ff7878787878787878 2 (by rfl) (by rw [certAct2_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord23 : RejectedWord := makeRejected [] 0xffffff000000ff4d4d4d4d4d4d4d4d 1 (by rfl) (by rw [certAct1_21845]; decide)
set_option maxRecDepth 16000 in
def rejectWord24 : RejectedWord := makeRejected [] 0xff00ff0000ff00ff5a5a5a5a5a5a5a5a 1 (by rfl) (by rw [certAct1_26214]; decide)
set_option maxRecDepth 16000 in
def rejectWord25 : RejectedWord := makeRejected [] 0x8080808080808080 2 (by rfl) (by rw [certAct2_32768]; decide)
set_option maxRecDepth 16000 in
def rejectWord26 : RejectedWord := makeRejected [] 0xffffff00acacacacacacacac 4 (by rfl) (by rw [certAct4_35064]; decide)
set_option maxRecDepth 16000 in
def rejectWord27 : RejectedWord := makeRejected [] 0xffffff00ff00b0b0b0b0b0b0b0b0 2 (by rfl) (by rw [certAct2_36744]; decide)
set_option maxRecDepth 16000 in
def rejectWord28 : RejectedWord := makeRejected [] 0xff00ffff00ff00a5a5a5a5a5a5a5a5 3 (by rfl) (by rw [certAct3_39321]; decide)
set_option maxRecDepth 16000 in
def rejectWord29 : RejectedWord := makeRejected [] 0xff000000ffffff00b2b2b2b2b2b2b2b2 2 (by rfl) (by rw [certAct2_43690]; decide)
set_option maxRecDepth 16000 in
def rejectWord30 : RejectedWord := makeRejected [] 0xff00ff00ffffe8e8e8e8e8e8e8e8 13 (by rfl) (by rw [certAct13_52428]; decide)
set_option maxRecDepth 16000 in
def rejectWord31 : RejectedWord := makeRejected [] 0xffff00000000ffffc3c3c3c3c3c3c3c3 1 (by rfl) (by rw [certAct1_61455]; decide)
set_option maxRecDepth 16000 in
def rejectWord32 : RejectedWord := makeRejected [] 0xffff0000ffff0000cccccccccccccccc 1 (by rfl) (by rw [certAct1_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord33 : RejectedWord := makeRejected [] 0xffff00ff00000000c5c5c5c5c5c5c5c5 1 (by rfl) (by rw [certAct1_61713]; decide)
set_option maxRecDepth 16000 in
def rejectWord34 : RejectedWord := makeRejected [] 0xffff000000ff0000d2d2d2d2d2d2d2d2 1 (by rfl) (by rw [certAct1_61986]; decide)
set_option maxRecDepth 16000 in
def rejectWord35 : RejectedWord := makeRejected [] 0xffffff00000000ffc8c8c8c8c8c8c8c8 1 (by rfl) (by rw [certAct1_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord36 : RejectedWord := makeRejected [] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 3 (by rfl) (by rw [certAct3_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord37 : RejectedWord := makeRejected [] 0xffffffff00000000f0f0f0f0f0f0f0f0 1 (by rfl) (by rw [certAct1_65280]; decide)
set_option maxRecDepth 16000 in
def rejectWord38 : RejectedWord := makeRejected [0x101010101010101] 0xffff000000003131313131313131 1 (by simp only [List.all_cons, List.all_nil, certAct1_1] <;> decide) (by rw [certAct1_3841]; decide)
set_option maxRecDepth 16000 in
def rejectWord39 : RejectedWord := makeRejected [0x101010101010101] 0xff00000000ff00001313131313131313 1 (by simp only [List.all_cons, List.all_nil, certAct1_1] <;> decide) (by rw [certAct1_8739]; decide)
set_option maxRecDepth 16000 in
def rejectWord40 : RejectedWord := makeRejected [0x101010101010101] 0xff00000000ffffff1313131313131313 1 (by simp only [List.all_cons, List.all_nil, certAct1_1] <;> decide) (by rw [certAct1_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord41 : RejectedWord := makeRejected [0x101010101010101] 0xff00ffff00ff00003232323232323232 1 (by simp only [List.all_cons, List.all_nil, certAct1_1] <;> decide) (by rw [certAct1_12066]; decide)
set_option maxRecDepth 16000 in
def rejectWord42 : RejectedWord := makeRejected [0x101010101010101] 0xffff000000000000c1c1c1c1c1c1c1c1 1 (by simp only [List.all_cons, List.all_nil, certAct1_1] <;> decide) (by rw [certAct1_61441]; decide)
set_option maxRecDepth 16000 in
def rejectWord43 : RejectedWord := makeRejected [0x101010101010101] 0xffffff00000000ffc8c8c8c8c8c8c8c8 1 (by simp only [List.all_cons, List.all_nil, certAct1_1] <;> decide) (by rw [certAct1_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord44 : RejectedWord := makeRejected [0xff0000000000000000] 0xff00000000000000000000000000 9 (by simp only [List.all_cons, List.all_nil, certAct9_4] <;> decide) (by rw [certAct9_1024]; decide)
set_option maxRecDepth 16000 in
def rejectWord45 : RejectedWord := makeRejected [0xff0000000000000000] 0xffff000000ff3030303030303030 9 (by simp only [List.all_cons, List.all_nil, certAct9_4] <;> decide) (by rw [certAct9_3844]; decide)
set_option maxRecDepth 16000 in
def rejectWord46 : RejectedWord := makeRejected [0xff0000000000000000] 0xff00ff000000ff0505050505050505 9 (by simp only [List.all_cons, List.all_nil, certAct9_4] <;> decide) (by rw [certAct9_4373]; decide)
set_option maxRecDepth 16000 in
def rejectWord47 : RejectedWord := makeRejected [0xff0000000000000000] 0xff00ff0000ffff0707070707070707 9 (by simp only [List.all_cons, List.all_nil, certAct9_4] <;> decide) (by rw [certAct9_4383]; decide)
set_option maxRecDepth 16000 in
def rejectWord48 : RejectedWord := makeRejected [0xff0000000000000000] 0xffffff000000ff4d4d4d4d4d4d4d4d 9 (by simp only [List.all_cons, List.all_nil, certAct9_4] <;> decide) (by rw [certAct9_21845]; decide)
set_option maxRecDepth 16000 in
def rejectWord49 : RejectedWord := makeRejected [0xff0000000000000000] 0xffff0000000000ffc0c0c0c0c0c0c0c0 9 (by simp only [List.all_cons, List.all_nil, certAct9_4] <;> decide) (by rw [certAct9_61444]; decide)
set_option maxRecDepth 16000 in
def rejectWord50 : RejectedWord := makeRejected [0xff0000000000000000] 0xffffff00000000ffc8c8c8c8c8c8c8c8 9 (by simp only [List.all_cons, List.all_nil, certAct9_4] <;> decide) (by rw [certAct9_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord51 : RejectedWord := makeRejected [0xff0000000000000000] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 9 (by simp only [List.all_cons, List.all_nil, certAct9_4] <;> decide) (by rw [certAct9_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord52 : RejectedWord := makeRejected [0x505050505050505, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff00000d0d0d0d0d0d0d0d 4 (by simp only [List.all_cons, List.all_nil, certAct4_17, certAct4_255] <;> decide) (by rw [certAct4_241]; decide)
set_option maxRecDepth 16000 in
def rejectWord53 : RejectedWord := makeRejected [0x505050505050505, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00ffffff00000d0d0d0d0d0d0d0d 4 (by simp only [List.all_cons, List.all_nil, certAct4_17, certAct4_255] <;> decide) (by rw [certAct4_4593]; decide)
set_option maxRecDepth 16000 in
def rejectWord54 : RejectedWord := makeRejected [0x505050505050505, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00000000ffffff1313131313131313 4 (by simp only [List.all_cons, List.all_nil, certAct4_17, certAct4_255] <;> decide) (by rw [certAct4_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord55 : RejectedWord := makeRejected [0x505050505050505, 0xffffffff0f0f0f0f0f0f0f0f] 0xffffff00000000ffc8c8c8c8c8c8c8c8 4 (by simp only [List.all_cons, List.all_nil, certAct4_17, certAct4_255] <;> decide) (by rw [certAct4_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord56 : RejectedWord := makeRejected [0x505050505050505, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 4 (by simp only [List.all_cons, List.all_nil, certAct4_17, certAct4_255] <;> decide) (by rw [certAct4_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord57 : RejectedWord := makeRejected [0xff0000ff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xff00000000ffffff1313131313131313 15 (by simp only [List.all_cons, List.all_nil, certAct15_132, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord58 : RejectedWord := makeRejected [0xff0000ff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xff000000ffff00ff1212121212121212 15 (by simp only [List.all_cons, List.all_nil, certAct15_132, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_8870]; decide)
set_option maxRecDepth 16000 in
def rejectWord59 : RejectedWord := makeRejected [0xff0000ff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xff00ffffa0a0a0a0a0a0a0a0 15 (by simp only [List.all_cons, List.all_nil, certAct15_132, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_34956]; decide)
set_option maxRecDepth 16000 in
def rejectWord60 : RejectedWord := makeRejected [0xff0000ff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffff0000ff0000ffc0c0c0c0c0c0c0c0 15 (by simp only [List.all_cons, List.all_nil, certAct15_132, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_61572]; decide)
set_option maxRecDepth 16000 in
def rejectWord61 : RejectedWord := makeRejected [0xff0000ff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 15 (by simp only [List.all_cons, List.all_nil, certAct15_132, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord62 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xffffff000c0c0c0c0c0c0c0c 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_248]; decide)
set_option maxRecDepth 16000 in
def rejectWord63 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00ffffff00000d0d0d0d0d0d0d0d 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_4593]; decide)
set_option maxRecDepth 16000 in
def rejectWord64 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00000000ffffff1313131313131313 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord65 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xff000000ffffff001212121212121212 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_8874]; decide)
set_option maxRecDepth 16000 in
def rejectWord66 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xffffff00acacacacacacacac 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_35064]; decide)
set_option maxRecDepth 16000 in
def rejectWord67 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ff00ff00c0c0c0c0c0c0c0c0 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_61576]; decide)
set_option maxRecDepth 16000 in
def rejectWord68 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ffff0000cccccccccccccccc 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord69 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xffffff00000000ffc8c8c8c8c8c8c8c8 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord70 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord71 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00ffffff00000d0d0d0d0d0d0d0d 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_4607, certAct4_255] <;> decide) (by rw [certAct4_4593]; decide)
set_option maxRecDepth 16000 in
def rejectWord72 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00000000ffffff1313131313131313 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_4607, certAct4_255] <;> decide) (by rw [certAct4_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord73 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ff00ff00c0c0c0c0c0c0c0c0 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_4607, certAct4_255] <;> decide) (by rw [certAct4_61576]; decide)
set_option maxRecDepth 16000 in
def rejectWord74 : RejectedWord := makeRejected [0xff00ff000000000000000000, 0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 0xffffff00000000ffc8c8c8c8c8c8c8c8 4 (by simp only [List.all_cons, List.all_nil, certAct4_136, certAct4_4607, certAct4_255] <;> decide) (by rw [certAct4_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord75 : RejectedWord := makeRejected [0xffffffff0f0f0f0f0f0f0f0f] 0xff00000202020202020202 4 (by simp only [List.all_cons, List.all_nil, certAct4_255] <;> decide) (by rw [certAct4_34]; decide)
set_option maxRecDepth 16000 in
def rejectWord76 : RejectedWord := makeRejected [0xffffffff0f0f0f0f0f0f0f0f] 0xff00ffffff00000d0d0d0d0d0d0d0d 4 (by simp only [List.all_cons, List.all_nil, certAct4_255] <;> decide) (by rw [certAct4_4593]; decide)
set_option maxRecDepth 16000 in
def rejectWord77 : RejectedWord := makeRejected [0xffffffff0f0f0f0f0f0f0f0f] 0xff00000000ffffff1313131313131313 4 (by simp only [List.all_cons, List.all_nil, certAct4_255] <;> decide) (by rw [certAct4_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord78 : RejectedWord := makeRejected [0xffffffff0f0f0f0f0f0f0f0f] 0xff000000ffffffff1f1f1f1f1f1f1f1f 4 (by simp only [List.all_cons, List.all_nil, certAct4_255] <;> decide) (by rw [certAct4_8959]; decide)
set_option maxRecDepth 16000 in
def rejectWord79 : RejectedWord := makeRejected [0xffffffff0f0f0f0f0f0f0f0f] 0xffff00000000ffffc3c3c3c3c3c3c3c3 4 (by simp only [List.all_cons, List.all_nil, certAct4_255] <;> decide) (by rw [certAct4_61455]; decide)
set_option maxRecDepth 16000 in
def rejectWord80 : RejectedWord := makeRejected [0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ffff0000cccccccccccccccc 4 (by simp only [List.all_cons, List.all_nil, certAct4_255] <;> decide) (by rw [certAct4_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord81 : RejectedWord := makeRejected [0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ffffffffcfcfcfcfcfcfcfcf 4 (by simp only [List.all_cons, List.all_nil, certAct4_255] <;> decide) (by rw [certAct4_61695]; decide)
set_option maxRecDepth 16000 in
def rejectWord82 : RejectedWord := makeRejected [0xffffffff0f0f0f0f0f0f0f0f] 0xffffff00000000ffc8c8c8c8c8c8c8c8 4 (by simp only [List.all_cons, List.all_nil, certAct4_255] <;> decide) (by rw [certAct4_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord83 : RejectedWord := makeRejected [0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 4 (by simp only [List.all_cons, List.all_nil, certAct4_255] <;> decide) (by rw [certAct4_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord84 : RejectedWord := makeRejected [0xff0000ff00000000000000000000, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00000000000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_1056, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_1024]; decide)
set_option maxRecDepth 16000 in
def rejectWord85 : RejectedWord := makeRejected [0xff0000ff00000000000000000000, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00ffff00000c0c0c0c0c0c0c0c 15 (by simp only [List.all_cons, List.all_nil, certAct15_1056, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_1264]; decide)
set_option maxRecDepth 16000 in
def rejectWord86 : RejectedWord := makeRejected [0xff0000ff00000000000000000000, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00000000ffffff1313131313131313 15 (by simp only [List.all_cons, List.all_nil, certAct15_1056, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord87 : RejectedWord := makeRejected [0xff0000ff00000000000000000000, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00ff0000ff00001212121212121212 15 (by simp only [List.all_cons, List.all_nil, certAct15_1056, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_9762]; decide)
set_option maxRecDepth 16000 in
def rejectWord88 : RejectedWord := makeRejected [0xff0000ff00000000000000000000, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00ffffff00a0a0a0a0a0a0a0a0 15 (by simp only [List.all_cons, List.all_nil, certAct15_1056, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_36008]; decide)
set_option maxRecDepth 16000 in
def rejectWord89 : RejectedWord := makeRejected [0xff0000ff00000000000000000000, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff0000ff0000c0c0c0c0c0c0c0c0 15 (by simp only [List.all_cons, List.all_nil, certAct15_1056, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_62496]; decide)
set_option maxRecDepth 16000 in
def rejectWord90 : RejectedWord := makeRejected [0xff0000ff00000000000000000000, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_1056, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord91 : RejectedWord := makeRejected [0x2222222222222222, 0xff00ffff00ff00003232323232323232, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_2050, certAct15_12066, certAct15_34959] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord92 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xff000000000404040404040404 2 (by simp only [List.all_cons, List.all_nil, certAct2_4080] <;> decide) (by rw [certAct2_272]; decide)
set_option maxRecDepth 16000 in
def rejectWord93 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xff00000000000808080808080808 2 (by simp only [List.all_cons, List.all_nil, certAct2_4080] <;> decide) (by rw [certAct2_1088]; decide)
set_option maxRecDepth 16000 in
def rejectWord94 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xff0000002020202020202020 12 (by simp only [List.all_cons, List.all_nil, certAct12_4080] <;> decide) (by rw [certAct12_2176]; decide)
set_option maxRecDepth 16000 in
def rejectWord95 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xff00ffffff00000d0d0d0d0d0d0d0d 12 (by simp only [List.all_cons, List.all_nil, certAct12_4080] <;> decide) (by rw [certAct12_4593]; decide)
set_option maxRecDepth 16000 in
def rejectWord96 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xffffffffff00003d3d3d3d3d3d3d3d 12 (by simp only [List.all_cons, List.all_nil, certAct12_4080] <;> decide) (by rw [certAct12_8177]; decide)
set_option maxRecDepth 16000 in
def rejectWord97 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xff00000000ffffff1313131313131313 2 (by simp only [List.all_cons, List.all_nil, certAct2_4080] <;> decide) (by rw [certAct2_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord98 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xff00ffff00ff00003232323232323232 2 (by simp only [List.all_cons, List.all_nil, certAct2_4080] <;> decide) (by rw [certAct2_12066]; decide)
set_option maxRecDepth 16000 in
def rejectWord99 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xff00ffffffff00003e3e3e3e3e3e3e3e 2 (by simp only [List.all_cons, List.all_nil, certAct2_4080] <;> decide) (by rw [certAct2_12274]; decide)
set_option maxRecDepth 16000 in
def rejectWord100 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xffffffffff00bcbcbcbcbcbcbcbc 2 (by simp only [List.all_cons, List.all_nil, certAct2_4080] <;> decide) (by rw [certAct2_36856]; decide)
set_option maxRecDepth 16000 in
def rejectWord101 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xffff0000ffff0000cccccccccccccccc 12 (by simp only [List.all_cons, List.all_nil, certAct12_4080] <;> decide) (by rw [certAct12_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord102 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xffffff00000000ffc8c8c8c8c8c8c8c8 2 (by simp only [List.all_cons, List.all_nil, certAct2_4080] <;> decide) (by rw [certAct2_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord103 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 12 (by simp only [List.all_cons, List.all_nil, certAct12_4080] <;> decide) (by rw [certAct12_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord104 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xffffffff00000000f0f0f0f0f0f0f0f0 2 (by simp only [List.all_cons, List.all_nil, certAct2_4080] <;> decide) (by rw [certAct2_65280]; decide)
set_option maxRecDepth 16000 in
def rejectWord105 : RejectedWord := makeRejected [0xffffffff00003c3c3c3c3c3c3c3c] 0xffffffffffff0000fcfcfcfcfcfcfcfc 12 (by simp only [List.all_cons, List.all_nil, certAct12_4080] <;> decide) (by rw [certAct12_65520]; decide)
set_option maxRecDepth 16000 in
def rejectWord106 : RejectedWord := makeRejected [0xffffffffffff3f3f3f3f3f3f3f3f, 0xffffffff00003c3c3c3c3c3c3c3c] 0xff00000000ff0808080808080808 2 (by simp only [List.all_cons, List.all_nil, certAct2_4095, certAct2_4080] <;> decide) (by rw [certAct2_1092]; decide)
set_option maxRecDepth 16000 in
def rejectWord107 : RejectedWord := makeRejected [0xffffffffffff3f3f3f3f3f3f3f3f, 0xffffffff00003c3c3c3c3c3c3c3c] 0xff00000000ffffff1313131313131313 2 (by simp only [List.all_cons, List.all_nil, certAct2_4095, certAct2_4080] <;> decide) (by rw [certAct2_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord108 : RejectedWord := makeRejected [0xffffffffffff3f3f3f3f3f3f3f3f, 0xffffffff00003c3c3c3c3c3c3c3c] 0xff00ffff00ff00003232323232323232 2 (by simp only [List.all_cons, List.all_nil, certAct2_4095, certAct2_4080] <;> decide) (by rw [certAct2_12066]; decide)
set_option maxRecDepth 16000 in
def rejectWord109 : RejectedWord := makeRejected [0xffffffffffff3f3f3f3f3f3f3f3f, 0xffffffff00003c3c3c3c3c3c3c3c] 0xffffff00000000ffc8c8c8c8c8c8c8c8 2 (by simp only [List.all_cons, List.all_nil, certAct2_4095, certAct2_4080] <;> decide) (by rw [certAct2_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord110 : RejectedWord := makeRejected [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff000000000000000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_8192]; decide)
set_option maxRecDepth 16000 in
def rejectWord111 : RejectedWord := makeRejected [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00000000ffffff1313131313131313 15 (by simp only [List.all_cons, List.all_nil, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord112 : RejectedWord := makeRejected [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff000000ff00001212121212121212 15 (by simp only [List.all_cons, List.all_nil, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_12834]; decide)
set_option maxRecDepth 16000 in
def rejectWord113 : RejectedWord := makeRejected [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff00000000ff4848484848484848 15 (by simp only [List.all_cons, List.all_nil, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_21572]; decide)
set_option maxRecDepth 16000 in
def rejectWord114 : RejectedWord := makeRejected [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff0000ff00ff00a0a0a0a0a0a0a0a0 15 (by simp only [List.all_cons, List.all_nil, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_39048]; decide)
set_option maxRecDepth 16000 in
def rejectWord115 : RejectedWord := makeRejected [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff0000ffff0000cccccccccccccccc 15 (by simp only [List.all_cons, List.all_nil, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord116 : RejectedWord := makeRejected [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord117 : RejectedWord := makeRejected [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00ffff00ffcccccccccccccccc 15 (by simp only [List.all_cons, List.all_nil, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_62708]; decide)
set_option maxRecDepth 16000 in
def rejectWord118 : RejectedWord := makeRejected [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 15 (by simp only [List.all_cons, List.all_nil, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord119 : RejectedWord := makeRejected [0xff00ff0000ffff0707070707070707, 0x101010101010101] 0xff00000000ff00001313131313131313 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383, certAct1_1] <;> decide) (by rw [certAct1_8739]; decide)
set_option maxRecDepth 16000 in
def rejectWord120 : RejectedWord := makeRejected [0xff00ff0000ffff0707070707070707, 0x101010101010101] 0xff00000000ffffff1313131313131313 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383, certAct1_1] <;> decide) (by rw [certAct1_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord121 : RejectedWord := makeRejected [0xff00ff0000ffff0707070707070707, 0x101010101010101] 0xff00ffff00ff00003232323232323232 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383, certAct1_1] <;> decide) (by rw [certAct1_12066]; decide)
set_option maxRecDepth 16000 in
def rejectWord122 : RejectedWord := makeRejected [0xff00ff0000ffff0707070707070707, 0x101010101010101] 0xffff000000000000c1c1c1c1c1c1c1c1 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383, certAct1_1] <;> decide) (by rw [certAct1_61441]; decide)
set_option maxRecDepth 16000 in
def rejectWord123 : RejectedWord := makeRejected [0xff00ff0000ffff0707070707070707, 0x101010101010101] 0xffffff00000000ffc8c8c8c8c8c8c8c8 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383, certAct1_1] <;> decide) (by rw [certAct1_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord124 : RejectedWord := makeRejected [0xff00ffff00ff000505050505050505, 0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00ffffffff000d0d0d0d0d0d0d0d 4 (by simp only [List.all_cons, List.all_nil, certAct4_4505, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_4601]; decide)
set_option maxRecDepth 16000 in
def rejectWord125 : RejectedWord := makeRejected [0xff00ffff00ff000505050505050505, 0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00000000ffffff1313131313131313 4 (by simp only [List.all_cons, List.all_nil, certAct4_4505, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord126 : RejectedWord := makeRejected [0xff00ffff00ff000505050505050505, 0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xff000000ffffff001212121212121212 4 (by simp only [List.all_cons, List.all_nil, certAct4_4505, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_8874]; decide)
set_option maxRecDepth 16000 in
def rejectWord127 : RejectedWord := makeRejected [0xff00ffff00ff000505050505050505, 0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ff00ff00c0c0c0c0c0c0c0c0 4 (by simp only [List.all_cons, List.all_nil, certAct4_4505, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_61576]; decide)
set_option maxRecDepth 16000 in
def rejectWord128 : RejectedWord := makeRejected [0xff00ffff00ff000505050505050505, 0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xffffff00000000ffc8c8c8c8c8c8c8c8 4 (by simp only [List.all_cons, List.all_nil, certAct4_4505, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord129 : RejectedWord := makeRejected [0xff00ffff00ff000505050505050505, 0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 4 (by simp only [List.all_cons, List.all_nil, certAct4_4505, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord130 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000] 0xffffff000000ff4d4d4d4d4d4d4d4d 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_4] <;> decide) (by rw [certAct9_21845]; decide)
set_option maxRecDepth 16000 in
def rejectWord131 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000] 0xffffffffff00ff4d4d4d4d4d4d4d4d 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_4] <;> decide) (by rw [certAct9_22005]; decide)
set_option maxRecDepth 16000 in
def rejectWord132 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000] 0xffff0000000000ffc0c0c0c0c0c0c0c0 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_4] <;> decide) (by rw [certAct9_61444]; decide)
set_option maxRecDepth 16000 in
def rejectWord133 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000] 0xffffff00000000ffc8c8c8c8c8c8c8c8 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_4] <;> decide) (by rw [certAct9_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord134 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_4] <;> decide) (by rw [certAct9_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord135 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffffff0000ffff4f4f4f4f4f4f4f4f 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_21855]; decide)
set_option maxRecDepth 16000 in
def rejectWord136 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffff0000000000ffc0c0c0c0c0c0c0c0 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_61444]; decide)
set_option maxRecDepth 16000 in
def rejectWord137 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord138 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffffff000000ff4d4d4d4d4d4d4d4d 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_21845]; decide)
set_option maxRecDepth 16000 in
def rejectWord139 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffffffffff00ff4d4d4d4d4d4d4d4d 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_22005]; decide)
set_option maxRecDepth 16000 in
def rejectWord140 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffff0000000000ffc0c0c0c0c0c0c0c0 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_61444]; decide)
set_option maxRecDepth 16000 in
def rejectWord141 : RejectedWord := makeRejected [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 9 (by simp only [List.all_cons, List.all_nil, certAct9_4593, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord142 : RejectedWord := makeRejected [0xff00ffffff00ff0d0d0d0d0d0d0d0d, 0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000] 0xffff0000000000ffc0c0c0c0c0c0c0c0 9 (by simp only [List.all_cons, List.all_nil, certAct9_4597, certAct9_4593, certAct9_4] <;> decide) (by rw [certAct9_61444]; decide)
set_option maxRecDepth 16000 in
def rejectWord143 : RejectedWord := makeRejected [0xff00ffffff00ff0d0d0d0d0d0d0d0d, 0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000] 0xffffff00000000ffc8c8c8c8c8c8c8c8 9 (by simp only [List.all_cons, List.all_nil, certAct9_4597, certAct9_4593, certAct9_4] <;> decide) (by rw [certAct9_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord144 : RejectedWord := makeRejected [0xff00ffffff00ff0d0d0d0d0d0d0d0d, 0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 9 (by simp only [List.all_cons, List.all_nil, certAct9_4597, certAct9_4593, certAct9_4] <;> decide) (by rw [certAct9_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord145 : RejectedWord := makeRejected [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00000000ffffff1313131313131313 4 (by simp only [List.all_cons, List.all_nil, certAct4_4607, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord146 : RejectedWord := makeRejected [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ff00ff00c0c0c0c0c0c0c0c0 4 (by simp only [List.all_cons, List.all_nil, certAct4_4607, certAct4_136, certAct4_255] <;> decide) (by rw [certAct4_61576]; decide)
set_option maxRecDepth 16000 in
def rejectWord147 : RejectedWord := makeRejected [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00000000ffffff1313131313131313 4 (by simp only [List.all_cons, List.all_nil, certAct4_4607, certAct4_255] <;> decide) (by rw [certAct4_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord148 : RejectedWord := makeRejected [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff00000000ffffc3c3c3c3c3c3c3c3 4 (by simp only [List.all_cons, List.all_nil, certAct4_4607, certAct4_255] <;> decide) (by rw [certAct4_61455]; decide)
set_option maxRecDepth 16000 in
def rejectWord149 : RejectedWord := makeRejected [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ffff0000cccccccccccccccc 4 (by simp only [List.all_cons, List.all_nil, certAct4_4607, certAct4_255] <;> decide) (by rw [certAct4_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord150 : RejectedWord := makeRejected [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 0xffffff00000000ffc8c8c8c8c8c8c8c8 4 (by simp only [List.all_cons, List.all_nil, certAct4_4607, certAct4_255] <;> decide) (by rw [certAct4_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord151 : RejectedWord := makeRejected [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 4 (by simp only [List.all_cons, List.all_nil, certAct4_4607, certAct4_255] <;> decide) (by rw [certAct4_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord152 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff000000000000000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_8192]; decide)
set_option maxRecDepth 16000 in
def rejectWord153 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff000000ff00001212121212121212 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_12834]; decide)
set_option maxRecDepth 16000 in
def rejectWord154 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff0000ffff0000cccccccccccccccc 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord155 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord156 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00ffff00ffcccccccccccccccc 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_62708]; decide)
set_option maxRecDepth 16000 in
def rejectWord157 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00000000000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_1024]; decide)
set_option maxRecDepth 16000 in
def rejectWord158 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0x2020202020202020 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_2048]; decide)
set_option maxRecDepth 16000 in
def rejectWord159 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff000000000000000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_8192]; decide)
set_option maxRecDepth 16000 in
def rejectWord160 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00ffffffff00003e3e3e3e3e3e3e3e 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_12274]; decide)
set_option maxRecDepth 16000 in
def rejectWord161 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00ffffffffff00b2b2b2b2b2b2b2b2 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_44970]; decide)
set_option maxRecDepth 16000 in
def rejectWord162 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff00000000ffffc3c3c3c3c3c3c3c3 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_61455]; decide)
set_option maxRecDepth 16000 in
def rejectWord163 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff0000ffff0000cccccccccccccccc 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord164 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff000000ff0000d2d2d2d2d2d2d2d2 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_61986]; decide)
set_option maxRecDepth 16000 in
def rejectWord165 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord166 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00ffff00ffcccccccccccccccc 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_62708]; decide)
set_option maxRecDepth 16000 in
def rejectWord167 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord168 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffff00000000f0f0f0f0f0f0f0f0 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_65280]; decide)
set_option maxRecDepth 16000 in
def rejectWord169 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffff00ff0000f2f2f2f2f2f2f2f2 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_65314]; decide)
set_option maxRecDepth 16000 in
def rejectWord170 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord171 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord172 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffff0000ff00ffffe3e3e3e3e3e3e3e3 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_63631]; decide)
set_option maxRecDepth 16000 in
def rejectWord173 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_34959] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord174 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_34959] <;> decide) (by rw [certAct15_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord175 : RejectedWord := makeRejected [0xff00ffff00ff00003232323232323232, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffff0000ff00ffffe3e3e3e3e3e3e3e3 15 (by simp only [List.all_cons, List.all_nil, certAct15_12066, certAct15_34959] <;> decide) (by rw [certAct15_63631]; decide)
set_option maxRecDepth 16000 in
def rejectWord176 : RejectedWord := makeRejected [0x4444444444444444, 0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00000000ffffff1313131313131313 15 (by simp only [List.all_cons, List.all_nil, certAct15_16400, certAct15_61713, certAct15_17652] <;> decide) (by rw [certAct15_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord177 : RejectedWord := makeRejected [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffff000000ff3030303030303030 9 (by simp only [List.all_cons, List.all_nil, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_3844]; decide)
set_option maxRecDepth 16000 in
def rejectWord178 : RejectedWord := makeRejected [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xff00ff000000ff0505050505050505 9 (by simp only [List.all_cons, List.all_nil, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_4373]; decide)
set_option maxRecDepth 16000 in
def rejectWord179 : RejectedWord := makeRejected [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xff00ff0000ffff0707070707070707 9 (by simp only [List.all_cons, List.all_nil, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_4383]; decide)
set_option maxRecDepth 16000 in
def rejectWord180 : RejectedWord := makeRejected [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffffff0000ffff4f4f4f4f4f4f4f4f 9 (by simp only [List.all_cons, List.all_nil, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_21855]; decide)
set_option maxRecDepth 16000 in
def rejectWord181 : RejectedWord := makeRejected [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffff0000000000ffc0c0c0c0c0c0c0c0 9 (by simp only [List.all_cons, List.all_nil, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_61444]; decide)
set_option maxRecDepth 16000 in
def rejectWord182 : RejectedWord := makeRejected [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffffff00000000ffc8c8c8c8c8c8c8c8 9 (by simp only [List.all_cons, List.all_nil, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord183 : RejectedWord := makeRejected [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 9 (by simp only [List.all_cons, List.all_nil, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord184 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff0000000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_128]; decide)
set_option maxRecDepth 16000 in
def rejectWord185 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00000000000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_1024]; decide)
set_option maxRecDepth 16000 in
def rejectWord186 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff000000000000000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_8192]; decide)
set_option maxRecDepth 16000 in
def rejectWord187 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00000000ffffff1313131313131313 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord188 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff000000ffff00001e1e1e1e1e1e1e1e 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord189 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0x4040404040404040 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_16384]; decide)
set_option maxRecDepth 16000 in
def rejectWord190 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00ff0000ff00ff5a5a5a5a5a5a5a5a 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_26214]; decide)
set_option maxRecDepth 16000 in
def rejectWord191 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00ff00ffff00ff5e5e5e5e5e5e5e5e 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_26358]; decide)
set_option maxRecDepth 16000 in
def rejectWord192 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff000000ffffff00b2b2b2b2b2b2b2b2 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_43690]; decide)
set_option maxRecDepth 16000 in
def rejectWord193 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00ffffffffecececececececec 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_52476]; decide)
set_option maxRecDepth 16000 in
def rejectWord194 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff00000000ffffc3c3c3c3c3c3c3c3 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_61455]; decide)
set_option maxRecDepth 16000 in
def rejectWord195 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff0000ffff0000cccccccccccccccc 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord196 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff000000ff0000d2d2d2d2d2d2d2d2 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_61986]; decide)
set_option maxRecDepth 16000 in
def rejectWord197 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord198 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00ffff00ffcccccccccccccccc 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_62708]; decide)
set_option maxRecDepth 16000 in
def rejectWord199 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord200 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffff00000000f0f0f0f0f0f0f0f0 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652] <;> decide) (by rw [certAct15_65280]; decide)
set_option maxRecDepth 16000 in
def rejectWord201 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xff00000000ffffff1313131313131313 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord202 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xff000000ffffffffb3b3b3b3b3b3b3b3 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_43695]; decide)
set_option maxRecDepth 16000 in
def rejectWord203 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xff00ffffffffecececececececec 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_52476]; decide)
set_option maxRecDepth 16000 in
def rejectWord204 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord205 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord206 : RejectedWord := makeRejected [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffff0000ff00ffffe3e3e3e3e3e3e3e3 15 (by simp only [List.all_cons, List.all_nil, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_63631]; decide)
set_option maxRecDepth 16000 in
def rejectWord207 : RejectedWord := makeRejected [0xffff00ffff00ff4c4c4c4c4c4c4c4c, 0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00000000ffffff1313131313131313 15 (by simp only [List.all_cons, List.all_nil, certAct15_21748, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord208 : RejectedWord := makeRejected [0xffff00ffff00ff4c4c4c4c4c4c4c4c, 0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff000000ff00001212121212121212 15 (by simp only [List.all_cons, List.all_nil, certAct15_21748, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_12834]; decide)
set_option maxRecDepth 16000 in
def rejectWord209 : RejectedWord := makeRejected [0xffff00ffff00ff4c4c4c4c4c4c4c4c, 0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_21748, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord210 : RejectedWord := makeRejected [0xffff00ffff00ff4c4c4c4c4c4c4c4c, 0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 15 (by simp only [List.all_cons, List.all_nil, certAct15_21748, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord211 : RejectedWord := makeRejected [0xff00ffffffff00ff7e7e7e7e7e7e7e7e, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff0000002020202020202020 15 (by simp only [List.all_cons, List.all_nil, certAct15_28662, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_2176]; decide)
set_option maxRecDepth 16000 in
def rejectWord212 : RejectedWord := makeRejected [0xff00ffffffff00ff7e7e7e7e7e7e7e7e, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff000000000000004040404040404040 15 (by simp only [List.all_cons, List.all_nil, certAct15_28662, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_24576]; decide)
set_option maxRecDepth 16000 in
def rejectWord213 : RejectedWord := makeRejected [0xff00ffffffff00ff7e7e7e7e7e7e7e7e, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00ffffffffff00b2b2b2b2b2b2b2b2 15 (by simp only [List.all_cons, List.all_nil, certAct15_28662, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_44970]; decide)
set_option maxRecDepth 16000 in
def rejectWord214 : RejectedWord := makeRejected [0xff00ffffffff00ff7e7e7e7e7e7e7e7e, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00fffffffffffffefefefefefefefe 15 (by simp only [List.all_cons, List.all_nil, certAct15_28662, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_61438]; decide)
set_option maxRecDepth 16000 in
def rejectWord215 : RejectedWord := makeRejected [0xff00ffffffff00ff7e7e7e7e7e7e7e7e, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_28662, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord216 : RejectedWord := makeRejected [0xff00ffffffff00ff7e7e7e7e7e7e7e7e, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00ffff00ffcccccccccccccccc 15 (by simp only [List.all_cons, List.all_nil, certAct15_28662, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_62708]; decide)
set_option maxRecDepth 16000 in
def rejectWord217 : RejectedWord := makeRejected [0xff00ffffffff00ff7e7e7e7e7e7e7e7e, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffffffff00fffefefefefefefefe 15 (by simp only [List.all_cons, List.all_nil, certAct15_28662, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_65526]; decide)
set_option maxRecDepth 16000 in
def rejectWord218 : RejectedWord := makeRejected [0xff00ffffa3a3a3a3a3a3a3a3] 0xff0000000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_34959] <;> decide) (by rw [certAct15_128]; decide)
set_option maxRecDepth 16000 in
def rejectWord219 : RejectedWord := makeRejected [0xff00ffffa3a3a3a3a3a3a3a3] 0x2020202020202020 15 (by simp only [List.all_cons, List.all_nil, certAct15_34959] <;> decide) (by rw [certAct15_2048]; decide)
set_option maxRecDepth 16000 in
def rejectWord220 : RejectedWord := makeRejected [0xff00ffffa3a3a3a3a3a3a3a3] 0xff00000000ffffff1313131313131313 15 (by simp only [List.all_cons, List.all_nil, certAct15_34959] <;> decide) (by rw [certAct15_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord221 : RejectedWord := makeRejected [0xff00ffffa3a3a3a3a3a3a3a3] 0xff000000ffff4b4b4b4b4b4b4b4b 15 (by simp only [List.all_cons, List.all_nil, certAct15_34959] <;> decide) (by rw [certAct15_17487]; decide)
set_option maxRecDepth 16000 in
def rejectWord222 : RejectedWord := makeRejected [0xff00ffffa3a3a3a3a3a3a3a3] 0x8080808080808080 15 (by simp only [List.all_cons, List.all_nil, certAct15_34959] <;> decide) (by rw [certAct15_32768]; decide)
set_option maxRecDepth 16000 in
def rejectWord223 : RejectedWord := makeRejected [0xff00ffffa3a3a3a3a3a3a3a3] 0xff000000ffffffffb3b3b3b3b3b3b3b3 15 (by simp only [List.all_cons, List.all_nil, certAct15_34959] <;> decide) (by rw [certAct15_43695]; decide)
set_option maxRecDepth 16000 in
def rejectWord224 : RejectedWord := makeRejected [0xff00ffffa3a3a3a3a3a3a3a3] 0xff00ff00ffffe8e8e8e8e8e8e8e8 15 (by simp only [List.all_cons, List.all_nil, certAct15_34959] <;> decide) (by rw [certAct15_52428]; decide)
set_option maxRecDepth 16000 in
def rejectWord225 : RejectedWord := makeRejected [0xff00ffffa3a3a3a3a3a3a3a3] 0xff00ff00ffffebebebebebebebeb 15 (by simp only [List.all_cons, List.all_nil, certAct15_34959] <;> decide) (by rw [certAct15_52431]; decide)
set_option maxRecDepth 16000 in
def rejectWord226 : RejectedWord := makeRejected [0xff00ffffa3a3a3a3a3a3a3a3] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_34959] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord227 : RejectedWord := makeRejected [0xff00ffffa3a3a3a3a3a3a3a3] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 15 (by simp only [List.all_cons, List.all_nil, certAct15_34959] <;> decide) (by rw [certAct15_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord228 : RejectedWord := makeRejected [0xff00ffffa3a3a3a3a3a3a3a3] 0xffff0000ff00ffffe3e3e3e3e3e3e3e3 15 (by simp only [List.all_cons, List.all_nil, certAct15_34959] <;> decide) (by rw [certAct15_63631]; decide)
set_option maxRecDepth 16000 in
def rejectWord229 : RejectedWord := makeRejected [0xffffffffafafafafafafafaf, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00ffffff00000d0d0d0d0d0d0d0d 4 (by simp only [List.all_cons, List.all_nil, certAct4_35071, certAct4_255] <;> decide) (by rw [certAct4_4593]; decide)
set_option maxRecDepth 16000 in
def rejectWord230 : RejectedWord := makeRejected [0xffffffffafafafafafafafaf, 0xffffffff0f0f0f0f0f0f0f0f] 0xff00000000ffffff1313131313131313 4 (by simp only [List.all_cons, List.all_nil, certAct4_35071, certAct4_255] <;> decide) (by rw [certAct4_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord231 : RejectedWord := makeRejected [0xffffffffafafafafafafafaf, 0xffffffff0f0f0f0f0f0f0f0f] 0xffffff00000000ffc8c8c8c8c8c8c8c8 4 (by simp only [List.all_cons, List.all_nil, certAct4_35071, certAct4_255] <;> decide) (by rw [certAct4_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord232 : RejectedWord := makeRejected [0xffffffffafafafafafafafaf, 0xffffffff0f0f0f0f0f0f0f0f] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 4 (by simp only [List.all_cons, List.all_nil, certAct4_35071, certAct4_255] <;> decide) (by rw [certAct4_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord233 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xff00000000000000000000000000 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_1024]; decide)
set_option maxRecDepth 16000 in
def rejectWord234 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xff00ff000000ff0505050505050505 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_4373]; decide)
set_option maxRecDepth 16000 in
def rejectWord235 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xff00ff0000ffff0707070707070707 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_4383]; decide)
set_option maxRecDepth 16000 in
def rejectWord236 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffffff000000ff4d4d4d4d4d4d4d4d 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_21845]; decide)
set_option maxRecDepth 16000 in
def rejectWord237 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffff0000000000ffc0c0c0c0c0c0c0c0 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_61444]; decide)
set_option maxRecDepth 16000 in
def rejectWord238 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffffff00000000ffc8c8c8c8c8c8c8c8 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord239 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord240 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xff00ff000000ff0505050505050505 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_4373]; decide)
set_option maxRecDepth 16000 in
def rejectWord241 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xff00ff0000ffff0707070707070707 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_4383]; decide)
set_option maxRecDepth 16000 in
def rejectWord242 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffffff0000ffff4f4f4f4f4f4f4f4f 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_21855]; decide)
set_option maxRecDepth 16000 in
def rejectWord243 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffff0000000000ffc0c0c0c0c0c0c0c0 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_61444]; decide)
set_option maxRecDepth 16000 in
def rejectWord244 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffffff00000000ffc8c8c8c8c8c8c8c8 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord245 : RejectedWord := makeRejected [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 9 (by simp only [List.all_cons, List.all_nil, certAct9_36744, certAct9_17487, certAct9_4] <;> decide) (by rw [certAct9_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord246 : RejectedWord := makeRejected [0xffffff00ffffb0b0b0b0b0b0b0b0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xff00000000ff0000000000000000 9 (by simp only [List.all_cons, List.all_nil, certAct9_36748, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_1028]; decide)
set_option maxRecDepth 16000 in
def rejectWord247 : RejectedWord := makeRejected [0xffffff00ffffb0b0b0b0b0b0b0b0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xff00ff000000ff0505050505050505 9 (by simp only [List.all_cons, List.all_nil, certAct9_36748, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_4373]; decide)
set_option maxRecDepth 16000 in
def rejectWord248 : RejectedWord := makeRejected [0xffffff00ffffb0b0b0b0b0b0b0b0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xff00ff0000ffff0707070707070707 9 (by simp only [List.all_cons, List.all_nil, certAct9_36748, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_4383]; decide)
set_option maxRecDepth 16000 in
def rejectWord249 : RejectedWord := makeRejected [0xffffff00ffffb0b0b0b0b0b0b0b0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffffff000000ff4d4d4d4d4d4d4d4d 9 (by simp only [List.all_cons, List.all_nil, certAct9_36748, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_21845]; decide)
set_option maxRecDepth 16000 in
def rejectWord250 : RejectedWord := makeRejected [0xffffff00ffffb0b0b0b0b0b0b0b0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffff0000000000ffc0c0c0c0c0c0c0c0 9 (by simp only [List.all_cons, List.all_nil, certAct9_36748, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_61444]; decide)
set_option maxRecDepth 16000 in
def rejectWord251 : RejectedWord := makeRejected [0xffffff00ffffb0b0b0b0b0b0b0b0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffffff00000000ffc8c8c8c8c8c8c8c8 9 (by simp only [List.all_cons, List.all_nil, certAct9_36748, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord252 : RejectedWord := makeRejected [0xffffff00ffffb0b0b0b0b0b0b0b0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0xffff0000ff00ff00e0e0e0e0e0e0e0e0 9 (by simp only [List.all_cons, List.all_nil, certAct9_36748, certAct9_36744, certAct9_4] <;> decide) (by rw [certAct9_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord253 : RejectedWord := makeRejected [0xff00ffffffffffffb3b3b3b3b3b3b3b3, 0xff00ffff00ff00003232323232323232, 0xff00ffffa3a3a3a3a3a3a3a3] 0xff00000000ff0000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_44975, certAct15_12066, certAct15_34959] <;> decide) (by rw [certAct15_1028]; decide)
set_option maxRecDepth 16000 in
def rejectWord254 : RejectedWord := makeRejected [0xff00ffffffffffffb3b3b3b3b3b3b3b3, 0xff00ffff00ff00003232323232323232, 0xff00ffffa3a3a3a3a3a3a3a3] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_44975, certAct15_12066, certAct15_34959] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord255 : RejectedWord := makeRejected [0xff00ffffffffefefefefefefefef, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0xff00000000ffffff1313131313131313 15 (by simp only [List.all_cons, List.all_nil, certAct15_52479, certAct15_17652, certAct15_34959] <;> decide) (by rw [certAct15_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord256 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffff000000ffcdcdcdcdcdcdcdcd 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_4096, certAct15_17652] <;> decide) (by rw [certAct15_62805]; decide)
set_option maxRecDepth 16000 in
def rejectWord257 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff000000000000000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_8192]; decide)
set_option maxRecDepth 16000 in
def rejectWord258 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0x4040404040404040 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_16384]; decide)
set_option maxRecDepth 16000 in
def rejectWord259 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0x8080808080808080 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_32768]; decide)
set_option maxRecDepth 16000 in
def rejectWord260 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord261 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffff000000ffcdcdcdcdcdcdcdcd 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_62805]; decide)
set_option maxRecDepth 16000 in
def rejectWord262 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff00ffff00ff00e5e5e5e5e5e5e5e5 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_63897]; decide)
set_option maxRecDepth 16000 in
def rejectWord263 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffff00000000f0f0f0f0f0f0f0f0 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_65280]; decide)
set_option maxRecDepth 16000 in
def rejectWord264 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffff00000000f5f5f5f5f5f5f5f5 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_65297]; decide)
set_option maxRecDepth 16000 in
def rejectWord265 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffff00ff0000f2f2f2f2f2f2f2f2 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_12066, certAct15_17652] <;> decide) (by rw [certAct15_65314]; decide)
set_option maxRecDepth 16000 in
def rejectWord266 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff000000000000000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_17652] <;> decide) (by rw [certAct15_8192]; decide)
set_option maxRecDepth 16000 in
def rejectWord267 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0x4040404040404040 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_17652] <;> decide) (by rw [certAct15_16384]; decide)
set_option maxRecDepth 16000 in
def rejectWord268 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0x8080808080808080 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_17652] <;> decide) (by rw [certAct15_32768]; decide)
set_option maxRecDepth 16000 in
def rejectWord269 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffff00000000ffc8c8c8c8c8c8c8c8 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_17652] <;> decide) (by rw [certAct15_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord270 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffff000000ffcdcdcdcdcdcdcdcd 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_17652] <;> decide) (by rw [certAct15_62805]; decide)
set_option maxRecDepth 16000 in
def rejectWord271 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffff00ffff00ff00e5e5e5e5e5e5e5e5 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_17652] <;> decide) (by rw [certAct15_63897]; decide)
set_option maxRecDepth 16000 in
def rejectWord272 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffff00000000f0f0f0f0f0f0f0f0 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_17652] <;> decide) (by rw [certAct15_65280]; decide)
set_option maxRecDepth 16000 in
def rejectWord273 : RejectedWord := makeRejected [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xffffffff00000000f5f5f5f5f5f5f5f5 15 (by simp only [List.all_cons, List.all_nil, certAct15_61713, certAct15_17652] <;> decide) (by rw [certAct15_65297]; decide)
set_option maxRecDepth 16000 in
def rejectWord274 : RejectedWord := makeRejected [0xffffffffffff00ffcdcdcdcdcdcdcdcd, 0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0xff00000000ff00000000000000000000 15 (by simp only [List.all_cons, List.all_nil, certAct15_62965, certAct15_61713, certAct15_17652] <;> decide) (by rw [certAct15_8224]; decide)
set_option maxRecDepth 16000 in
def rejectWord275 : RejectedWord := makeRejected [0xffff0000ff00ff00e0e0e0e0e0e0e0e0, 0x101010101010101] 0xffffff00000000ffc8c8c8c8c8c8c8c8 1 (by simp only [List.all_cons, List.all_nil, certAct1_63624, certAct1_1] <;> decide) (by rw [certAct1_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord276 : RejectedWord := makeRejected [0xffff0000ff00ff00e0e0e0e0e0e0e0e0, 0xff00ff0000ffff0707070707070707, 0x101010101010101] 0xffffff00000000ffc8c8c8c8c8c8c8c8 1 (by simp only [List.all_cons, List.all_nil, certAct1_63624, certAct1_4383, certAct1_1] <;> decide) (by rw [certAct1_62532]; decide)

set_option maxRecDepth 16000 in
def rejectLookup (k : Nat) : RejectedWord := (if k < 2395410264 then (if k < 991728538 then (if k < 406522875 then (if k < 170843018 then (if k < 50342466 then (if k < 24055063 then (if k < 4511858 then (if k < 1632000 then rejectWord6 else rejectWord1) else (if k < 8160000 then rejectWord129 else rejectWord8)) else (if k < 49821511 then (if k < 49643462 then rejectWord177 else rejectWord187) else (if k < 49978202 then rejectWord40 else rejectWord77))) else (if k < 76364013 then (if k < 50600017 then (if k < 50529039 then rejectWord97 else rejectWord25) else (if k < 64797092 then rejectWord220 else rejectWord89)) else (if k < 120647112 then (if k < 92434654 then rejectWord211 else rejectWord193) else (if k < 156955510 then rejectWord161 else (if k < 163248595 then rejectWord34 else rejectWord94))))) else (if k < 290167429 then (if k < 202116108 then (if k < 196741940 then (if k < 175053268 then rejectWord244 else rejectWord63) else (if k < 202109849 then rejectWord27 else rejectWord26)) else (if k < 256876399 then (if k < 242382026 then rejectWord0 else rejectWord16) else (if k < 267228257 then rejectWord84 else rejectWord249))) else (if k < 340943357 then (if k < 290866433 then (if k < 290502169 then rejectWord195 else rejectWord80) else (if k < 298680085 then rejectWord101 else rejectWord247)) else (if k < 378224569 then (if k < 362466379 then rejectWord181 else rejectWord162) else (if k < 404232216 then rejectWord239 else (if k < 405040859 then rejectWord2 else rejectWord57)))))) else (if k < 661168496 then (if k < 543974474 then (if k < 453112081 then (if k < 430892471 then (if k < 417792000 then rejectWord69 else rejectWord3) else (if k < 446681538 then rejectWord114 else rejectWord59)) else (if k < 500526002 then (if k < 488139578 then rejectWord88 else rejectWord245) else (if k < 535305266 then rejectWord49 else rejectWord132))) else (if k < 602031414 then (if k < 555958377 then (if k < 552915158 then rejectWord140 else rejectWord100) else (if k < 591386095 then rejectWord142 else rejectWord56)) else (if k < 611072057 then (if k < 603506362 then rejectWord75 else rejectWord168) else (if k < 621498726 then rejectWord256 else (if k < 634134885 then rejectWord150 else rejectWord248))))) else (if k < 855861925 then (if k < 755549279 then (if k < 720644006 then (if k < 683282766 then rejectWord146 else rejectWord71) else (if k < 736177991 then rejectWord208 else rejectWord36)) else (if k < 776467814 then (if k < 762938796 then rejectWord122 else rejectWord72) else (if k < 808464432 then rejectWord275 else (if k < 809649725 then rejectWord4 else rejectWord219)))) else (if k < 886434866 then (if k < 868823713 then (if k < 861644150 then rejectWord192 else rejectWord65) else (if k < 870094282 then rejectWord10 else rejectWord126)) else (if k < 932951970 then (if k < 916973254 then rejectWord127 else rejectWord160) else (if k < 948751320 then rejectWord17 else (if k < 977244885 then rejectWord157 else rejectWord201))))))) else (if k < 1709913370 then (if k < 1226862976 then (if k < 1099823908 then (if k < 1058445790 then (if k < 1017267762 then (if k < 992595953 then rejectWord112 else rejectWord251) else (if k < 1032501067 then rejectWord117 else rejectWord183)) else (if k < 1069312437 then (if k < 1064280566 then rejectWord259 else rejectWord186) else (if k < 1087935133 then rejectWord164 else rejectWord196))) else (if k < 1165903346 then (if k < 1115231870 then (if k < 1111277715 then rejectWord260 else rejectWord158) else (if k < 1116188425 then rejectWord165 else rejectWord173)) else (if k < 1198250972 then (if k < 1187174244 then rejectWord28 else rejectWord232) else (if k < 1212048955 then rejectWord136 else (if k < 1220887625 then rejectWord131 else rejectWord209))))) else (if k < 1538184185 then (if k < 1352864441 then (if k < 1300505851 then (if k < 1288693826 then rejectWord134 else rejectWord23) else (if k < 1309892513 then rejectWord175 else rejectWord252)) else (if k < 1424141110 then (if k < 1401577949 then rejectWord111 else rejectWord107) else (if k < 1471309409 then rejectWord110 else rejectWord139))) else (if k < 1593052000 then (if k < 1551000966 then (if k < 1546771857 then rejectWord210 else rejectWord236) else (if k < 1561000173 then rejectWord138 else rejectWord30)) else (if k < 1617355170 then (if k < 1616928864 then rejectWord254 else rejectWord7) else (if k < 1635847989 then rejectWord189 else (if k < 1664480038 then rejectWord270 else rejectWord225)))))) else (if k < 2021902249 then (if k < 1881077783 then (if k < 1789762188 then (if k < 1744770602 then (if k < 1727381741 then rejectWord67 else rejectWord188) else (if k < 1773429581 then rejectWord264 else rejectWord68)) else (if k < 1802828379 then (if k < 1793936189 then rejectWord266 else rejectWord153) else (if k < 1803527383 then rejectWord200 else rejectWord104))) else (if k < 1955491348 then (if k < 1916792368 then (if k < 1882571072 then rejectWord234 else rejectWord263) else (if k < 1918560252 then rejectWord120 else rejectWord170)) else (if k < 1988405432 then (if k < 1987440229 then rejectWord54 else rejectWord70) else (if k < 2007584339 then rejectWord149 else (if k < 2011756183 then rejectWord255 else rejectWord105))))) else (if k < 2197815916 then (if k < 2139508293 then (if k < 2104247875 then (if k < 2088960000 then rejectWord86 else rejectWord11) else (if k < 2108057297 then rejectWord156 else rejectWord61)) else (if k < 2172748165 then (if k < 2148658674 then rejectWord45 else rejectWord74) else (if k < 2179827991 then rejectWord20 else (if k < 2192781049 then rejectWord191 else rejectWord92)))) else (if k < 2288352565 then (if k < 2235856812 then (if k < 2202416080 then rejectWord15 else rejectWord151) else (if k < 2254871011 then rejectWord171 else rejectWord42)) else (if k < 2327189569 then (if k < 2294179808 then rejectWord143 else rejectWord155) else (if k < 2355992179 then rejectWord204 else (if k < 2371196341 then rejectWord52 else rejectWord145)))))))) else (if k < 3247941720 then (if k < 2733416121 then (if k < 2589888690 then (if k < 2511981307 then (if k < 2467901153 then (if k < 2406813687 then (if k < 2402263100 then rejectWord130 else rejectWord91) else (if k < 2407148427 then rejectWord194 else rejectWord79)) else (if k < 2508879316 then (if k < 2482138576 then rejectWord257 else rejectWord163) else (if k < 2511506995 then rejectWord214 else rejectWord206))) else (if k < 2551279497 then (if k < 2535354281 then (if k < 2519898366 then rejectWord235 else rejectWord31) else (if k < 2540732264 then rejectWord178 else rejectWord135)) else (if k < 2562280908 then (if k < 2556704695 then rejectWord230 else rejectWord272) else (if k < 2563256411 then rejectWord221 else (if k < 2570288663 then rejectWord96 else rejectWord228))))) else (if k < 2653812419 then (if k < 2608105247 then (if k < 2596462711 then (if k < 2593665222 then rejectWord113 else rejectWord141) else (if k < 2605649125 then rejectWord125 else rejectWord144)) else (if k < 2615377227 then (if k < 2612101232 then rejectWord246 else rejectWord62) else (if k < 2624464261 then rejectWord81 else rejectWord172))) else (if k < 2708200733 then (if k < 2697105779 then (if k < 2696149224 then rejectWord212 else rejectWord167) else (if k < 2702809125 then rejectWord174 else rejectWord116)) else (if k < 2712320834 then (if k < 2711927086 then rejectWord106 else rejectWord185) else (if k < 2720407974 then rejectWord44 else (if k < 2724888820 then rejectWord33 else rejectWord190)))))) else (if k < 3030400119 then (if k < 2859649257 then (if k < 2798036628 then (if k < 2751522633 then (if k < 2733967742 then rejectWord243 else rejectWord19) else (if k < 2779097005 then rejectWord109 else rejectWord37)) else (if k < 2822291806 then (if k < 2804466259 then rejectWord12 else rejectWord169) else (if k < 2831951879 then rejectWord258 else rejectWord180))) else (if k < 2932970522 then (if k < 2914791590 then (if k < 2907381669 then rejectWord216 else rejectWord124) else (if k < 2925793956 then rejectWord93 else rejectWord233)) else (if k < 2978004205 then (if k < 2933334786 then rejectWord76 else rejectWord95) else (if k < 3006274089 then rejectWord47 else (if k < 3024435238 then rejectWord29 else rejectWord202))))) else (if k < 3129064569 then (if k < 3054352464 then (if k < 3044639495 then (if k < 3031716636 then rejectWord265 else rejectWord35) else (if k < 3049581190 then rejectWord99 else rejectWord215)) else (if k < 3070693048 then (if k < 3068430203 then rejectWord58 else rejectWord269) else (if k < 3073966425 then rejectWord60 else (if k < 3092274506 then rejectWord53 else rejectWord238)))) else (if k < 3208561294 then (if k < 3158261446 then (if k < 3140474564 then rejectWord24 else rejectWord87) else (if k < 3166257805 then rejectWord14 else rejectWord179)) else (if k < 3233857728 then (if k < 3216765343 then rejectWord253 else rejectWord271) else (if k < 3235635725 then rejectWord9 else (if k < 3244077105 then rejectWord222 else rejectWord46))))))) else (if k < 3727687312 then (if k < 3414587418 then (if k < 3381735200 then (if k < 3318462093 then (if k < 3294185134 then (if k < 3266737052 then rejectWord137 else rejectWord123) else (if k < 3305436032 then rejectWord21 else rejectWord55)) else (if k < 3347878242 then (if k < 3342002907 then rejectWord261 else rejectWord267) else (if k < 3351545482 then rejectWord73 else rejectWord64))) else (if k < 3401108302 then (if k < 3387534824 then (if k < 3387013869 then rejectWord18 else rejectWord41) else (if k < 3400248121 then rejectWord98 else rejectWord108)) else (if k < 3414193670 then (if k < 3407622127 then rejectWord13 else rejectWord90) else (if k < 3414371719 then rejectWord197 else (if k < 3414528410 then rejectWord43 else rejectWord82))))) else (if k < 3555169056 then (if k < 3423007870 then (if k < 3415150225 then (if k < 3414892674 then rejectWord50 else rejectWord102) else (if k < 3420256970 then rejectWord226 else rejectWord198)) else (if k < 3447766438 then (if k < 3426144202 then rejectWord203 else rejectWord32) else (if k < 3480495230 then rejectWord223 else (if k < 3545230148 then rejectWord48 else rejectWord22)))) else (if k < 3648854882 then (if k < 3635758653 then (if k < 3566521333 then rejectWord250 else rejectWord147) else (if k < 3640627347 then rejectWord262 else rejectWord276)) else (if k < 3662257053 then (if k < 3649811437 then rejectWord184 else rejectWord218) else (if k < 3669754574 then rejectWord152 else (if k < 3724657798 then rejectWord229 else rejectWord166)))))) else (if k < 4002050164 then (if k < 3901224181 then (if k < 3838083212 then (if k < 3746551004 then (if k < 3736151621 then rejectWord176 else rejectWord224) else (if k < 3771894441 then rejectWord182 else rejectWord240)) else (if k < 3893853302 then (if k < 3875537016 then rejectWord217 else rejectWord5) else (if k < 3897056625 then rejectWord38 else rejectWord268))) else (if k < 3940912913 then (if k < 3915462540 then (if k < 3908106923 then rejectWord231 else rejectWord205) else (if k < 3919473337 then rejectWord121 else rejectWord274)) else (if k < 3981634150 then (if k < 3975052495 then rejectWord133 else rejectWord154) else (if k < 3982182589 then rejectWord237 else (if k < 3999735527 then rejectWord128 else rejectWord66))))) else (if k < 4163700526 then (if k < 4107349241 then (if k < 4075897413 then (if k < 4069715831 then rejectWord78 else rejectWord115) else (if k < 4076463273 then rejectWord242 else rejectWord273)) else (if k < 4131531146 then (if k < 4130135038 then rejectWord241 else rejectWord207) else (if k < 4132158729 then rejectWord159 else (if k < 4141431005 then rejectWord213 else rejectWord85)))) else (if k < 4223203814 then (if k < 4222810066 then (if k < 4202247350 then rejectWord148 else rejectWord119) else (if k < 4223144806 then rejectWord199 else rejectWord83)) else (if k < 4223766621 then (if k < 4223509070 then rejectWord51 else rejectWord103) else (if k < 4243209452 then rejectWord227 else (if k < 4283726479 then rejectWord39 else rejectWord118)))))))))

set_option maxRecDepth 16000 in
def allowed (rev : List W) (z : W) : Bool :=
  let q := rejectLookup (rejectKey rev z)
  !(q.val == z && q.rev == rev)

set_option maxRecDepth 16000 in
theorem allowed_of_min (rev : List W) (z : W)
    (h : ∀ i : Fin 16, (∀ w ∈ rev, aut i w = w) → z.toNat ≤ (aut i z).toNat) :
    allowed rev z = true := by
  let q := rejectLookup (rejectKey rev z)
  change (!(q.val == z && q.rev == rev)) = true
  by_cases hz : q.val = z
  · by_cases hr : q.rev = rev
    · have fixed : ∀ w ∈ rev, aut q.g w = w := hr ▸ q.fixes
      have sm : (aut q.g z).toNat < z.toNat := hz ▸ q.lower
      exact (Nat.not_lt_of_ge (h q.g fixed) sm).elim
    · simp [hr]
  · simp [hz]

-- For each recorded first-step context, the corresponding subtree has already been excluded.
set_option maxRecDepth 16000 in
theorem allContextCons {α : Type} {f : α → Bool} {x : α} {xs : List α}
    (hh : f x = true) (ht : xs.all f = true) : (x :: xs).all f = true := by
  simp only [List.all_cons, hh, ht, Bool.and_self]

set_option maxRecDepth 16000 in
def cacheNext (f : Nat → Nat → List W → Bool) (tab : List (Nat × Nat × List W))
    (e w : Nat) (ws : List W) : Bool := if (e,w,ws) ∈ tab then false else f e w ws

set_option maxRecDepth 16000 in
theorem cacheNext_eq (f : Nat → Nat → List W → Bool) (tab : List (Nat × Nat × List W))
    (h : tab.all (fun t => !(f t.1 t.2.1 t.2.2)) = true) : cacheNext f tab = f := by
  funext e w ws
  unfold cacheNext
  split_ifs with ht
  · have yes := List.all_eq_true.mp h (e,w,ws) ht
    dsimp only at yes
    cases hv : f e w ws <;> simp_all
  · rfl

set_option maxRecDepth 16000 in
def cachedBranch (m k : Nat) (rev : List W) (tab : List (Nat × Nat × List W))
    (e last : Nat) (ws : List W) : Bool :=
  ws == [goal] || (pairs ws).any (fun (a,b,r) => dispatch e last
    (fun e' w ys => allowed rev (BitVec.ofNat 128 w) && cacheNext
      (fun e'' w' zs => symSearch allowed m k (BitVec.ofNat 128 w' :: rev) e'' w' zs) tab e' w ys) a b r)

set_option maxRecDepth 16000 in
theorem cachedBranch_eq (m k : Nat) (rev : List W) (tab : List (Nat × Nat × List W))
    (h : tab.all (fun t => !(symSearch allowed m k (BitVec.ofNat 128 t.2.1 :: rev) t.1 t.2.1 t.2.2)) = true) :
    cachedBranch m k rev tab = symSearch allowed (m+1) k rev := by
  have hc := cacheNext_eq (fun e w zs => symSearch allowed m k (BitVec.ofNat 128 w :: rev) e w zs) tab h
  funext e last ws
  simp only [cachedBranch, symSearch, hc]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode209 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode208 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode207 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode206 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode205 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode204 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode203 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode202 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode201 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode200 : symSearch allowed 2 6 [0xffffff000000ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffff000000ff4d4d4d4d4d4d4d4d [0xffffff000000ff4d4d4d4d4d4d4d4d, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode199 : symSearch allowed 2 6 [0xffff000000ff7878787878787878, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffff000000ff7878787878787878 [0xffff000000ff7878787878787878, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode198 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode197 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode196 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode195 : symSearch allowed 2 6 [0xffffffff00003c3c3c3c3c3c3c3c, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffffff00003c3c3c3c3c3c3c3c [0xffffffff00003c3c3c3c3c3c3c3c, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode194 : symSearch allowed 2 6 [0xff00000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00000000000000000000 [0xff00000000000000000000, 0xff00000000ff00001212121212121212, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode193 : symSearch allowed 2 6 [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffffffff00ff4d4d4d4d4d4d4d4d [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ff000000000505050505050505, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode192 : symSearch allowed 2 6 [0x404040404040404, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0x404040404040404 [0x404040404040404, 0xff00ff000000000505050505050505, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode191 : symSearch allowed 2 6 [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffffff00ff7c7c7c7c7c7c7c7c [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xffff000000003030303030303030, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode190 : symSearch allowed 2 6 [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffffffff4f4f4f4f4f4f4f4f [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode189 : symSearch allowed 2 6 [0xff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff0000000000000000 [0xff0000000000000000, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable188 : List (Nat × Nat × List W) := [
  (0, 0xff0000000000000000, [0xff0000000000000000, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffffffff4f4f4f4f4f4f4f4f, [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffffff00ff7c7c7c7c7c7c7c7c, [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xffff000000003030303030303030, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0x404040404040404, [0x404040404040404, 0xff00ff000000000505050505050505, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffffffff00ff4d4d4d4d4d4d4d4d, [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ff000000000505050505050505, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00000000000000000000, [0xff00000000000000000000, 0xff00000000ff00001212121212121212, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffffff00003c3c3c3c3c3c3c3c, [0xffffffff00003c3c3c3c3c3c3c3c, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffff000000ff7878787878787878, [0xffff000000ff7878787878787878, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffff000000ff4d4d4d4d4d4d4d4d, [0xffffff000000ff4d4d4d4d4d4d4d4d, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212])]

set_option maxRecDepth 16000 in
theorem contextGood188 : contextTable188.all (fun t => !(symSearch allowed 2 6 (BitVec.ofNat 128 t.2.1 :: [0xff00ffff00ff4c4c4c4c4c4c4c4c]) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable188
  exact (allContextCons (congrArg Bool.not numericNode189) (allContextCons (congrArg Bool.not numericNode190) (allContextCons (congrArg Bool.not numericNode191) (allContextCons (congrArg Bool.not numericNode192) (allContextCons (congrArg Bool.not numericNode193) (allContextCons (congrArg Bool.not numericNode194) (allContextCons (congrArg Bool.not numericNode195) (allContextCons (congrArg Bool.not numericNode196) (allContextCons (congrArg Bool.not numericNode197) (allContextCons (congrArg Bool.not numericNode198) (allContextCons (congrArg Bool.not numericNode199) (allContextCons (congrArg Bool.not numericNode200) (allContextCons (congrArg Bool.not numericNode201) (allContextCons (congrArg Bool.not numericNode202) (allContextCons (congrArg Bool.not numericNode203) (allContextCons (congrArg Bool.not numericNode204) (allContextCons (congrArg Bool.not numericNode205) (allContextCons (congrArg Bool.not numericNode206) (allContextCons (congrArg Bool.not numericNode207) (allContextCons (congrArg Bool.not numericNode208) (allContextCons (congrArg Bool.not numericNode209) rfl)))))))))))))))))))))

set_option maxRecDepth 16000 in
theorem contextEq188 : cachedBranch 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] contextTable188 = symSearch allowed 3 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] := cachedBranch_eq 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] contextTable188 contextGood188

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode188 : symSearch allowed 3 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by
  rw [← contextEq188]
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode187 : symSearch allowed 2 6 [0xff00ffff00ff00a5a5a5a5a5a5a5a5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffff00ff00a5a5a5a5a5a5a5a5 [0xff00ffff00ff00a5a5a5a5a5a5a5a5, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode186 : symSearch allowed 2 6 [0xffff00ff00ff00001717171717171717, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffff00ff00ff00001717171717171717 [0xffff00ff00ff00001717171717171717, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode185 : symSearch allowed 2 6 [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffff00ff00000000c5c5c5c5c5c5c5c5 [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode184 : symSearch allowed 2 6 [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff0000000000000000000000000000 [0xff0000000000000000000000000000, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode183 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode182 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode181 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode180 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode179 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode178 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode177 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode176 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode175 : symSearch allowed 2 6 [0xffffff000000003535353535353535, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffff000000003535353535353535 [0xffffff000000003535353535353535, 0xffff000000003030303030303030, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode174 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode173 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode172 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode171 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode170 : symSearch allowed 2 6 [0xffff0000ffff3333333333333333, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffff0000ffff3333333333333333 [0xffff0000ffff3333333333333333, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode169 : symSearch allowed 2 6 [0xffffff000000ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffff000000ff4d4d4d4d4d4d4d4d [0xffffff000000ff4d4d4d4d4d4d4d4d, 0xff00000000ff4848484848484848, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode168 : symSearch allowed 2 6 [0xffffff000000ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffff000000ff4d4d4d4d4d4d4d4d [0xffffff000000ff4d4d4d4d4d4d4d4d, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode167 : symSearch allowed 2 6 [0xffff000000ff7878787878787878, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffff000000ff7878787878787878 [0xffff000000ff7878787878787878, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode166 : symSearch allowed 2 6 [0xffff000000ff7878787878787878, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffff000000ff7878787878787878 [0xffff000000ff7878787878787878, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode165 : symSearch allowed 2 6 [0xff00000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00000000000000000000 [0xff00000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode164 : symSearch allowed 2 6 [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffffffff00ff4d4d4d4d4d4d4d4d [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode163 : symSearch allowed 2 6 [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffffffff00ff4d4d4d4d4d4d4d4d [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode162 : symSearch allowed 2 6 [0x404040404040404, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0x404040404040404 [0x404040404040404, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode161 : symSearch allowed 2 6 [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffffff00ff7c7c7c7c7c7c7c7c [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000003030303030303030, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode160 : symSearch allowed 2 6 [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffffffff4f4f4f4f4f4f4f4f [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode159 : symSearch allowed 2 6 [0xff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff0000000000000000 [0xff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable158 : List (Nat × Nat × List W) := [
  (0, 0xff0000000000000000, [0xff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffffffff4f4f4f4f4f4f4f4f, [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffffff00ff7c7c7c7c7c7c7c7c, [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000003030303030303030, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0x404040404040404, [0x404040404040404, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffffffffff00ff4d4d4d4d4d4d4d4d, [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffffffff00ff4d4d4d4d4d4d4d4d, [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00000000000000000000, [0xff00000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffff000000ff7878787878787878, [0xffff000000ff7878787878787878, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffff000000ff7878787878787878, [0xffff000000ff7878787878787878, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffffff000000ff4d4d4d4d4d4d4d4d, [0xffffff000000ff4d4d4d4d4d4d4d4d, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffff000000ff4d4d4d4d4d4d4d4d, [0xffffff000000ff4d4d4d4d4d4d4d4d, 0xff00000000ff4848484848484848, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffff0000ffff3333333333333333, [0xffff0000ffff3333333333333333, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (2, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffff000000003535353535353535, [0xffffff000000003535353535353535, 0xffff000000003030303030303030, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (2, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (2, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xff0000000000000000000000000000, [0xff0000000000000000000000000000, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffff00ff00000000c5c5c5c5c5c5c5c5, [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffff00ff00ff00001717171717171717, [0xffff00ff00ff00001717171717171717, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff00a5a5a5a5a5a5a5a5, [0xff00ffff00ff00a5a5a5a5a5a5a5a5, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212])]

set_option maxRecDepth 16000 in
theorem contextGood158 : contextTable158.all (fun t => !(symSearch allowed 2 6 (BitVec.ofNat 128 t.2.1 :: [0xff00ffff00ff4c4c4c4c4c4c4c4c]) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable158
  exact (allContextCons (congrArg Bool.not numericNode159) (allContextCons (congrArg Bool.not numericNode160) (allContextCons (congrArg Bool.not numericNode161) (allContextCons (congrArg Bool.not numericNode162) (allContextCons (congrArg Bool.not numericNode163) (allContextCons (congrArg Bool.not numericNode164) (allContextCons (congrArg Bool.not numericNode165) (allContextCons (congrArg Bool.not numericNode166) (allContextCons (congrArg Bool.not numericNode167) (allContextCons (congrArg Bool.not numericNode168) (allContextCons (congrArg Bool.not numericNode169) (allContextCons (congrArg Bool.not numericNode170) (allContextCons (congrArg Bool.not numericNode171) (allContextCons (congrArg Bool.not numericNode172) (allContextCons (congrArg Bool.not numericNode173) (allContextCons (congrArg Bool.not numericNode174) (allContextCons (congrArg Bool.not numericNode175) (allContextCons (congrArg Bool.not numericNode176) (allContextCons (congrArg Bool.not numericNode177) (allContextCons (congrArg Bool.not numericNode178) (allContextCons (congrArg Bool.not numericNode179) (allContextCons (congrArg Bool.not numericNode180) (allContextCons (congrArg Bool.not numericNode181) (allContextCons (congrArg Bool.not numericNode182) (allContextCons (congrArg Bool.not numericNode183) (allContextCons (congrArg Bool.not numericNode184) (allContextCons (congrArg Bool.not numericNode185) (allContextCons (congrArg Bool.not numericNode186) (allContextCons (congrArg Bool.not numericNode187) rfl)))))))))))))))))))))))))))))

set_option maxRecDepth 16000 in
theorem contextEq158 : cachedBranch 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] contextTable158 = symSearch allowed 3 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] := cachedBranch_eq 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] contextTable158 contextGood158

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode158 : symSearch allowed 3 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by
  rw [← contextEq158]
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode157 : symSearch allowed 2 6 [0xff00ffff00ff00a5a5a5a5a5a5a5a5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffff00ff00a5a5a5a5a5a5a5a5 [0xff00ffff00ff00a5a5a5a5a5a5a5a5, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode156 : symSearch allowed 2 6 [0xffff00ff00ff00001717171717171717, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffff00ff00ff00001717171717171717 [0xffff00ff00ff00001717171717171717, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode155 : symSearch allowed 2 6 [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffff00ff00000000c5c5c5c5c5c5c5c5 [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode154 : symSearch allowed 2 6 [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff0000000000000000000000000000 [0xff0000000000000000000000000000, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode153 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode152 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode151 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode150 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode149 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode148 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode147 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode146 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode145 : symSearch allowed 2 6 [0xffffff000000003535353535353535, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffff000000003535353535353535 [0xffffff000000003535353535353535, 0xffff000000003030303030303030, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode144 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode143 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode142 : symSearch allowed 2 6 [0xffff0000ffff3333333333333333, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffff0000ffff3333333333333333 [0xffff0000ffff3333333333333333, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode141 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode140 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode139 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode138 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode137 : symSearch allowed 2 6 [0xffffffff00003c3c3c3c3c3c3c3c, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffffff00003c3c3c3c3c3c3c3c [0xffffffff00003c3c3c3c3c3c3c3c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode136 : symSearch allowed 2 6 [0xffffffff00003c3c3c3c3c3c3c3c, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffffff00003c3c3c3c3c3c3c3c [0xffffffff00003c3c3c3c3c3c3c3c, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode135 : symSearch allowed 2 6 [0xff00000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00000000000000000000 [0xff00000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff00001212121212121212, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode134 : symSearch allowed 2 6 [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffffffff00ff4d4d4d4d4d4d4d4d [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode133 : symSearch allowed 2 6 [0x404040404040404, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0x404040404040404 [0x404040404040404, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode132 : symSearch allowed 2 6 [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xffffffff00ff7c7c7c7c7c7c7c7c [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000003030303030303030, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode131 : symSearch allowed 2 6 [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff00ffffffff4f4f4f4f4f4f4f4f [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode130 : symSearch allowed 2 6 [0xff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 0 0xff0000000000000000 [0xff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable129 : List (Nat × Nat × List W) := [
  (0, 0xff0000000000000000, [0xff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffffffff4f4f4f4f4f4f4f4f, [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffffff00ff7c7c7c7c7c7c7c7c, [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000003030303030303030, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0x404040404040404, [0x404040404040404, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffffffff00ff4d4d4d4d4d4d4d4d, [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00000000000000000000, [0xff00000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff00001212121212121212, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffffffff00003c3c3c3c3c3c3c3c, [0xffffffff00003c3c3c3c3c3c3c3c, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffffff00003c3c3c3c3c3c3c3c, [0xffffffff00003c3c3c3c3c3c3c3c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (2, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffff0000ffff3333333333333333, [0xffff0000ffff3333333333333333, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffff000000003535353535353535, [0xffffff000000003535353535353535, 0xffff000000003030303030303030, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (2, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (2, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xff0000000000000000000000000000, [0xff0000000000000000000000000000, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffff00ff00000000c5c5c5c5c5c5c5c5, [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffff00ff00ff00001717171717171717, [0xffff00ff00ff00001717171717171717, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff00a5a5a5a5a5a5a5a5, [0xff00ffff00ff00a5a5a5a5a5a5a5a5, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212])]

set_option maxRecDepth 16000 in
theorem contextGood129 : contextTable129.all (fun t => !(symSearch allowed 2 6 (BitVec.ofNat 128 t.2.1 :: [0xff00ffff00ff4c4c4c4c4c4c4c4c]) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable129
  exact (allContextCons (congrArg Bool.not numericNode130) (allContextCons (congrArg Bool.not numericNode131) (allContextCons (congrArg Bool.not numericNode132) (allContextCons (congrArg Bool.not numericNode133) (allContextCons (congrArg Bool.not numericNode134) (allContextCons (congrArg Bool.not numericNode135) (allContextCons (congrArg Bool.not numericNode136) (allContextCons (congrArg Bool.not numericNode137) (allContextCons (congrArg Bool.not numericNode138) (allContextCons (congrArg Bool.not numericNode139) (allContextCons (congrArg Bool.not numericNode140) (allContextCons (congrArg Bool.not numericNode141) (allContextCons (congrArg Bool.not numericNode142) (allContextCons (congrArg Bool.not numericNode143) (allContextCons (congrArg Bool.not numericNode144) (allContextCons (congrArg Bool.not numericNode145) (allContextCons (congrArg Bool.not numericNode146) (allContextCons (congrArg Bool.not numericNode147) (allContextCons (congrArg Bool.not numericNode148) (allContextCons (congrArg Bool.not numericNode149) (allContextCons (congrArg Bool.not numericNode150) (allContextCons (congrArg Bool.not numericNode151) (allContextCons (congrArg Bool.not numericNode152) (allContextCons (congrArg Bool.not numericNode153) (allContextCons (congrArg Bool.not numericNode154) (allContextCons (congrArg Bool.not numericNode155) (allContextCons (congrArg Bool.not numericNode156) (allContextCons (congrArg Bool.not numericNode157) rfl))))))))))))))))))))))))))))

set_option maxRecDepth 16000 in
theorem contextEq129 : cachedBranch 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] contextTable129 = symSearch allowed 3 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] := cachedBranch_eq 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] contextTable129 contextGood129

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode129 : symSearch allowed 3 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by
  rw [← contextEq129]
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode128 : symSearch allowed 2 6 [0xff00ffff00ff00a5a5a5a5a5a5a5a5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffff00ff00a5a5a5a5a5a5a5a5 [0xff00ffff00ff00a5a5a5a5a5a5a5a5, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode127 : symSearch allowed 2 6 [0xffff00ff00ff00001717171717171717, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffff00ff00ff00001717171717171717 [0xffff00ff00ff00001717171717171717, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode126 : symSearch allowed 2 6 [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffff00ff00000000c5c5c5c5c5c5c5c5 [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode125 : symSearch allowed 2 6 [0xff0000000000000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff0000000000000000000000000000 [0xff0000000000000000000000000000, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode124 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode123 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode122 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode121 : symSearch allowed 1 6 [0xffff00ff00ff00001717171717171717, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffff00ff00ff00001717171717171717 [0xffff00ff00ff00001717171717171717, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode120 : symSearch allowed 1 6 [0xffff000000ff0000d2d2d2d2d2d2d2d2, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffff000000ff0000d2d2d2d2d2d2d2d2 [0xffff000000ff0000d2d2d2d2d2d2d2d2, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00ff000000000505050505050505] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode119 : symSearch allowed 1 6 [0xff000000000000000000000000000000, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff000000000000000000000000000000 [0xff000000000000000000000000000000, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00ff000000000505050505050505] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode118 : symSearch allowed 1 6 [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffff00ff00000000c5c5c5c5c5c5c5c5 [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode117 : symSearch allowed 1 6 [0xff0000000000000000000000000000, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff0000000000000000000000000000 [0xff0000000000000000000000000000, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode116 : symSearch allowed 1 6 [0xff00000000ffffff1313131313131313, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00000000ffffff1313131313131313 [0xff00000000ffffff1313131313131313, 0xffff0303030303030303, 0xff00000000ff00001212121212121212, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode115 : symSearch allowed 1 6 [0xff00000000ffffff1313131313131313, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xff00000000ffffff1313131313131313 [0xff00000000ffffff1313131313131313, 0xffff0303030303030303, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode114 : symSearch allowed 1 6 [0xff00ff0000ffff0707070707070707, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode113 : symSearch allowed 1 6 [0xff00ff0000ffff0707070707070707, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode112 : symSearch allowed 1 6 [0xffff00000000ffffc3c3c3c3c3c3c3c3, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffff00000000ffffc3c3c3c3c3c3c3c3 [0xffff00000000ffffc3c3c3c3c3c3c3c3, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode111 : symSearch allowed 1 6 [0xff00ff00ffff00ff5e5e5e5e5e5e5e5e, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ff00ffff00ff5e5e5e5e5e5e5e5e [0xff00ff00ffff00ff5e5e5e5e5e5e5e5e, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff00001212121212121212, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode110 : symSearch allowed 1 6 [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffffffff00ff4d4d4d4d4d4d4d4d [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode109 : symSearch allowed 1 6 [0xffffff00ffff00ffcccccccccccccccc, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffff00ffff00ffcccccccccccccccc [0xffffff00ffff00ffcccccccccccccccc, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode108 : symSearch allowed 1 6 [0xff00ffffffffff00b2b2b2b2b2b2b2b2, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffffffffff00b2b2b2b2b2b2b2b2 [0xff00ffffffffff00b2b2b2b2b2b2b2b2, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode107 : symSearch allowed 1 6 [0x1010101010101010, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0x1010101010101010 [0x1010101010101010, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode106 : symSearch allowed 1 6 [0xffffffff00ff00b5b5b5b5b5b5b5b5, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffffff00ff00b5b5b5b5b5b5b5b5 [0xffffffff00ff00b5b5b5b5b5b5b5b5, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode105 : symSearch allowed 1 6 [0xff000000000000000000000000, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff000000000000000000000000 [0xff000000000000000000000000, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode104 : symSearch allowed 1 6 [0xffffffffff00ff00f0f0f0f0f0f0f0f0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffffffff00ff00f0f0f0f0f0f0f0f0 [0xffffffffff00ff00f0f0f0f0f0f0f0f0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode103 : symSearch allowed 1 6 [0x8080808080808080, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0x8080808080808080 [0x8080808080808080, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode102 : symSearch allowed 1 6 [0xffffff00ffffb3b3b3b3b3b3b3b3, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffff00ffffb3b3b3b3b3b3b3b3 [0xffffff00ffffb3b3b3b3b3b3b3b3, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode101 : symSearch allowed 1 6 [0xff000000000000000000, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff000000000000000000 [0xff000000000000000000, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode100 : symSearch allowed 1 6 [0xfffffffffffffcfcfcfcfcfcfcfc, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xfffffffffffffcfcfcfcfcfcfcfc [0xfffffffffffffcfcfcfcfcfcfcfc, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode99 : symSearch allowed 1 6 [0xff00ff0000000000000000000000, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ff0000000000000000000000 [0xff00ff0000000000000000000000, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable98 : List (Nat × Nat × List W) := [
  (1, 0xff00ff0000000000000000000000, [0xff00ff0000000000000000000000, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xfffffffffffffcfcfcfcfcfcfcfc, [0xfffffffffffffcfcfcfcfcfcfcfc, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xff000000000000000000, [0xff000000000000000000, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xffffff00ffffb3b3b3b3b3b3b3b3, [0xffffff00ffffb3b3b3b3b3b3b3b3, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0x8080808080808080, [0x8080808080808080, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xffffffffff00ff00f0f0f0f0f0f0f0f0, [0xffffffffff00ff00f0f0f0f0f0f0f0f0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xff000000000000000000000000, [0xff000000000000000000000000, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212]),
  (1, 0xffffffff00ff00b5b5b5b5b5b5b5b5, [0xffffffff00ff00b5b5b5b5b5b5b5b5, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212]),
  (1, 0x1010101010101010, [0x1010101010101010, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505]),
  (1, 0xff00ffffffffff00b2b2b2b2b2b2b2b2, [0xff00ffffffffff00b2b2b2b2b2b2b2b2, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505]),
  (1, 0xffffff00ffff00ffcccccccccccccccc, [0xffffff00ffff00ffcccccccccccccccc, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xffffffffff00ff4d4d4d4d4d4d4d4d, [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212]),
  (1, 0xff00ff00ffff00ff5e5e5e5e5e5e5e5e, [0xff00ff00ffff00ff5e5e5e5e5e5e5e5e, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff00001212121212121212, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505]),
  (1, 0xffff00000000ffffc3c3c3c3c3c3c3c3, [0xffff00000000ffffc3c3c3c3c3c3c3c3, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (2, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212]),
  (1, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212]),
  (2, 0xff00000000ffffff1313131313131313, [0xff00000000ffffff1313131313131313, 0xffff0303030303030303, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505]),
  (1, 0xff00000000ffffff1313131313131313, [0xff00000000ffffff1313131313131313, 0xffff0303030303030303, 0xff00000000ff00001212121212121212, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505]),
  (1, 0xff0000000000000000000000000000, [0xff0000000000000000000000000000, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00000000ff00001212121212121212]),
  (1, 0xffff00ff00000000c5c5c5c5c5c5c5c5, [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00000000ff00001212121212121212]),
  (1, 0xff000000000000000000000000000000, [0xff000000000000000000000000000000, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00ff000000000505050505050505]),
  (1, 0xffff000000ff0000d2d2d2d2d2d2d2d2, [0xffff000000ff0000d2d2d2d2d2d2d2d2, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xff00ff000000000505050505050505]),
  (1, 0xffff00ff00ff00001717171717171717, [0xffff00ff00ff00001717171717171717, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0])]

set_option maxRecDepth 16000 in
theorem contextGood98 : contextTable98.all (fun t => !(symSearch allowed 1 6 (BitVec.ofNat 128 t.2.1 :: [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c]) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable98
  exact (allContextCons (congrArg Bool.not numericNode99) (allContextCons (congrArg Bool.not numericNode100) (allContextCons (congrArg Bool.not numericNode101) (allContextCons (congrArg Bool.not numericNode102) (allContextCons (congrArg Bool.not numericNode103) (allContextCons (congrArg Bool.not numericNode104) (allContextCons (congrArg Bool.not numericNode105) (allContextCons (congrArg Bool.not numericNode106) (allContextCons (congrArg Bool.not numericNode107) (allContextCons (congrArg Bool.not numericNode108) (allContextCons (congrArg Bool.not numericNode109) (allContextCons (congrArg Bool.not numericNode110) (allContextCons (congrArg Bool.not numericNode111) (allContextCons (congrArg Bool.not numericNode112) (allContextCons (congrArg Bool.not numericNode113) (allContextCons (congrArg Bool.not numericNode114) (allContextCons (congrArg Bool.not numericNode115) (allContextCons (congrArg Bool.not numericNode116) (allContextCons (congrArg Bool.not numericNode117) (allContextCons (congrArg Bool.not numericNode118) (allContextCons (congrArg Bool.not numericNode119) (allContextCons (congrArg Bool.not numericNode120) (allContextCons (congrArg Bool.not numericNode121) rfl)))))))))))))))))))))))

set_option maxRecDepth 16000 in
theorem contextEq98 : cachedBranch 1 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] contextTable98 = symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] := cachedBranch_eq 1 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] contextTable98 contextGood98

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode98 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 3 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by
  rw [← contextEq98]
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode97 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode96 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode95 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode94 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 3 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode93 : symSearch allowed 2 6 [0xffffff000000003535353535353535, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffff000000003535353535353535 [0xffffff000000003535353535353535, 0xffff000000003030303030303030, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode92 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode91 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 2 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode90 : symSearch allowed 2 6 [0xffff0000ffff3333333333333333, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffff0000ffff3333333333333333 [0xffff0000ffff3333333333333333, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode89 : symSearch allowed 2 6 [0xff00000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00000000000000000000 [0xff00000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff00001212121212121212, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode88 : symSearch allowed 2 6 [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffffffff00ff4d4d4d4d4d4d4d4d [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode87 : symSearch allowed 2 6 [0x404040404040404, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0x404040404040404 [0x404040404040404, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode86 : symSearch allowed 2 6 [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xffffffff00ff7c7c7c7c7c7c7c7c [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000003030303030303030, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode85 : symSearch allowed 2 6 [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff00ffffffff4f4f4f4f4f4f4f4f [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode84 : symSearch allowed 2 6 [0xff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c] 1 0xff0000000000000000 [0xff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable83 : List (Nat × Nat × List W) := [
  (1, 0xff0000000000000000, [0xff0000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffffffff4f4f4f4f4f4f4f4f, [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffffffff00ff7c7c7c7c7c7c7c7c, [0xffffffff00ff7c7c7c7c7c7c7c7c, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000003030303030303030, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0x404040404040404, [0x404040404040404, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffffffffff00ff4d4d4d4d4d4d4d4d, [0xffffffffff00ff4d4d4d4d4d4d4d4d, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00000000000000000000, [0xff00000000000000000000, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff00001212121212121212, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffff0000ffff3333333333333333, [0xffff0000ffff3333333333333333, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (2, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffffff000000003535353535353535, [0xffffff000000003535353535353535, 0xffff000000003030303030303030, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (3, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (2, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (2, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (3, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (2, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (2, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xff0000000000000000000000000000, [0xff0000000000000000000000000000, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffff00ff00000000c5c5c5c5c5c5c5c5, [0xffff00ff00000000c5c5c5c5c5c5c5c5, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffff00ff00ff00001717171717171717, [0xffff00ff00ff00001717171717171717, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffff00ff00a5a5a5a5a5a5a5a5, [0xff00ffff00ff00a5a5a5a5a5a5a5a5, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212])]

set_option maxRecDepth 16000 in
theorem contextGood83 : contextTable83.all (fun t => !(symSearch allowed 2 6 (BitVec.ofNat 128 t.2.1 :: [0xff00ffff00ff4c4c4c4c4c4c4c4c]) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable83
  exact (allContextCons (congrArg Bool.not numericNode84) (allContextCons (congrArg Bool.not numericNode85) (allContextCons (congrArg Bool.not numericNode86) (allContextCons (congrArg Bool.not numericNode87) (allContextCons (congrArg Bool.not numericNode88) (allContextCons (congrArg Bool.not numericNode89) (allContextCons (congrArg Bool.not numericNode90) (allContextCons (congrArg Bool.not numericNode91) (allContextCons (congrArg Bool.not numericNode92) (allContextCons (congrArg Bool.not numericNode93) (allContextCons (congrArg Bool.not numericNode94) (allContextCons (congrArg Bool.not numericNode95) (allContextCons (congrArg Bool.not numericNode96) (allContextCons (congrArg Bool.not numericNode97) (allContextCons (congrArg Bool.not numericNode98) (allContextCons (congrArg Bool.not numericNode122) (allContextCons (congrArg Bool.not numericNode123) (allContextCons (congrArg Bool.not numericNode124) (allContextCons (congrArg Bool.not numericNode125) (allContextCons (congrArg Bool.not numericNode126) (allContextCons (congrArg Bool.not numericNode127) (allContextCons (congrArg Bool.not numericNode128) rfl))))))))))))))))))))))

set_option maxRecDepth 16000 in
theorem contextEq83 : cachedBranch 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] contextTable83 = symSearch allowed 3 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] := cachedBranch_eq 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] contextTable83 contextGood83

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode83 : symSearch allowed 3 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c] 3 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by
  rw [← contextEq83]
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode82 : symSearch allowed 3 6 [0xffffffff00003c3c3c3c3c3c3c3c] 1 0xffffffff00003c3c3c3c3c3c3c3c [0xffffffff00003c3c3c3c3c3c3c3c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode81 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode80 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode79 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff00ffffa3a3a3a3a3a3a3a3] 1 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode78 : symSearch allowed 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode77 : symSearch allowed 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode76 : symSearch allowed 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3] 1 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode75 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ff000000000505050505050505, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode74 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode73 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffffa3a3a3a3a3a3a3a3] 1 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode72 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode71 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode70 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffffa3a3a3a3a3a3a3a3] 1 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode69 : symSearch allowed 2 6 [0xffffff00acacacacacacacac, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xffffff00acacacacacacacac [0xffffff00acacacacacacacac, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode68 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xff00ff000000000505050505050505, 0xff00ffffa3a3a3a3a3a3a3a3, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode67 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ffffa3a3a3a3a3a3a3a3, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode66 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xff00ffffa3a3a3a3a3a3a3a3] 1 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xff00ffffa3a3a3a3a3a3a3a3, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode65 : symSearch allowed 2 6 [0xffffffff0f0f0f0f0f0f0f0f, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xffffffff0f0f0f0f0f0f0f0f [0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffffa3a3a3a3a3a3a3a3, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode64 : symSearch allowed 2 6 [0xff0000000000000000, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xff0000000000000000 [0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode63 : symSearch allowed 2 6 [0x202020202020202, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0x202020202020202 [0x202020202020202, 0xff00000000ff00001212121212121212, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode62 : symSearch allowed 2 6 [0xff00ffff00ffffa7a7a7a7a7a7a7a7, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xff00ffff00ffffa7a7a7a7a7a7a7a7 [0xff00ffff00ffffa7a7a7a7a7a7a7a7, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode61 : symSearch allowed 2 6 [0x101010101010101, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0x101010101010101 [0x101010101010101, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode60 : symSearch allowed 2 6 [0xffffff00ffffb3b3b3b3b3b3b3b3, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xffffff00ffffb3b3b3b3b3b3b3b3 [0xffffff00ffffb3b3b3b3b3b3b3b3, 0xffff000000003030303030303030, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode59 : symSearch allowed 2 6 [0xffffffffafafafafafafafaf, 0xff00ffffa3a3a3a3a3a3a3a3] 0 0xffffffffafafafafafafafaf [0xffffffffafafafafafafafaf, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable58 : List (Nat × Nat × List W) := [
  (0, 0xffffffffafafafafafafafaf, [0xffffffffafafafafafafafaf, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xffffff00ffffb3b3b3b3b3b3b3b3, [0xffffff00ffffb3b3b3b3b3b3b3b3, 0xffff000000003030303030303030, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0x101010101010101, [0x101010101010101, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xff00ffff00ffffa7a7a7a7a7a7a7a7, [0xff00ffff00ffffa7a7a7a7a7a7a7a7, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0x202020202020202, [0x202020202020202, 0xff00000000ff00001212121212121212, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848]),
  (0, 0xff0000000000000000, [0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xffffffff0f0f0f0f0f0f0f0f, [0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffffa3a3a3a3a3a3a3a3, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (1, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xff00ffffa3a3a3a3a3a3a3a3, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xff00ffffa3a3a3a3a3a3a3a3, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xff00ff000000000505050505050505, 0xff00ffffa3a3a3a3a3a3a3a3, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xffffff00acacacacacacacac, [0xffffff00acacacacacacacac, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (1, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (1, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ff000000000505050505050505, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (1, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848]),
  (0, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848]),
  (0, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848])]

set_option maxRecDepth 16000 in
theorem contextGood58 : contextTable58.all (fun t => !(symSearch allowed 2 6 (BitVec.ofNat 128 t.2.1 :: [0xff00ffffa3a3a3a3a3a3a3a3]) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable58
  exact (allContextCons (congrArg Bool.not numericNode59) (allContextCons (congrArg Bool.not numericNode60) (allContextCons (congrArg Bool.not numericNode61) (allContextCons (congrArg Bool.not numericNode62) (allContextCons (congrArg Bool.not numericNode63) (allContextCons (congrArg Bool.not numericNode64) (allContextCons (congrArg Bool.not numericNode65) (allContextCons (congrArg Bool.not numericNode66) (allContextCons (congrArg Bool.not numericNode67) (allContextCons (congrArg Bool.not numericNode68) (allContextCons (congrArg Bool.not numericNode69) (allContextCons (congrArg Bool.not numericNode70) (allContextCons (congrArg Bool.not numericNode71) (allContextCons (congrArg Bool.not numericNode72) (allContextCons (congrArg Bool.not numericNode73) (allContextCons (congrArg Bool.not numericNode74) (allContextCons (congrArg Bool.not numericNode75) (allContextCons (congrArg Bool.not numericNode76) (allContextCons (congrArg Bool.not numericNode77) (allContextCons (congrArg Bool.not numericNode78) (allContextCons (congrArg Bool.not numericNode79) (allContextCons (congrArg Bool.not numericNode80) (allContextCons (congrArg Bool.not numericNode81) rfl)))))))))))))))))))))))

set_option maxRecDepth 16000 in
theorem contextEq58 : cachedBranch 2 6 [0xff00ffffa3a3a3a3a3a3a3a3] contextTable58 = symSearch allowed 3 6 [0xff00ffffa3a3a3a3a3a3a3a3] := cachedBranch_eq 2 6 [0xff00ffffa3a3a3a3a3a3a3a3] contextTable58 contextGood58

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode58 : symSearch allowed 3 6 [0xff00ffffa3a3a3a3a3a3a3a3] 1 0xff00ffffa3a3a3a3a3a3a3a3 [0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by
  rw [← contextEq58]
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode57 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode56 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 0 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode55 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000] 1 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode54 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff0000000000000000] 0 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode53 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff0000000000000000] 0 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode52 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xff0000000000000000] 1 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode51 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000] 0 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ff000000000505050505050505, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode50 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000] 0 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffff00000c0c0c0c0c0c0c0c, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode49 : symSearch allowed 2 6 [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000] 1 0xff00ffffff00000d0d0d0d0d0d0d0d [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode48 : symSearch allowed 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff0000000000000000] 0 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff0000000000000000, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode47 : symSearch allowed 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff0000000000000000] 0 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xff0000000000000000, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode46 : symSearch allowed 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff0000000000000000] 1 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff0000000000000000, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode45 : symSearch allowed 2 6 [0xff000000000000000000, 0xff0000000000000000] 0 0xff000000000000000000 [0xff000000000000000000, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode44 : symSearch allowed 2 6 [0xff00000000ffffff1313131313131313, 0xff0000000000000000] 0 0xff00000000ffffff1313131313131313 [0xff00000000ffffff1313131313131313, 0xff00000000ff00001212121212121212, 0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode43 : symSearch allowed 2 6 [0xff00000000ffffff1313131313131313, 0xff0000000000000000] 0 0xff00000000ffffff1313131313131313 [0xff00000000ffffff1313131313131313, 0xffff0303030303030303, 0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode42 : symSearch allowed 2 6 [0xff00000000ffffff1313131313131313, 0xff0000000000000000] 1 0xff00000000ffffff1313131313131313 [0xff00000000ffffff1313131313131313, 0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode41 : symSearch allowed 2 6 [0xffffffff0f0f0f0f0f0f0f0f, 0xff0000000000000000] 0 0xffffffff0f0f0f0f0f0f0f0f [0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode40 : symSearch allowed 2 6 [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0 0xff000000ffff4b4b4b4b4b4b4b4b [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff00000000ff4848484848484848, 0xff0000000000000000, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode39 : symSearch allowed 2 6 [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 0 0xff000000ffff4b4b4b4b4b4b4b4b [0xff000000ffff4b4b4b4b4b4b4b4b, 0xffff0303030303030303, 0xff0000000000000000, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode38 : symSearch allowed 2 6 [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000] 1 0xff000000ffff4b4b4b4b4b4b4b4b [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode37 : symSearch allowed 2 6 [0xff00ffffa0a0a0a0a0a0a0a0, 0xff0000000000000000] 0 0xff00ffffa0a0a0a0a0a0a0a0 [0xff00ffffa0a0a0a0a0a0a0a0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode36 : symSearch allowed 2 6 [0xff00ffffa0a0a0a0a0a0a0a0, 0xff0000000000000000] 0 0xff00ffffa0a0a0a0a0a0a0a0 [0xff00ffffa0a0a0a0a0a0a0a0, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode35 : symSearch allowed 2 6 [0xff00ffffa0a0a0a0a0a0a0a0, 0xff0000000000000000] 1 0xff00ffffa0a0a0a0a0a0a0a0 [0xff00ffffa0a0a0a0a0a0a0a0, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode34 : symSearch allowed 2 6 [0xff00000000ff00ff1212121212121212, 0xff0000000000000000] 0 0xff00000000ff00ff1212121212121212 [0xff00000000ff00ff1212121212121212, 0xff00000000ff00001212121212121212, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode33 : symSearch allowed 2 6 [0xff00000000ff00ff1212121212121212, 0xff0000000000000000] 0 0xff00000000ff00ff1212121212121212 [0xff00000000ff00ff1212121212121212, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode32 : symSearch allowed 2 6 [0xff00000000ff00ff1212121212121212, 0xff0000000000000000] 1 0xff00000000ff00ff1212121212121212 [0xff00000000ff00ff1212121212121212, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode31 : symSearch allowed 2 6 [0xffff00ff0c0c0c0c0c0c0c0c, 0xff0000000000000000] 0 0xffff00ff0c0c0c0c0c0c0c0c [0xffff00ff0c0c0c0c0c0c0c0c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode30 : symSearch allowed 2 6 [0xffff00ff0c0c0c0c0c0c0c0c, 0xff0000000000000000] 0 0xffff00ff0c0c0c0c0c0c0c0c [0xffff00ff0c0c0c0c0c0c0c0c, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode29 : symSearch allowed 2 6 [0xffff00ff0c0c0c0c0c0c0c0c, 0xff0000000000000000] 1 0xffff00ff0c0c0c0c0c0c0c0c [0xffff00ff0c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable28 : List (Nat × Nat × List W) := [
  (1, 0xffff00ff0c0c0c0c0c0c0c0c, [0xffff00ff0c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffff00ff0c0c0c0c0c0c0c0c, [0xffff00ff0c0c0c0c0c0c0c0c, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffff00ff0c0c0c0c0c0c0c0c, [0xffff00ff0c0c0c0c0c0c0c0c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00000000ff00ff1212121212121212, [0xff00000000ff00ff1212121212121212, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00000000ff00ff1212121212121212, [0xff00000000ff00ff1212121212121212, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00000000ff00ff1212121212121212, [0xff00000000ff00ff1212121212121212, 0xff00000000ff00001212121212121212, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffffa0a0a0a0a0a0a0a0, [0xff00ffffa0a0a0a0a0a0a0a0, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xff00ffffa0a0a0a0a0a0a0a0, [0xff00ffffa0a0a0a0a0a0a0a0, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xff00ffffa0a0a0a0a0a0a0a0, [0xff00ffffa0a0a0a0a0a0a0a0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xff000000ffff4b4b4b4b4b4b4b4b, [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff0000000000000000, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff000000ffff4b4b4b4b4b4b4b4b, [0xff000000ffff4b4b4b4b4b4b4b4b, 0xffff0303030303030303, 0xff0000000000000000, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff000000ffff4b4b4b4b4b4b4b4b, [0xff000000ffff4b4b4b4b4b4b4b4b, 0xff00000000ff4848484848484848, 0xff0000000000000000, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffffff0f0f0f0f0f0f0f0f, [0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00000000ffffff1313131313131313, [0xff00000000ffffff1313131313131313, 0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00000000ffffff1313131313131313, [0xff00000000ffffff1313131313131313, 0xffff0303030303030303, 0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00000000ffffff1313131313131313, [0xff00000000ffffff1313131313131313, 0xff00000000ff00001212121212121212, 0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff000000000000000000, [0xff000000000000000000, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff0000000000000000, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (1, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff0000000000000000, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xff0000000000000000, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff0000000000000000, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xffff00000c0c0c0c0c0c0c0c, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffffff00000d0d0d0d0d0d0d0d, [0xff00ffffff00000d0d0d0d0d0d0d0d, 0xff00ff000000000505050505050505, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212]),
  (0, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212])]

set_option maxRecDepth 16000 in
theorem contextGood28 : contextTable28.all (fun t => !(symSearch allowed 2 6 (BitVec.ofNat 128 t.2.1 :: [0xff0000000000000000]) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable28
  exact (allContextCons (congrArg Bool.not numericNode29) (allContextCons (congrArg Bool.not numericNode30) (allContextCons (congrArg Bool.not numericNode31) (allContextCons (congrArg Bool.not numericNode32) (allContextCons (congrArg Bool.not numericNode33) (allContextCons (congrArg Bool.not numericNode34) (allContextCons (congrArg Bool.not numericNode35) (allContextCons (congrArg Bool.not numericNode36) (allContextCons (congrArg Bool.not numericNode37) (allContextCons (congrArg Bool.not numericNode38) (allContextCons (congrArg Bool.not numericNode39) (allContextCons (congrArg Bool.not numericNode40) (allContextCons (congrArg Bool.not numericNode41) (allContextCons (congrArg Bool.not numericNode42) (allContextCons (congrArg Bool.not numericNode43) (allContextCons (congrArg Bool.not numericNode44) (allContextCons (congrArg Bool.not numericNode45) (allContextCons (congrArg Bool.not numericNode46) (allContextCons (congrArg Bool.not numericNode47) (allContextCons (congrArg Bool.not numericNode48) (allContextCons (congrArg Bool.not numericNode49) (allContextCons (congrArg Bool.not numericNode50) (allContextCons (congrArg Bool.not numericNode51) (allContextCons (congrArg Bool.not numericNode52) (allContextCons (congrArg Bool.not numericNode53) (allContextCons (congrArg Bool.not numericNode54) (allContextCons (congrArg Bool.not numericNode55) (allContextCons (congrArg Bool.not numericNode56) (allContextCons (congrArg Bool.not numericNode57) rfl)))))))))))))))))))))))))))))

set_option maxRecDepth 16000 in
theorem contextEq28 : cachedBranch 2 6 [0xff0000000000000000] contextTable28 = symSearch allowed 3 6 [0xff0000000000000000] := cachedBranch_eq 2 6 [0xff0000000000000000] contextTable28 contextGood28

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode28 : symSearch allowed 3 6 [0xff0000000000000000] 1 0xff0000000000000000 [0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by
  rw [← contextEq28]
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode27 : symSearch allowed 3 6 [0x101010101010101] 1 0x101010101010101 [0x101010101010101, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode26 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode25 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode24 : symSearch allowed 2 6 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffffffff0f0f0f0f0f0f0f0f] 1 0xffffff00ff00b0b0b0b0b0b0b0b0 [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode23 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode22 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode21 : symSearch allowed 2 6 [0xff00ffff00ff00003232323232323232, 0xffffffff0f0f0f0f0f0f0f0f] 1 0xff00ffff00ff00003232323232323232 [0xff00ffff00ff00003232323232323232, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode20 : symSearch allowed 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode19 : symSearch allowed 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode18 : symSearch allowed 2 6 [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffffffff0f0f0f0f0f0f0f0f] 1 0xff00ffff00ff4c4c4c4c4c4c4c4c [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode17 : symSearch allowed 2 6 [0xffffffff00003c3c3c3c3c3c3c3c, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xffffffff00003c3c3c3c3c3c3c3c [0xffffffff00003c3c3c3c3c3c3c3c, 0xffff000000003030303030303030, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode16 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xff00ff000000000505050505050505, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode15 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode14 : symSearch allowed 2 6 [0xff00ff0000ffff0707070707070707, 0xffffffff0f0f0f0f0f0f0f0f] 1 0xff00ff0000ffff0707070707070707 [0xff00ff0000ffff0707070707070707, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode13 : symSearch allowed 2 6 [0xffff0000ffff3333333333333333, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xffff0000ffff3333333333333333 [0xffff0000ffff3333333333333333, 0xffff000000003030303030303030, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode12 : symSearch allowed 2 6 [0xffffffffafafafafafafafaf, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xffffffffafafafafafafafaf [0xffffffffafafafafafafafaf, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode11 : symSearch allowed 2 6 [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff00ff000000000000000000 [0xff00ff000000000000000000, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode10 : symSearch allowed 2 6 [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff00ff000000000000000000 [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode9 : symSearch allowed 2 6 [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f] 1 0xff00ff000000000000000000 [0xff00ff000000000000000000, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode8 : symSearch allowed 2 6 [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff00ffffffff4f4f4f4f4f4f4f4f [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode7 : symSearch allowed 2 6 [0xff0808080808080808, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff0808080808080808 [0xff0808080808080808, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode6 : symSearch allowed 2 6 [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff00ffffffffff0f0f0f0f0f0f0f0f [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode5 : symSearch allowed 2 6 [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xff00ffffffffff0f0f0f0f0f0f0f0f [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode4 : symSearch allowed 2 6 [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f] 1 0xff00ffffffffff0f0f0f0f0f0f0f0f [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode3 : symSearch allowed 2 6 [0x505050505050505, 0xffffffff0f0f0f0f0f0f0f0f] 0 0x505050505050505 [0x505050505050505, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode2 : symSearch allowed 2 6 [0xffffffffffff3f3f3f3f3f3f3f3f, 0xffffffff0f0f0f0f0f0f0f0f] 0 0xffffffffffff3f3f3f3f3f3f3f3f [0xffffffffffff3f3f3f3f3f3f3f3f, 0xffff000000003030303030303030, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable1 : List (Nat × Nat × List W) := [
  (0, 0xffffffffffff3f3f3f3f3f3f3f3f, [0xffffffffffff3f3f3f3f3f3f3f3f, 0xffff000000003030303030303030, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0x505050505050505, [0x505050505050505, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffffffffff0f0f0f0f0f0f0f0f, [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffffffffff0f0f0f0f0f0f0f0f, [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffffffffff0f0f0f0f0f0f0f0f, [0xff00ffffffffff0f0f0f0f0f0f0f0f, 0xff00ff000000000505050505050505, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff0808080808080808, [0xff0808080808080808, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffffffff4f4f4f4f4f4f4f4f, [0xff00ffffffff4f4f4f4f4f4f4f4f, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ff000000000000000000, [0xff00ff000000000000000000, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xff00ff000000000000000000, [0xff00ff000000000000000000, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xff00ff000000000000000000, [0xff00ff000000000000000000, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xffffffffafafafafafafafaf, [0xffffffffafafafafafafafaf, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xffff0000ffff3333333333333333, [0xffff0000ffff3333333333333333, 0xffff000000003030303030303030, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xffff0303030303030303, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ff0000ffff0707070707070707, [0xff00ff0000ffff0707070707070707, 0xff00ff000000000505050505050505, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xffffffff00003c3c3c3c3c3c3c3c, [0xffffffff00003c3c3c3c3c3c3c3c, 0xffff000000003030303030303030, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xffff000000003030303030303030, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (0, 0xff00ffff00ff00003232323232323232, [0xff00ffff00ff00003232323232323232, 0xff00000000ff00001212121212121212, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xffff000000003030303030303030, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (0, 0xffffff00ff00b0b0b0b0b0b0b0b0, [0xffffff00ff00b0b0b0b0b0b0b0b0, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848])]

set_option maxRecDepth 16000 in
theorem contextGood1 : contextTable1.all (fun t => !(symSearch allowed 2 6 (BitVec.ofNat 128 t.2.1 :: [0xffffffff0f0f0f0f0f0f0f0f]) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable1
  exact (allContextCons (congrArg Bool.not numericNode2) (allContextCons (congrArg Bool.not numericNode3) (allContextCons (congrArg Bool.not numericNode4) (allContextCons (congrArg Bool.not numericNode5) (allContextCons (congrArg Bool.not numericNode6) (allContextCons (congrArg Bool.not numericNode7) (allContextCons (congrArg Bool.not numericNode8) (allContextCons (congrArg Bool.not numericNode9) (allContextCons (congrArg Bool.not numericNode10) (allContextCons (congrArg Bool.not numericNode11) (allContextCons (congrArg Bool.not numericNode12) (allContextCons (congrArg Bool.not numericNode13) (allContextCons (congrArg Bool.not numericNode14) (allContextCons (congrArg Bool.not numericNode15) (allContextCons (congrArg Bool.not numericNode16) (allContextCons (congrArg Bool.not numericNode17) (allContextCons (congrArg Bool.not numericNode18) (allContextCons (congrArg Bool.not numericNode19) (allContextCons (congrArg Bool.not numericNode20) (allContextCons (congrArg Bool.not numericNode21) (allContextCons (congrArg Bool.not numericNode22) (allContextCons (congrArg Bool.not numericNode23) (allContextCons (congrArg Bool.not numericNode24) (allContextCons (congrArg Bool.not numericNode25) (allContextCons (congrArg Bool.not numericNode26) rfl)))))))))))))))))))))))))

set_option maxRecDepth 16000 in
theorem contextEq1 : cachedBranch 2 6 [0xffffffff0f0f0f0f0f0f0f0f] contextTable1 = symSearch allowed 3 6 [0xffffffff0f0f0f0f0f0f0f0f] := cachedBranch_eq 2 6 [0xffffffff0f0f0f0f0f0f0f0f] contextTable1 contextGood1

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode1 : symSearch allowed 3 6 [0xffffffff0f0f0f0f0f0f0f0f] 1 0xffffffff0f0f0f0f0f0f0f0f [0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0] = false := by
  rw [← contextEq1]
  decide +kernel

set_option maxRecDepth 16000 in
def contextTable0 : List (Nat × Nat × List W) := [
  (1, 0xffffffff0f0f0f0f0f0f0f0f, [0xffffffff0f0f0f0f0f0f0f0f, 0xffff0303030303030303, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0x101010101010101, [0x101010101010101, 0xffff0303030303030303, 0xff00ff000000000505050505050505, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff0000000000000000, [0xff0000000000000000, 0xffff0303030303030303, 0xff00000000ff4848484848484848, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffffa3a3a3a3a3a3a3a3, [0xff00ffffa3a3a3a3a3a3a3a3, 0xffff0303030303030303, 0xff00ff00a0a0a0a0a0a0a0a0, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848]),
  (1, 0xffffffff00003c3c3c3c3c3c3c3c, [0xffffffff00003c3c3c3c3c3c3c3c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff000000003030303030303030, 0xffff0303030303030303, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00000000ff4848484848484848, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (3, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (2, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (2, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0]),
  (1, 0xff00ffff00ff4c4c4c4c4c4c4c4c, [0xff00ffff00ff4c4c4c4c4c4c4c4c, 0xffff00000c0c0c0c0c0c0c0c, 0xff00000000ff4848484848484848, 0xffff0303030303030303, 0xffff000000003030303030303030, 0xffff000000000000c0c0c0c0c0c0c0c0, 0xff00ff000000000505050505050505, 0xff00000000ff00001212121212121212, 0xff00ff00a0a0a0a0a0a0a0a0])]

set_option maxRecDepth 16000 in
theorem contextGood0 : contextTable0.all (fun t => !(symSearch allowed 3 6 (BitVec.ofNat 128 t.2.1 :: []) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable0
  exact (allContextCons (congrArg Bool.not numericNode1) (allContextCons (congrArg Bool.not numericNode27) (allContextCons (congrArg Bool.not numericNode28) (allContextCons (congrArg Bool.not numericNode58) (allContextCons (congrArg Bool.not numericNode82) (allContextCons (congrArg Bool.not numericNode83) (allContextCons (congrArg Bool.not numericNode129) (allContextCons (congrArg Bool.not numericNode158) (allContextCons (congrArg Bool.not numericNode188) rfl)))))))))

set_option maxRecDepth 16000 in
theorem contextEq0 : cachedBranch 3 6 [] contextTable0 = symSearch allowed 4 6 [] := cachedBranch_eq 3 6 [] contextTable0 contextGood0

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericalFront : inputs.sublists.all (fun l => decide (11 < l.length) || (cuts l != -1) ||
    !(symSearch allowed 4 6 [] (11-l.length) 0 l)) = true := by
  rw [← contextEq0]
  decide +kernel

set_option maxRecDepth 16000 in
theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 10)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨gs, hlen, hord, hcan, S, hsub, hl⟩ := canonComplete (get_build C hm hr)
  have hlenk : gs.length ≤ 10 := Nat.le_trans hlen hs
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := chain_card hl
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hcuts : cuts l = -1 := cuts_full (hlS ▸ hl)
  have hsearch := symComplete allowed allowed_of_min 4 6 [] l (11 - l.length) 0 gs hnd hlenk (by omega) hord hcan (hlS ▸ hl)
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp numericalFront l hmem
  have h4 : decide (11 < l.length) = false := by simp; omega
  have h5 : (cuts l != -1) = false := by simp [hcuts]
  rw [h4, h5, hsearch] at hrow
  exact Bool.noConfusion hrow

end PEqualNP.Outside.L_meta_8971

set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_8971 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (13740 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_8971.no_small C hm hs hr
