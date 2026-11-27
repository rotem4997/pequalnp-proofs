import PEqualNP.Defs

/- Adapted from the checked live-circuit normalization and search in L-meta-6349. -/

namespace PEqualNP.Outside.L_meta_8977

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

abbrev W := BitVec 96

def ops (x y : W) : List W := [x &&& y, x ||| y].filter (fun z => z != 0 && z != BitVec.allOnes 96)

def sep (x : W) : BitVec 48 := ((x >>> 48) &&& ~~~x).setWidth 48

def cuts (ws : List W) : BitVec 48 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 48) ++ (0 : BitVec 48)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0xfff111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f00f000111111111111, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]

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

def differs (i : Fin 48) (w : W) : Prop :=
  w.getLsbD (48 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 48) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz.1 with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (48 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (48 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 48, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 48) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 96 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {gs : List (W × W × W)} {ws : List W} (h : liveChain basicOps goal gs ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := chain_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 48)[j]
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
  z == 0 || z == BitVec.allOnes 96 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 96) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 96) :
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
    · exact ⟨BitVec.allOnes 96, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 96 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 96 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 96 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 96 ∨ t ∈ available ∨
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
      · by_cases h1 : x &&& y = BitVec.allOnes 96
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
      · by_cases h1 : x ||| y = BitVec.allOnes 96
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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 96) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 96 ∨ z ∈ av) : represents av (w ++ [z]) := by
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

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (31710 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) := [(0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3), (3, 0), (3, 1), (3, 2)]

def negL : List (Fin 4 × Fin 4) := [(0, 0), (1, 1), (2, 2), (3, 3)]

def samp (k : Fin 96) : Fin 4 × Fin 4 :=
  if k.val < 48 then negL.getD (k.val % 4) (0, 0) else posL.getD (((k.val - 48) / 4) % 12) (0, 0)

theorem input_rows : ∀ k : Fin 96,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 96, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 96) :
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
def orders : Array Nat := #[0xbeeb6caeaa689e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040, 0x8e28605d65542ca248beeb6c4d24501c6144aeaa687de75c0c20409e69646da6583ce34c, 0x8a386079f75c69b658bafb6caaba689a796449345059755438f34c18714428b248083040, 0xbafb6c4934501871448a386059755428b24879f75caaba6808304069b6589a796438f34c, 0xae9aa8bedbac9e59a45d55944d14903cd38c8e18a07dd79c6d96982c92880c10801c5184, 0x5d55948e18a02c9288ae9aa87dd79c0c1080bedbac4d14901c51849e59a43cd38c6d9698, 0x79d7dc8a18e06996d84914d05955d438d3ccbadbecaa9ae89a59e41851c40810c02892c8, 0x4914d0badbec1851c479d7dcaa9ae80810c08a18e05955d42892c86996d838d3cc9a59e4, 0x55759445349034f38ca6baa8b6fbac9679a475f79c8638a065b69804308024b288147184, 0xa6baa875f79c0430805575948638a024b288453490b6fbac14718434f38c9679a465b698, 0x4524d05565d434e3cc75e7dc8628e065a6d8a6aae8b6ebec9669e40420c01461c424a2c8, 0x75e7dca6aae80420c04524d0b6ebec1461c45565d48628e024a2c834e3cc65a6d89669e4, 0xbeeb2d9e6925aeaa298e28216da6197de71d2ca2091c61050c20015d65154d24113ce30d, 0x8e28212ca2095d6515beeb2d1c61054d24119e69256da6193ce30daeaa297de71d0c2001, 0x8a382169b61979f71dbafb2d9a7925aaba2918710528b20908300149341159751538f30d, 0xbafb2d1871054934118a382128b20959751569b6199a792538f30d79f71daaba29083001, 0xae9a2a9e5926bedb2e5d55163cd30e4d14122c920a0c10021c51068e18227dd71e6d961a, 0x5d55162c920a8e1822ae9a2a0c10027dd71e9e59263cd30e6d961abedb2e4d14121c5106, 0x79d71f69961b8a182349141338d30f59551718510708100328920bbadb2faa9a2b9a5927, 0x491413185107badb2f79d71f081003aa9a2b69961b38d30f9a59278a182359551728920b, 0x55751634f30e453412a6ba2a967926b6fb2e04300224b20a14710675f71e86382265b61a, 0xa6ba2a04300275f71e55751624b20a86382234f30e96792665b61a453412b6fb2e147106, 0x45241334e30f55651775e71f65a61b86282304200314610724a20ba6aa2bb6eb2f966927, 0x75e71f042003a6aa2b452413146107b6eb2f34e30f65a61b96692755651786282324a20b, 0x9e49a5becbadae8aa92c82891c41850c00818e08a16d86997dc79d5d45953cc38d4d0491, 0x2c82898e08a15d45959e49a56d86993cc38dbecbad1c41854d0491ae8aa90c00817dc79d, 0x6986d98a08e179c7dd1841c52882c90800c1bacbed9a49e5aa8ae94904d138c3cd5945d5, 0x1841c5bacbed4904d16986d99a49e538c3cd8a08e12882c95945d579c7dd0800c1aa8ae9, 0x9e4966ae8a6abecb6e2c824a0c00421c41465d45563cc34e4d04528e08626d865a7dc75e, 0x2c824a5d45568e08629e49663cc34e6d865aae8a6a0c00427dc75ebecb6e1c41464d0452, 0x69865b79c75f8a086318414708004328824b49045338c34f594557bacb6f9a4967aa8a6b, 0x184147490453bacb6f69865b38c34f9a496779c75f080043aa8a6b8a086328824b594557, 0x34c3ce5545d64504d20400c22482ca1441c6a68aea9649e6b6cbee75c7de6586da8608e2, 0x400c2a68aea75c7de34c3ce9649e66586da5545d62482ca8608e24504d21441c6b6cbee, 0x34c38f45049355459704008314418724828b75c79f65869b8608a3a68aab9649a7b6cbaf, 0x4008375c79fa68aab34c38f65869b9649a7450493144187b6cbaf55459724828b8608a3, 0x20b2891071850030819279a5b2fbada2baa961b6998238a171f79d30f38d517595413491, 0x9279a561b69930f38d20b2898238a1517595107185b2fbad413491003081a2baa971f79d, 0x1061c520a2c90020c161a6d98228e171e7dd9269e5b2ebeda2aae930e3cd4124d15165d5, 0x61a6d99269e530e3cd1061c5b2ebed4124d120a2c98228e15165d50020c171e7dda2aae9, 0x20b24a003042107146927966a2ba6ab2fb6e30f34e51755641345261b65a82386271f75e, 0x92796630f34e61b65a20b24a517556823862003042a2ba6a71f75e107146b2fb6e413452, 0x10614700204320a24b61a65b71e75f82286330e34f412453516557926967b2eb6fa2aa6b, 0x61a65b30e34f926967106147412453b2eb6f00204371e75fa2aa6b20a24b822863516557, 0x10c22092ca1051c630d3ce5155d64114d29259e6a29aeab2dbee6196da71d7de8218e2, 0x30d3ce9259e66196da0010c2a29aea71d7de2092ca5155d68218e21051c64114d2b2dbee, 0x108310518720928b30d38f41149351559761969b71d79f8218a39259a7a29aabb2dbaf, 0x30d38f61969b9259a700108371d79fa29aab105187411493b2dbaf20928b5155978218a3]

set_option maxRecDepth 16000 in
def invNumbers : Array (Fin 48) := #[0, 1, 2, 3, 4, 5, 8, 9, 6, 7, 10, 11, 12, 13, 14, 15, 24, 25, 36, 37, 26, 27, 38, 39, 16, 17, 20, 21, 28, 29, 40, 41, 32, 33, 44, 45, 18, 19, 22, 23, 30, 31, 42, 43, 34, 35, 46, 47]

set_option maxRecDepth 16000 in
def invSym (g : Fin 48) : Fin 48 := invNumbers[g.val]?.getD 0

set_option maxRecDepth 16000 in
def slot (g : Fin 48) (k : Fin 96) : Fin 96 :=
  let off := (orders[g.val]?.getD 0 >>> (6 * (k.val % 48))) % 64 % 48
  ⟨if k.val < 48 then off else 48 + off, by dsimp [off]; split <;> omega⟩

set_option maxRecDepth 16000 in
def aut (g : Fin 48) (x : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun k : Fin 96 => x.getLsbD (slot g k).val)).cast List.length_ofFn

set_option maxRecDepth 16000 in
theorem aut_bit (g : Fin 48) (x : W) (k : Fin 96) :
    (aut g x).getLsbD k.val = x.getLsbD (slot g k).val := by
  simp only [aut, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using k.isLt), List.getElem_ofFn]

set_option maxRecDepth 16000 in
theorem slot_inv : ∀ (g : Fin 48) (k : Fin 96), slot g (slot (invSym g) k) = k := by
  decide +kernel

set_option maxRecDepth 16000 in
theorem aut_left (g : Fin 48) (x : W) : aut (invSym g) (aut g x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := aut_bit (invSym g) (aut g x) ⟨i, hi⟩
  exact hh.trans ((aut_bit g x (slot (invSym g) ⟨i,hi⟩)).trans (by rw [slot_inv]))

set_option maxRecDepth 16000 in
theorem aut_inj (g : Fin 48) : Function.Injective (aut g) := by
  intro x y h
  simpa only [aut_left] using congrArg (aut (invSym g)) h

set_option maxRecDepth 16000 in
theorem aut_goal : ∀ g : Fin 48, aut g goal = goal := by
  decide +kernel

set_option maxRecDepth 16000 in
theorem aut_inputs : ∀ g : Fin 48, inputs.all (fun x => (inputs.elem (aut g x))) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
theorem aut_and (g : Fin 48) (a b : W) : aut g (a &&& b) = aut g a &&& aut g b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa only [BitVec.getLsbD_and] using
    (aut_bit g (a &&& b) ⟨i,hi⟩).trans (by rw [BitVec.getLsbD_and, ← aut_bit, ← aut_bit])

set_option maxRecDepth 16000 in
theorem aut_or (g : Fin 48) (a b : W) : aut g (a ||| b) = aut g a ||| aut g b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa only [BitVec.getLsbD_or] using
    (aut_bit g (a ||| b) ⟨i,hi⟩).trans (by rw [BitVec.getLsbD_or, ← aut_bit, ← aut_bit])

set_option maxRecDepth 16000 in
theorem aut_zero (g : Fin 48) : aut g 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa using aut_bit g 0 ⟨i,hi⟩

set_option maxRecDepth 16000 in
theorem aut_ones (g : Fin 48) : aut g (BitVec.allOnes 96) = BitVec.allOnes 96 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (aut g (BitVec.allOnes 96)).getLsbD i = _ from aut_bit g _ ⟨i,hi⟩, BitVec.getLsbD_eq_getElem (slot g ⟨i,hi⟩).isLt, BitVec.getLsbD_eq_getElem hi, BitVec.getElem_allOnes, BitVec.getElem_allOnes]

set_option maxRecDepth 16000 in
theorem aut_ops (g : Fin 48) {a b z : W} (hz : z ∈ basicOps a b) :
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
def moveGate (g : Fin 48) (v : WGate) : WGate := (aut g v.1, aut g v.2.1, aut g v.2.2)

set_option maxRecDepth 16000 in
theorem move_chain (g : Fin 48) {gs : List WGate} {s : Finset W}
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
    (∀ g : Fin 48, (∀ w ∈ rev, aut g w = w) → v.2.2.toNat ≤ (aut g v.2.2).toNat) ∧
    canonical (v.2.2 :: rev) vs

set_option maxRecDepth 16000 in
theorem canon_of_lex (gs : List WGate) (rev : List W)
    (hm : ∀ g : Fin 48, (∀ w ∈ rev, aut g w = w) →
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
      dispatch extra last (fun e w ts => allowed rev (BitVec.ofNat 96 w) &&
        symSearch m k (BitVec.ofNat 96 w :: rev) e w ts) a b r

variable (allowed_of_min : ∀ (rev : List W) (z : W),
  (∀ i : Fin 48, (∀ w ∈ rev, aut i w = w) → z.toNat ≤ (aut i z).toNat) → allowed rev z = true)

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
      let next (e w : ℕ) (ts : List W) := allowed rev (BitVec.ofNat 96 w) &&
        symSearch allowed m k (BitVec.ofNat 96 w :: rev) e w ts
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
        have hword : BitVec.ofNat 96 z.toNat = z := by simp
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
  g : Fin 48
  fixes : ∀ w ∈ rev, aut g w = w
  lower : (aut g val).toNat < val.toNat

set_option maxRecDepth 16000 in
def makeRejected (rev : List W) (val : W) (g : Fin 48)
    (fixes : rev.all (fun w => aut g w == w) = true)
    (lower : (aut g val).toNat < val.toNat) : RejectedWord :=
  ⟨rev, val, g, fun w hw => beq_iff_eq.mp (List.all_eq_true.mp fixes w hw), lower⟩

set_option maxRecDepth 16000 in
def rejectKey (rev : List W) (z : W) : Nat :=
  rev.foldl (fun h w => (h * 65599 + w.toNat % 1000003) % 4294967291) (z.toNat % 4294967291)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_1 : aut 1 (0x111111111111 : W) = (0x111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_16 : aut 1 (0xf000000000000000 : W) = (0xf000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_18 : aut 1 (0xf00f000000000000 : W) = (0xf00f000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_256 : aut 1 (0xf000000000000000000 : W) = (0xf0000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_512 : aut 1 (0xf0000000000000000000 : W) = (0xf0000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_768 : aut 1 (0xff000000000000000000 : W) = (0xf00f0000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_4096 : aut 1 (0xf000000000000000000000 : W) = (0xf00000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_4371 : aut 1 (0xf00f00f00f111111111111 : W) = (0xffff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_4383 : aut 1 (0xf00f00ffff111111111111 : W) = (0xf00f00ffff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_8192 : aut 1 (0xf0000000000000000000000 : W) = (0xf00000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_8739 : aut 1 (0xf00f000000f333333333333 : W) = (0xfff000333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_8751 : aut 1 (0xf00f0000fff333333333333 : W) = (0xf00ffff000333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_8754 : aut 1 (0xf00f000f00f222222222222 : W) = (0xfff00f222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_8946 : aut 1 (0xf00f0fff00f222222222222 : W) = (0xf00f0fff00f222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_12288 : aut 1 (0xff000000000000000000000 : W) = (0xf00f00000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_13107 : aut 1 (0xff0ff00f00f333333333333 : W) = (0xffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_13119 : aut 1 (0xff0ff00ffff333333333333 : W) = (0xf00fffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_13299 : aut 1 (0xff0fffff00f333333333333 : W) = (0xf00f0ffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_13311 : aut 1 (0xff0ffffffff333333333333 : W) = (0xff0ffffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_16384 : aut 1 (0xf00000000000000000000000 : W) = (0xf00000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_17477 : aut 1 (0xf000000f00f0555555555555 : W) = (0xfff000000555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_17487 : aut 1 (0xf000000f0fff555555555555 : W) = (0xffff00f000555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_17494 : aut 1 (0xf000000ff0ff444444444444 : W) = (0xfff00f00f444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_17652 : aut 1 (0xf00000fff0f0666666666666 : W) = (0xf0fff00000f666666666666 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_20292 : aut 1 (0xf00fff0f00f0444444444444 : W) = (0xf00fff0f00f0444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_21845 : aut 1 (0xf0f00f0ff0f0555555555555 : W) = (0xfff000fff555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_21855 : aut 1 (0xf0f00f0fffff555555555555 : W) = (0xffff00ffff555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_24405 : aut 1 (0xf0ffff0ff0f0555555555555 : W) = (0xf00fff0f0fff555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_26214 : aut 1 (0xff00f00f00ff666666666666 : W) = (0xffffff000666666666666 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_26358 : aut 1 (0xff00f0fff0ff666666666666 : W) = (0xf0ffffff00f666666666666 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_28518 : aut 1 (0xff0fff0f00ff666666666666 : W) = (0xf00ffffff0f0666666666666 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_30719 : aut 1 (0xfff0ffffffff777777777777 : W) = (0xfffffffffff777777777777 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61441 : aut 1 (0xfff000000000999999999999 : W) = (0xf00f00f00999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61455 : aut 1 (0xfff000000fff999999999999 : W) = (0xff0ff0ff00999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61458 : aut 1 (0xfff00000f00f888888888888 : W) = (0xf00f0ff0f888888888888 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61680 : aut 1 (0xfff000fff000aaaaaaaaaaaa : W) = (0xf0ff0f00f0faaaaaaaaaaaa : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61713 : aut 1 (0xfff00f00f000999999999999 : W) = (0xf00f00fff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61727 : aut 1 (0xfff00f00ffff999999999999 : W) = (0xff0ff0ffff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_61986 : aut 1 (0xfff0f000000faaaaaaaaaaaa : W) = (0xf00ffff00aaaaaaaaaaaa : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_62194 : aut 1 (0xfff0f0fff00faaaaaaaaaaaa : W) = (0xf0ff0ffff0faaaaaaaaaaaa : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_62463 : aut 1 (0xfff0ffffffffbbbbbbbbbbbb : W) = (0xfffffffffffbbbbbbbbbbbb : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_62532 : aut 1 (0xfff0000f00f0cccccccccccc : W) = (0xffff00f00cccccccccccc : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_65280 : aut 1 (0xffffff000000cccccccccccc : W) = (0xf00f00ff0ff0cccccccccccc : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct1_65348 : aut 1 (0xffffff0f00f0cccccccccccc : W) = (0xf00fffff0ff0cccccccccccc : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_1 : aut 2 (0x111111111111 : W) = (0x111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_2 : aut 2 (0xf000000000000 : W) = (0xf000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_8 : aut 2 (0xf00000000000000 : W) = (0xf0000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_16 : aut 2 (0xf000000000000000 : W) = (0xf000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_18 : aut 2 (0xf00f000000000000 : W) = (0xf00f000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_31 : aut 2 (0xffff111111111111 : W) = (0xffff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_34 : aut 2 (0xf222222222222 : W) = (0xf222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_128 : aut 2 (0xf00000000000000000 : W) = (0xf0000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_136 : aut 2 (0xf00f00000000000000 : W) = (0xf00f0000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_241 : aut 2 (0xfff000333333333333 : W) = (0xfff000333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_242 : aut 2 (0xfff00f222222222222 : W) = (0xfff00f222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_255 : aut 2 (0xffffff333333333333 : W) = (0xffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_4096 : aut 2 (0xf000000000000000000000 : W) = (0xf000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_4371 : aut 2 (0xf00f00f00f111111111111 : W) = (0xf00f00f00f111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_4383 : aut 2 (0xf00f00ffff111111111111 : W) = (0xf00f00ffff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_4607 : aut 2 (0xf00fffffff333333333333 : W) = (0xf00fffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_8192 : aut 2 (0xf0000000000000000000000 : W) = (0xf0000000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_8751 : aut 2 (0xf00f0000fff333333333333 : W) = (0xf00f0000fff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_8946 : aut 2 (0xf00f0fff00f222222222222 : W) = (0xf00f0fff00f222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_8947 : aut 2 (0xf00f0fff00f333333333333 : W) = (0xf00f0fff00f333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_8959 : aut 2 (0xf00f0ffffff333333333333 : W) = (0xf00f0ffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_13107 : aut 2 (0xff0ff00f00f333333333333 : W) = (0xff0ff00f00f333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_13119 : aut 2 (0xff0ff00ffff333333333333 : W) = (0xff0ff00ffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_13311 : aut 2 (0xff0ffffffff333333333333 : W) = (0xff0ffffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_17478 : aut 2 (0xf000000f00ff444444444444 : W) = (0xf00f00f0f888888888888 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_17487 : aut 2 (0xf000000f0fff555555555555 : W) = (0xf00f00fff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_17492 : aut 2 (0xf000000ff0f0444444444444 : W) = (0xf00f0ff00888888888888 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_17652 : aut 2 (0xf00000fff0f0666666666666 : W) = (0xf00ffff00aaaaaaaaaaaa : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_17663 : aut 2 (0xf00000ffffff777777777777 : W) = (0xf00ffffffbbbbbbbbbbbb : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_21845 : aut 2 (0xf0f00f0ff0f0555555555555 : W) = (0xff0ff0ff00999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_21855 : aut 2 (0xf0f00f0fffff555555555555 : W) = (0xff0ff0ffff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_22015 : aut 2 (0xf0f00fffffff777777777777 : W) = (0xff0fffffffbbbbbbbbbbbb : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_26214 : aut 2 (0xff00f00f00ff666666666666 : W) = (0xf0ff0f00f0faaaaaaaaaaaa : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_26358 : aut 2 (0xff00f0fff0ff666666666666 : W) = (0xf0ff0ffff0faaaaaaaaaaaa : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_26367 : aut 2 (0xff00f0ffffff777777777777 : W) = (0xf0ff0ffffffbbbbbbbbbbbb : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_32768 : aut 2 (0x888888888888 : W) = (0x444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_49152 : aut 2 (0xf00000000000888888888888 : W) = (0xf00000000444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_52428 : aut 2 (0xf00f00ff0ff0cccccccccccc : W) = (0xf00f00ff0ff0cccccccccccc : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_61442 : aut 2 (0xfff00000000f888888888888 : W) = (0xfff00000f444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_61455 : aut 2 (0xfff000000fff999999999999 : W) = (0xfff000fff555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_61456 : aut 2 (0xfff00000f000888888888888 : W) = (0xfff00f000444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_61680 : aut 2 (0xfff000fff000aaaaaaaaaaaa : W) = (0xffffff000666666666666 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_61695 : aut 2 (0xfff000ffffffbbbbbbbbbbbb : W) = (0xfffffffff777777777777 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_61727 : aut 2 (0xfff00f00ffff999999999999 : W) = (0xffff00ffff555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_61951 : aut 2 (0xfff00fffffffbbbbbbbbbbbb : W) = (0xffffffffff777777777777 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_62194 : aut 2 (0xfff0f0fff00faaaaaaaaaaaa : W) = (0xf0ffffff00f666666666666 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_62207 : aut 2 (0xfff0f0ffffffbbbbbbbbbbbb : W) = (0xf0fffffffff777777777777 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_63624 : aut 2 (0xffff00f00f00888888888888 : W) = (0xf00fff0f00f0444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct2_64716 : aut 2 (0xffff00ff0ff0cccccccccccc : W) = (0xf00fffff0ff0cccccccccccc : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_1 : aut 3 (0x111111111111 : W) = (0x111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_18 : aut 3 (0xf00f000000000000 : W) = (0xf00f000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_3841 : aut 3 (0xfff000000555555555555 : W) = (0xf00f00f00999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_3858 : aut 3 (0xfff00f00f444444444444 : W) = (0xf00f0ff0f888888888888 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_4383 : aut 3 (0xf00f00ffff111111111111 : W) = (0xf00f00ffff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_7953 : aut 3 (0xffff00f000555555555555 : W) = (0xf00f00fff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_7967 : aut 3 (0xffff00ffff555555555555 : W) = (0xff0ff0ffff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_8946 : aut 3 (0xf00f0fff00f222222222222 : W) = (0xf00f0fff00f222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_12066 : aut 3 (0xf0fff00000f666666666666 : W) = (0xf00ffff00aaaaaaaaaaaa : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_12274 : aut 3 (0xf0ffffff00f666666666666 : W) = (0xf0ff0ffff0faaaaaaaaaaaa : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_13311 : aut 3 (0xff0ffffffff333333333333 : W) = (0xff0ffffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_39321 : aut 3 (0xff0ff0ff00999999999999 : W) = (0xfff000fff555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_43690 : aut 3 (0xf0ff0f00f0faaaaaaaaaaaa : W) = (0xffffff000666666666666 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct3_48127 : aut 3 (0xfffffffffffbbbbbbbbbbbb : W) = (0xfffffffffff777777777777 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_1 : aut 4 (0x111111111111 : W) = (0x111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_4 : aut 4 (0xf0000000000000 : W) = (0xf000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_8 : aut 4 (0xf00000000000000 : W) = (0xf00000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_15 : aut 4 (0xfff111111111111 : W) = (0xfff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_1024 : aut 4 (0x444444444444 : W) = (0x222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_2048 : aut 4 (0xf00000000000000000000 : W) = (0xf00000000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_3848 : aut 4 (0xfff000f00444444444444 : W) = (0xffff00222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_3855 : aut 4 (0xfff000fff555555555555 : W) = (0xffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_4383 : aut 4 (0xf00f00ffff111111111111 : W) = (0xf00f00ffff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_17484 : aut 4 (0xf000000f0ff0444444444444 : W) = (0xf00f0000f0f222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_17487 : aut 4 (0xf000000f0fff555555555555 : W) = (0xf00f0000fff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_20292 : aut 4 (0xf00fff0f00f0444444444444 : W) = (0xf00f0fff00f222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_34959 : aut 4 (0xf00f00fff999999999999 : W) = (0xf00f00fff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_36744 : aut 4 (0xffff00f00cccccccccccc : W) = (0xf00ffff00aaaaaaaaaaaa : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_36751 : aut 4 (0xffff00fffdddddddddddd : W) = (0xf00ffffffbbbbbbbbbbbb : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_39327 : aut 4 (0xff0ff0ffff999999999999 : W) = (0xff0ff0ffff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_52428 : aut 4 (0xf00f00ff0ff0cccccccccccc : W) = (0xf0ff0f00f0faaaaaaaaaaaa : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct4_52431 : aut 4 (0xf00f00ff0fffdddddddddddd : W) = (0xf0ff0f00fffbbbbbbbbbbbb : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct7_1 : aut 7 (0x111111111111 : W) = (0x111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct7_4383 : aut 7 (0xf00f00ffff111111111111 : W) = (0xf00f00ffff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct7_34953 : aut 7 (0xf00f00f00999999999999 : W) = (0xfff000333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct7_39327 : aut 7 (0xff0ff0ffff999999999999 : W) = (0xf00fffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_4383 : aut 9 (0xf00f00ffff111111111111 : W) = (0xf00f00ffff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct9_4593 : aut 9 (0xf00ffff000333333333333 : W) = (0xf00f00fff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_17 : aut 12 (0xf000111111111111 : W) = (0xf222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_32 : aut 12 (0x222222222222 : W) = (0x111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_64 : aut 12 (0xf0000000000000000 : W) = (0xf0000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_68 : aut 12 (0xf00f0000000000000 : W) = (0xf00f0000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_244 : aut 12 (0xfff0f0222222222222 : W) = (0xf0fff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_255 : aut 12 (0xffffff333333333333 : W) = (0xffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_2184 : aut 12 (0xf00f00f00000000000000 : W) = (0xf00f00f00000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_3908 : aut 12 (0xfff0f00f0444444444444 : W) = (0xfff0f00f0444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_4080 : aut 12 (0xffffff000666666666666 : W) = (0xfff000fff555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_4095 : aut 12 (0xfffffffff777777777777 : W) = (0xfffffffff777777777777 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_8806 : aut 12 (0xf00f00f00ff222222222222 : W) = (0xf00f0ff0f0111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_8946 : aut 12 (0xf00f0fff00f222222222222 : W) = (0xf00f00ffff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_8959 : aut 12 (0xf00f0ffffff333333333333 : W) = (0xf00fffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_17652 : aut 12 (0xf00000fff0f0666666666666 : W) = (0xf000000f0fff555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_20292 : aut 12 (0xf00fff0f00f0444444444444 : W) = (0xf00fff0f00f0444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_20468 : aut 12 (0xf00ffffff0f0666666666666 : W) = (0xf00fff0f0fff555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_35020 : aut 12 (0xf00ff0ff0888888888888 : W) = (0xf00ff0ff0888888888888 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_35064 : aut 12 (0xf00ffff00aaaaaaaaaaaa : W) = (0xf00f00fff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_35071 : aut 12 (0xf00ffffffbbbbbbbbbbbb : W) = (0xf00ffffffbbbbbbbbbbbb : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_61680 : aut 12 (0xfff000fff000aaaaaaaaaaaa : W) = (0xfff000000fff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_63624 : aut 12 (0xffff00f00f00888888888888 : W) = (0xffff00f00f00888888888888 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct12_63736 : aut 12 (0xffff00ffff00aaaaaaaaaaaa : W) = (0xffff00f00fff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct13_2 : aut 13 (0xf000000000000 : W) = (0xf000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct13_4371 : aut 13 (0xf00f00f00f111111111111 : W) = (0xfff00f222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct13_8751 : aut 13 (0xf00f0000fff333333333333 : W) = (0xf00f0000fff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct13_8946 : aut 13 (0xf00f0fff00f222222222222 : W) = (0xf00f00ffff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct13_13107 : aut 13 (0xff0ff00f00f333333333333 : W) = (0xffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct13_13119 : aut 13 (0xff0ff00ffff333333333333 : W) = (0xf00f0ffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct13_20292 : aut 13 (0xf00fff0f00f0444444444444 : W) = (0xf00fff0f00f0444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct13_20294 : aut 13 (0xf00fff0f00ff444444444444 : W) = (0xf00fff0f00ff444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct13_61442 : aut 13 (0xfff00000000f888888888888 : W) = (0xf00f00f0f888888888888 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_2 : aut 15 (0xf000000000000 : W) = (0xf000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct15_3842 : aut 15 (0xfff00000f444444444444 : W) = (0xf00f00f0f888888888888 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_128 : aut 43 (0xf00000000000000000 : W) = (0xf000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_130 : aut 43 (0xf0000f000000000000 : W) = (0xf0000f000000000000 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_8751 : aut 43 (0xf00f0000fff333333333333 : W) = (0xf00ffff00aaaaaaaaaaaa : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_8946 : aut 43 (0xf00f0fff00f222222222222 : W) = (0xf00f0fff00f222222222222 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_17487 : aut 43 (0xf000000f0fff555555555555 : W) = (0xffff00f00cccccccccccc : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_17606 : aut 43 (0xf00000ff00ff444444444444 : W) = (0xffff0000f444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_20292 : aut 43 (0xf00fff0f00f0444444444444 : W) = (0xf00fff0f00f0444444444444 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_32768 : aut 43 (0x888888888888 : W) = (0x111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_34954 : aut 43 (0xf00f00f0f888888888888 : W) = (0xf00fff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_34959 : aut 43 (0xf00f00fff999999999999 : W) = (0xf00f00fff999999999999 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_43690 : aut 43 (0xf0ff0f00f0faaaaaaaaaaaa : W) = (0xffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_43695 : aut 43 (0xf0ff0f00fffbbbbbbbbbbbb : W) = (0xf00ffffffbbbbbbbbbbbb : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_43770 : aut 43 (0xf0ff0ffff0faaaaaaaaaaaa : W) = (0xf00f0ffffff333333333333 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_43775 : aut 43 (0xf0ff0ffffffbbbbbbbbbbbb : W) = (0xf0ff0ffffffbbbbbbbbbbbb : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_52428 : aut 43 (0xf00f00ff0ff0cccccccccccc : W) = (0xfff000fff555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_52431 : aut 43 (0xf00f00ff0fffdddddddddddd : W) = (0xffff00fffdddddddddddd : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_53196 : aut 43 (0xf00fffff0ff0cccccccccccc : W) = (0xf00fff0f0fff555555555555 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_61570 : aut 43 (0xfff000f0000f888888888888 : W) = (0xf00ff0f00f111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_63624 : aut 43 (0xffff00f00f00888888888888 : W) = (0xf00f00ffff111111111111 : W) := by decide +kernel
set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem certAct43_63631 : aut 43 (0xffff00f00fff999999999999 : W) = (0xff0ff0ffff999999999999 : W) := by decide +kernel

set_option maxRecDepth 16000 in
def rejectWord0 : RejectedWord := makeRejected [] 0xf0000000000000 4 (by rfl) (by rw [certAct4_4]; decide)
set_option maxRecDepth 16000 in
def rejectWord1 : RejectedWord := makeRejected [] 0xf00000000000000 2 (by rfl) (by rw [certAct2_8]; decide)
set_option maxRecDepth 16000 in
def rejectWord2 : RejectedWord := makeRejected [] 0xf000000000000000 1 (by rfl) (by rw [certAct1_16]; decide)
set_option maxRecDepth 16000 in
def rejectWord3 : RejectedWord := makeRejected [] 0x222222222222 12 (by rfl) (by rw [certAct12_32]; decide)
set_option maxRecDepth 16000 in
def rejectWord4 : RejectedWord := makeRejected [] 0xf0000000000000000 12 (by rfl) (by rw [certAct12_64]; decide)
set_option maxRecDepth 16000 in
def rejectWord5 : RejectedWord := makeRejected [] 0xf00000000000000000 2 (by rfl) (by rw [certAct2_128]; decide)
set_option maxRecDepth 16000 in
def rejectWord6 : RejectedWord := makeRejected [] 0xf000000000000000000 1 (by rfl) (by rw [certAct1_256]; decide)
set_option maxRecDepth 16000 in
def rejectWord7 : RejectedWord := makeRejected [] 0xf0000000000000000000 1 (by rfl) (by rw [certAct1_512]; decide)
set_option maxRecDepth 16000 in
def rejectWord8 : RejectedWord := makeRejected [] 0x444444444444 4 (by rfl) (by rw [certAct4_1024]; decide)
set_option maxRecDepth 16000 in
def rejectWord9 : RejectedWord := makeRejected [] 0xf00000000000000000000 4 (by rfl) (by rw [certAct4_2048]; decide)
set_option maxRecDepth 16000 in
def rejectWord10 : RejectedWord := makeRejected [] 0xfff000fff555555555555 4 (by rfl) (by rw [certAct4_3855]; decide)
set_option maxRecDepth 16000 in
def rejectWord11 : RejectedWord := makeRejected [] 0xffffff000666666666666 12 (by rfl) (by rw [certAct12_4080]; decide)
set_option maxRecDepth 16000 in
def rejectWord12 : RejectedWord := makeRejected [] 0xf000000000000000000000 1 (by rfl) (by rw [certAct1_4096]; decide)
set_option maxRecDepth 16000 in
def rejectWord13 : RejectedWord := makeRejected [] 0xf00ffff000333333333333 9 (by rfl) (by rw [certAct9_4593]; decide)
set_option maxRecDepth 16000 in
def rejectWord14 : RejectedWord := makeRejected [] 0xffff00f000555555555555 3 (by rfl) (by rw [certAct3_7953]; decide)
set_option maxRecDepth 16000 in
def rejectWord15 : RejectedWord := makeRejected [] 0xf0000000000000000000000 1 (by rfl) (by rw [certAct1_8192]; decide)
set_option maxRecDepth 16000 in
def rejectWord16 : RejectedWord := makeRejected [] 0xf00f0000fff333333333333 1 (by rfl) (by rw [certAct1_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord17 : RejectedWord := makeRejected [] 0xf00f0fff00f222222222222 12 (by rfl) (by rw [certAct12_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord18 : RejectedWord := makeRejected [] 0xf0fff00000f666666666666 3 (by rfl) (by rw [certAct3_12066]; decide)
set_option maxRecDepth 16000 in
def rejectWord19 : RejectedWord := makeRejected [] 0xff0ff00f00f333333333333 1 (by rfl) (by rw [certAct1_13107]; decide)
set_option maxRecDepth 16000 in
def rejectWord20 : RejectedWord := makeRejected [] 0xf00000000000000000000000 1 (by rfl) (by rw [certAct1_16384]; decide)
set_option maxRecDepth 16000 in
def rejectWord21 : RejectedWord := makeRejected [] 0xf000000f0fff555555555555 1 (by rfl) (by rw [certAct1_17487]; decide)
set_option maxRecDepth 16000 in
def rejectWord22 : RejectedWord := makeRejected [] 0xf00000fff0f0666666666666 1 (by rfl) (by rw [certAct1_17652]; decide)
set_option maxRecDepth 16000 in
def rejectWord23 : RejectedWord := makeRejected [] 0xf00fff0f00f0444444444444 4 (by rfl) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord24 : RejectedWord := makeRejected [] 0xf0f00f0ff0f0555555555555 1 (by rfl) (by rw [certAct1_21845]; decide)
set_option maxRecDepth 16000 in
def rejectWord25 : RejectedWord := makeRejected [] 0xff00f00f00ff666666666666 1 (by rfl) (by rw [certAct1_26214]; decide)
set_option maxRecDepth 16000 in
def rejectWord26 : RejectedWord := makeRejected [] 0x888888888888 2 (by rfl) (by rw [certAct2_32768]; decide)
set_option maxRecDepth 16000 in
def rejectWord27 : RejectedWord := makeRejected [] 0xf00ffff00aaaaaaaaaaaa 12 (by rfl) (by rw [certAct12_35064]; decide)
set_option maxRecDepth 16000 in
def rejectWord28 : RejectedWord := makeRejected [] 0xffff00f00cccccccccccc 4 (by rfl) (by rw [certAct4_36744]; decide)
set_option maxRecDepth 16000 in
def rejectWord29 : RejectedWord := makeRejected [] 0xff0ff0ff00999999999999 3 (by rfl) (by rw [certAct3_39321]; decide)
set_option maxRecDepth 16000 in
def rejectWord30 : RejectedWord := makeRejected [] 0xf0ff0f00f0faaaaaaaaaaaa 3 (by rfl) (by rw [certAct3_43690]; decide)
set_option maxRecDepth 16000 in
def rejectWord31 : RejectedWord := makeRejected [] 0xf00f00ff0ff0cccccccccccc 4 (by rfl) (by rw [certAct4_52428]; decide)
set_option maxRecDepth 16000 in
def rejectWord32 : RejectedWord := makeRejected [] 0xfff000000fff999999999999 1 (by rfl) (by rw [certAct1_61455]; decide)
set_option maxRecDepth 16000 in
def rejectWord33 : RejectedWord := makeRejected [] 0xfff000fff000aaaaaaaaaaaa 1 (by rfl) (by rw [certAct1_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord34 : RejectedWord := makeRejected [] 0xfff00f00f000999999999999 1 (by rfl) (by rw [certAct1_61713]; decide)
set_option maxRecDepth 16000 in
def rejectWord35 : RejectedWord := makeRejected [] 0xfff0f000000faaaaaaaaaaaa 1 (by rfl) (by rw [certAct1_61986]; decide)
set_option maxRecDepth 16000 in
def rejectWord36 : RejectedWord := makeRejected [] 0xfff0000f00f0cccccccccccc 1 (by rfl) (by rw [certAct1_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord37 : RejectedWord := makeRejected [] 0xffff00f00f00888888888888 2 (by rfl) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord38 : RejectedWord := makeRejected [] 0xffffff000000cccccccccccc 1 (by rfl) (by rw [certAct1_65280]; decide)
set_option maxRecDepth 16000 in
def rejectWord39 : RejectedWord := makeRejected [0x111111111111] 0xfff000000555555555555 3 (by simp only [List.all_cons, List.all_nil, certAct3_1] <;> decide) (by rw [certAct3_3841]; decide)
set_option maxRecDepth 16000 in
def rejectWord40 : RejectedWord := makeRejected [0x111111111111] 0xf00f000000f333333333333 1 (by simp only [List.all_cons, List.all_nil, certAct1_1] <;> decide) (by rw [certAct1_8739]; decide)
set_option maxRecDepth 16000 in
def rejectWord41 : RejectedWord := makeRejected [0x111111111111] 0xf000000f00f0555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_1] <;> decide) (by rw [certAct1_17477]; decide)
set_option maxRecDepth 16000 in
def rejectWord42 : RejectedWord := makeRejected [0x111111111111] 0xf00fff0f00f0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_1] <;> decide) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord43 : RejectedWord := makeRejected [0x111111111111] 0xf00f00f00999999999999 7 (by simp only [List.all_cons, List.all_nil, certAct7_1] <;> decide) (by rw [certAct7_34953]; decide)
set_option maxRecDepth 16000 in
def rejectWord44 : RejectedWord := makeRejected [0x111111111111] 0xfff000000000999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_1] <;> decide) (by rw [certAct1_61441]; decide)
set_option maxRecDepth 16000 in
def rejectWord45 : RejectedWord := makeRejected [0x111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_1] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord46 : RejectedWord := makeRejected [0x111111111111, 0xf00f00fff999999999999] 0xf00fff0f00f0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_1, certAct4_34959] <;> decide) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord47 : RejectedWord := makeRejected [0xf000000000000] 0xfff00000f444444444444 15 (by simp only [List.all_cons, List.all_nil, certAct15_2] <;> decide) (by rw [certAct15_3842]; decide)
set_option maxRecDepth 16000 in
def rejectWord48 : RejectedWord := makeRejected [0xf000000000000] 0xf00f00f00f111111111111 13 (by simp only [List.all_cons, List.all_nil, certAct13_2] <;> decide) (by rw [certAct13_4371]; decide)
set_option maxRecDepth 16000 in
def rejectWord49 : RejectedWord := makeRejected [0xf000000000000] 0xf00f0fff00f222222222222 13 (by simp only [List.all_cons, List.all_nil, certAct13_2] <;> decide) (by rw [certAct13_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord50 : RejectedWord := makeRejected [0xf000000000000] 0xff0ff00f00f333333333333 13 (by simp only [List.all_cons, List.all_nil, certAct13_2] <;> decide) (by rw [certAct13_13107]; decide)
set_option maxRecDepth 16000 in
def rejectWord51 : RejectedWord := makeRejected [0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord52 : RejectedWord := makeRejected [0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord53 : RejectedWord := makeRejected [0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord54 : RejectedWord := makeRejected [0xf000000000000, 0xf00f00ffff111111111111] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord55 : RejectedWord := makeRejected [0xf000000000000, 0xf00f00ffff111111111111] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord56 : RejectedWord := makeRejected [0xf000000000000, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord57 : RejectedWord := makeRejected [0xf000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_2, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord58 : RejectedWord := makeRejected [0xf000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_2, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord59 : RejectedWord := makeRejected [0xf000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_2, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord60 : RejectedWord := makeRejected [0xf00000000000000, 0xf00f00ffff111111111111, 0xf00f00fff999999999999] 0xfff000f00444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_8, certAct4_4383, certAct4_34959] <;> decide) (by rw [certAct4_3848]; decide)
set_option maxRecDepth 16000 in
def rejectWord61 : RejectedWord := makeRejected [0xf00000000000000, 0xf00f00ffff111111111111, 0xf00f00fff999999999999] 0xf000000f0ff0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_8, certAct4_4383, certAct4_34959] <;> decide) (by rw [certAct4_17484]; decide)
set_option maxRecDepth 16000 in
def rejectWord62 : RejectedWord := makeRejected [0xf00000000000000, 0xf00f00ffff111111111111, 0xf00f00fff999999999999] 0xf00fff0f00f0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_8, certAct4_4383, certAct4_34959] <;> decide) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord63 : RejectedWord := makeRejected [0xfff111111111111, 0xf00f00ffff111111111111, 0xf00f00fff999999999999] 0xf00fff0f00f0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_15, certAct4_4383, certAct4_34959] <;> decide) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord64 : RejectedWord := makeRejected [0xf000000000000000, 0xf00f00ffff111111111111, 0xffffff333333333333] 0xf000000ff0f0444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_16, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_17492]; decide)
set_option maxRecDepth 16000 in
def rejectWord65 : RejectedWord := makeRejected [0xf000000000000000, 0xf00f00ffff111111111111, 0xffffff333333333333] 0xfff00000f000888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_16, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_61456]; decide)
set_option maxRecDepth 16000 in
def rejectWord66 : RejectedWord := makeRejected [0xf000000000000000, 0xf00f00ffff111111111111, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_16, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord67 : RejectedWord := makeRejected [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_18, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_16]; decide)
set_option maxRecDepth 16000 in
def rejectWord68 : RejectedWord := makeRejected [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff00f00f444444444444 3 (by simp only [List.all_cons, List.all_nil, certAct3_18, certAct3_8946, certAct3_4383] <;> decide) (by rw [certAct3_3858]; decide)
set_option maxRecDepth 16000 in
def rejectWord69 : RejectedWord := makeRejected [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf00f00f00f111111111111 1 (by simp only [List.all_cons, List.all_nil, certAct1_18, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_4371]; decide)
set_option maxRecDepth 16000 in
def rejectWord70 : RejectedWord := makeRejected [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf00f000f00f222222222222 1 (by simp only [List.all_cons, List.all_nil, certAct1_18, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_8754]; decide)
set_option maxRecDepth 16000 in
def rejectWord71 : RejectedWord := makeRejected [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff0ff00ffff333333333333 1 (by simp only [List.all_cons, List.all_nil, certAct1_18, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_13119]; decide)
set_option maxRecDepth 16000 in
def rejectWord72 : RejectedWord := makeRejected [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff0fffff00f333333333333 1 (by simp only [List.all_cons, List.all_nil, certAct1_18, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_13299]; decide)
set_option maxRecDepth 16000 in
def rejectWord73 : RejectedWord := makeRejected [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf000000ff0ff444444444444 1 (by simp only [List.all_cons, List.all_nil, certAct1_18, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_17494]; decide)
set_option maxRecDepth 16000 in
def rejectWord74 : RejectedWord := makeRejected [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff00000f00f888888888888 1 (by simp only [List.all_cons, List.all_nil, certAct1_18, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61458]; decide)
set_option maxRecDepth 16000 in
def rejectWord75 : RejectedWord := makeRejected [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_18, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord76 : RejectedWord := makeRejected [0xffff111111111111, 0xf00f00ffff111111111111, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_31, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord77 : RejectedWord := makeRejected [0xf222222222222, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_34, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord78 : RejectedWord := makeRejected [0xf222222222222, 0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_34, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord79 : RejectedWord := makeRejected [0xf00f0000000000000, 0xffffff333333333333] 0xfff0f0222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_68, certAct12_255] <;> decide) (by rw [certAct12_244]; decide)
set_option maxRecDepth 16000 in
def rejectWord80 : RejectedWord := makeRejected [0xf00f0000000000000, 0xffffff333333333333] 0xf00f00f00ff222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_68, certAct12_255] <;> decide) (by rw [certAct12_8806]; decide)
set_option maxRecDepth 16000 in
def rejectWord81 : RejectedWord := makeRejected [0xf00f0000000000000, 0xffffff333333333333] 0xf00f0fff00f222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_68, certAct12_255] <;> decide) (by rw [certAct12_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord82 : RejectedWord := makeRejected [0xf00f0000000000000, 0xffffff333333333333] 0xf00000fff0f0666666666666 12 (by simp only [List.all_cons, List.all_nil, certAct12_68, certAct12_255] <;> decide) (by rw [certAct12_17652]; decide)
set_option maxRecDepth 16000 in
def rejectWord83 : RejectedWord := makeRejected [0xf00f0000000000000, 0xf00fff0f00f0444444444444, 0xffffff333333333333] 0xfff0f0222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_68, certAct12_20292, certAct12_255] <;> decide) (by rw [certAct12_244]; decide)
set_option maxRecDepth 16000 in
def rejectWord84 : RejectedWord := makeRejected [0xf00f0000000000000, 0xf00fff0f00f0444444444444, 0xffffff333333333333] 0xf00f00f00ff222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_68, certAct12_20292, certAct12_255] <;> decide) (by rw [certAct12_8806]; decide)
set_option maxRecDepth 16000 in
def rejectWord85 : RejectedWord := makeRejected [0xf00f0000000000000, 0xf00fff0f00f0444444444444, 0xffffff333333333333] 0xf00f0fff00f222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_68, certAct12_20292, certAct12_255] <;> decide) (by rw [certAct12_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord86 : RejectedWord := makeRejected [0xf0000f000000000000, 0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xf00000ff00ff444444444444 43 (by simp only [List.all_cons, List.all_nil, certAct43_130, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_17606]; decide)
set_option maxRecDepth 16000 in
def rejectWord87 : RejectedWord := makeRejected [0xf0000f000000000000, 0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xf00f00f0f888888888888 43 (by simp only [List.all_cons, List.all_nil, certAct43_130, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_34954]; decide)
set_option maxRecDepth 16000 in
def rejectWord88 : RejectedWord := makeRejected [0xf0000f000000000000, 0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xfff000f0000f888888888888 43 (by simp only [List.all_cons, List.all_nil, certAct43_130, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_61570]; decide)
set_option maxRecDepth 16000 in
def rejectWord89 : RejectedWord := makeRejected [0xf0000f000000000000, 0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xffff00f00f00888888888888 43 (by simp only [List.all_cons, List.all_nil, certAct43_130, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord90 : RejectedWord := makeRejected [0xfff000333333333333, 0x111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_241, certAct2_1] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord91 : RejectedWord := makeRejected [0xfff00f222222222222, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord92 : RejectedWord := makeRejected [0xfff00f222222222222, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord93 : RejectedWord := makeRejected [0xfff00f222222222222, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord94 : RejectedWord := makeRejected [0xfff00f222222222222, 0xf000000000000, 0xf00f00ffff111111111111] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_242, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord95 : RejectedWord := makeRejected [0xfff00f222222222222, 0xf000000000000, 0xf00f00ffff111111111111] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_242, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord96 : RejectedWord := makeRejected [0xfff00f222222222222, 0xf000000000000, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_242, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord97 : RejectedWord := makeRejected [0xfff00f222222222222, 0xf222222222222, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_242, certAct2_34, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord98 : RejectedWord := makeRejected [0xffffff333333333333] 0xf000111111111111 12 (by simp only [List.all_cons, List.all_nil, certAct12_255] <;> decide) (by rw [certAct12_17]; decide)
set_option maxRecDepth 16000 in
def rejectWord99 : RejectedWord := makeRejected [0xffffff333333333333] 0xf00f00000000000000 2 (by simp only [List.all_cons, List.all_nil, certAct2_255] <;> decide) (by rw [certAct2_136]; decide)
set_option maxRecDepth 16000 in
def rejectWord100 : RejectedWord := makeRejected [0xffffff333333333333] 0xffffff000666666666666 12 (by simp only [List.all_cons, List.all_nil, certAct12_255] <;> decide) (by rw [certAct12_4080]; decide)
set_option maxRecDepth 16000 in
def rejectWord101 : RejectedWord := makeRejected [0xffffff333333333333] 0xf00f0fff00f222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_255] <;> decide) (by rw [certAct12_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord102 : RejectedWord := makeRejected [0xffffff333333333333] 0xf00f0ffffff333333333333 12 (by simp only [List.all_cons, List.all_nil, certAct12_255] <;> decide) (by rw [certAct12_8959]; decide)
set_option maxRecDepth 16000 in
def rejectWord103 : RejectedWord := makeRejected [0xffffff333333333333] 0xf000000f0fff555555555555 2 (by simp only [List.all_cons, List.all_nil, certAct2_255] <;> decide) (by rw [certAct2_17487]; decide)
set_option maxRecDepth 16000 in
def rejectWord104 : RejectedWord := makeRejected [0xffffff333333333333] 0xf00000fff0f0666666666666 2 (by simp only [List.all_cons, List.all_nil, certAct2_255] <;> decide) (by rw [certAct2_17652]; decide)
set_option maxRecDepth 16000 in
def rejectWord105 : RejectedWord := makeRejected [0xffffff333333333333] 0xf00000ffffff777777777777 2 (by simp only [List.all_cons, List.all_nil, certAct2_255] <;> decide) (by rw [certAct2_17663]; decide)
set_option maxRecDepth 16000 in
def rejectWord106 : RejectedWord := makeRejected [0xffffff333333333333] 0xf00ffff00aaaaaaaaaaaa 12 (by simp only [List.all_cons, List.all_nil, certAct12_255] <;> decide) (by rw [certAct12_35064]; decide)
set_option maxRecDepth 16000 in
def rejectWord107 : RejectedWord := makeRejected [0xffffff333333333333] 0xfff000000fff999999999999 2 (by simp only [List.all_cons, List.all_nil, certAct2_255] <;> decide) (by rw [certAct2_61455]; decide)
set_option maxRecDepth 16000 in
def rejectWord108 : RejectedWord := makeRejected [0xffffff333333333333] 0xfff000fff000aaaaaaaaaaaa 2 (by simp only [List.all_cons, List.all_nil, certAct2_255] <;> decide) (by rw [certAct2_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord109 : RejectedWord := makeRejected [0xffffff333333333333] 0xfff000ffffffbbbbbbbbbbbb 2 (by simp only [List.all_cons, List.all_nil, certAct2_255] <;> decide) (by rw [certAct2_61695]; decide)
set_option maxRecDepth 16000 in
def rejectWord110 : RejectedWord := makeRejected [0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord111 : RejectedWord := makeRejected [0xffffff333333333333, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_255, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord112 : RejectedWord := makeRejected [0xffffff333333333333, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_255, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord113 : RejectedWord := makeRejected [0xffffff333333333333, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_255, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord114 : RejectedWord := makeRejected [0xf00f00f00000000000000, 0xfffffffff777777777777, 0xffffff333333333333] 0xf00f0fff00f222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_2184, certAct12_4095, certAct12_255] <;> decide) (by rw [certAct12_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord115 : RejectedWord := makeRejected [0xfff0f00f0444444444444, 0xf00f0000000000000, 0xffffff333333333333] 0xf00f0fff00f222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_3908, certAct12_68, certAct12_255] <;> decide) (by rw [certAct12_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord116 : RejectedWord := makeRejected [0xfffffffff777777777777, 0xffffff333333333333] 0xf00f0fff00f222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_4095, certAct12_255] <;> decide) (by rw [certAct12_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord117 : RejectedWord := makeRejected [0xf00f00f00f111111111111, 0xf000000000000, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4371, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord118 : RejectedWord := makeRejected [0xf00f00f00f111111111111, 0xfff00f222222222222, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4371, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord119 : RejectedWord := makeRejected [0xf00f00f00f111111111111, 0xffffff333333333333, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4371, certAct2_255, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord120 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf0000000000000 4 (by simp only [List.all_cons, List.all_nil, certAct4_4383] <;> decide) (by rw [certAct4_4]; decide)
set_option maxRecDepth 16000 in
def rejectWord121 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf00000000000000 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383] <;> decide) (by rw [certAct2_8]; decide)
set_option maxRecDepth 16000 in
def rejectWord122 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_16]; decide)
set_option maxRecDepth 16000 in
def rejectWord123 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_256]; decide)
set_option maxRecDepth 16000 in
def rejectWord124 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf000000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_4096]; decide)
set_option maxRecDepth 16000 in
def rejectWord125 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf00ffff000333333333333 9 (by simp only [List.all_cons, List.all_nil, certAct9_4383] <;> decide) (by rw [certAct9_4593]; decide)
set_option maxRecDepth 16000 in
def rejectWord126 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xffff00f000555555555555 3 (by simp only [List.all_cons, List.all_nil, certAct3_4383] <;> decide) (by rw [certAct3_7953]; decide)
set_option maxRecDepth 16000 in
def rejectWord127 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xffff00ffff555555555555 3 (by simp only [List.all_cons, List.all_nil, certAct3_4383] <;> decide) (by rw [certAct3_7967]; decide)
set_option maxRecDepth 16000 in
def rejectWord128 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf0000000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_8192]; decide)
set_option maxRecDepth 16000 in
def rejectWord129 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf00f0000fff333333333333 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord130 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf0fff00000f666666666666 3 (by simp only [List.all_cons, List.all_nil, certAct3_4383] <;> decide) (by rw [certAct3_12066]; decide)
set_option maxRecDepth 16000 in
def rejectWord131 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xff0ff00f00f333333333333 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_13107]; decide)
set_option maxRecDepth 16000 in
def rejectWord132 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xff0ff00ffff333333333333 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_13119]; decide)
set_option maxRecDepth 16000 in
def rejectWord133 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf00000000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_16384]; decide)
set_option maxRecDepth 16000 in
def rejectWord134 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf000000f0fff555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_17487]; decide)
set_option maxRecDepth 16000 in
def rejectWord135 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf00000fff0f0666666666666 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_17652]; decide)
set_option maxRecDepth 16000 in
def rejectWord136 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf00fff0f00f0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_4383] <;> decide) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord137 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf0f00f0ff0f0555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_21845]; decide)
set_option maxRecDepth 16000 in
def rejectWord138 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf0f00f0fffff555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_21855]; decide)
set_option maxRecDepth 16000 in
def rejectWord139 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xff00f00f00ff666666666666 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_26214]; decide)
set_option maxRecDepth 16000 in
def rejectWord140 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xff0ff0ff00999999999999 3 (by simp only [List.all_cons, List.all_nil, certAct3_4383] <;> decide) (by rw [certAct3_39321]; decide)
set_option maxRecDepth 16000 in
def rejectWord141 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xff0ff0ffff999999999999 7 (by simp only [List.all_cons, List.all_nil, certAct7_4383] <;> decide) (by rw [certAct7_39327]; decide)
set_option maxRecDepth 16000 in
def rejectWord142 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf0ff0f00f0faaaaaaaaaaaa 3 (by simp only [List.all_cons, List.all_nil, certAct3_4383] <;> decide) (by rw [certAct3_43690]; decide)
set_option maxRecDepth 16000 in
def rejectWord143 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xf00f00ff0ff0cccccccccccc 4 (by simp only [List.all_cons, List.all_nil, certAct4_4383] <;> decide) (by rw [certAct4_52428]; decide)
set_option maxRecDepth 16000 in
def rejectWord144 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xfff000000fff999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_61455]; decide)
set_option maxRecDepth 16000 in
def rejectWord145 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xfff000fff000aaaaaaaaaaaa 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord146 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xfff00f00f000999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_61713]; decide)
set_option maxRecDepth 16000 in
def rejectWord147 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xfff00f00ffff999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_61727]; decide)
set_option maxRecDepth 16000 in
def rejectWord148 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xfff0f000000faaaaaaaaaaaa 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_61986]; decide)
set_option maxRecDepth 16000 in
def rejectWord149 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xfff0000f00f0cccccccccccc 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord150 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord151 : RejectedWord := makeRejected [0xf00f00ffff111111111111] 0xffffff000000cccccccccccc 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383] <;> decide) (by rw [certAct1_65280]; decide)
set_option maxRecDepth 16000 in
def rejectWord152 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0x111111111111] 0xf00f000000f333333333333 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383, certAct1_1] <;> decide) (by rw [certAct1_8739]; decide)
set_option maxRecDepth 16000 in
def rejectWord153 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0x111111111111] 0xf000000f00f0555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383, certAct1_1] <;> decide) (by rw [certAct1_17477]; decide)
set_option maxRecDepth 16000 in
def rejectWord154 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0x111111111111] 0xf00fff0f00f0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_4383, certAct4_1] <;> decide) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord155 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0x111111111111] 0xfff000000000999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_4383, certAct1_1] <;> decide) (by rw [certAct1_61441]; decide)
set_option maxRecDepth 16000 in
def rejectWord156 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0x111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_1] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord157 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0x111111111111, 0xf00f00fff999999999999] 0xf00fff0f00f0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_4383, certAct4_1, certAct4_34959] <;> decide) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord158 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord159 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord160 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord161 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xf000000000000, 0xf00f00ffff111111111111] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord162 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xf000000000000, 0xf00f00ffff111111111111] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord163 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xf000000000000, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord164 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xf222222222222, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_34, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord165 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xfff000333333333333, 0x111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_241, certAct2_1] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord166 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xfff00f222222222222, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord167 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xfff00f222222222222, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord168 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xfff00f222222222222, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord169 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xffffff333333333333] 0xf00000fff0f0666666666666 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_17652]; decide)
set_option maxRecDepth 16000 in
def rejectWord170 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xffffff333333333333] 0xf00000ffffff777777777777 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_17663]; decide)
set_option maxRecDepth 16000 in
def rejectWord171 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xffffff333333333333] 0xfff000fff000aaaaaaaaaaaa 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord172 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xffffff333333333333] 0xfff000ffffffbbbbbbbbbbbb 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_61695]; decide)
set_option maxRecDepth 16000 in
def rejectWord173 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord174 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xf00f00fff999999999999] 0xf00fff0f00f0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_4383, certAct4_34959] <;> decide) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord175 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xf00f00fff999999999999] 0xf00f00ff0ff0cccccccccccc 4 (by simp only [List.all_cons, List.all_nil, certAct4_4383, certAct4_34959] <;> decide) (by rw [certAct4_52428]; decide)
set_option maxRecDepth 16000 in
def rejectWord176 : RejectedWord := makeRejected [0xf00f00ffff111111111111, 0xf00f00fff999999999999] 0xf00f00ff0fffdddddddddddd 4 (by simp only [List.all_cons, List.all_nil, certAct4_4383, certAct4_34959] <;> decide) (by rw [certAct4_52431]; decide)
set_option maxRecDepth 16000 in
def rejectWord177 : RejectedWord := makeRejected [0xf00fffffff333333333333, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4607, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord178 : RejectedWord := makeRejected [0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xf00f00000000000000 2 (by simp only [List.all_cons, List.all_nil, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_136]; decide)
set_option maxRecDepth 16000 in
def rejectWord179 : RejectedWord := makeRejected [0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xf000000000000000000000 2 (by simp only [List.all_cons, List.all_nil, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_4096]; decide)
set_option maxRecDepth 16000 in
def rejectWord180 : RejectedWord := makeRejected [0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xf00000fff0f0666666666666 2 (by simp only [List.all_cons, List.all_nil, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_17652]; decide)
set_option maxRecDepth 16000 in
def rejectWord181 : RejectedWord := makeRejected [0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xf0f00f0fffff555555555555 2 (by simp only [List.all_cons, List.all_nil, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_21855]; decide)
set_option maxRecDepth 16000 in
def rejectWord182 : RejectedWord := makeRejected [0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xf0f00fffffff777777777777 2 (by simp only [List.all_cons, List.all_nil, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_22015]; decide)
set_option maxRecDepth 16000 in
def rejectWord183 : RejectedWord := makeRejected [0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xfff000fff000aaaaaaaaaaaa 2 (by simp only [List.all_cons, List.all_nil, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord184 : RejectedWord := makeRejected [0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xfff00f00ffff999999999999 2 (by simp only [List.all_cons, List.all_nil, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_61727]; decide)
set_option maxRecDepth 16000 in
def rejectWord185 : RejectedWord := makeRejected [0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xfff00fffffffbbbbbbbbbbbb 2 (by simp only [List.all_cons, List.all_nil, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_61951]; decide)
set_option maxRecDepth 16000 in
def rejectWord186 : RejectedWord := makeRejected [0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord187 : RejectedWord := makeRejected [0xf00fffffff333333333333, 0xf00f00ffff111111111111, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_4607, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord188 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xf000000000000] 0xf00f0fff00f222222222222 13 (by simp only [List.all_cons, List.all_nil, certAct13_8751, certAct13_2] <;> decide) (by rw [certAct13_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord189 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xf000000000000] 0xff0ff00ffff333333333333 13 (by simp only [List.all_cons, List.all_nil, certAct13_8751, certAct13_2] <;> decide) (by rw [certAct13_13119]; decide)
set_option maxRecDepth 16000 in
def rejectWord190 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord191 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord192 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord193 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xf000000000000, 0xf00f00ffff111111111111] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord194 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xf000000000000, 0xf00f00ffff111111111111] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord195 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xf000000000000, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord196 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xfff00f222222222222, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord197 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xfff00f222222222222, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord198 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xfff00f222222222222, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord199 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xf00f00ffff111111111111, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord200 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xf00f00ffff111111111111, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord201 : RejectedWord := makeRejected [0xf00f0000fff333333333333, 0xf00f00ffff111111111111, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8751, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord202 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0x111111111111] 0xf000000f00f0555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_1] <;> decide) (by rw [certAct1_17477]; decide)
set_option maxRecDepth 16000 in
def rejectWord203 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0x111111111111] 0xfff000000000999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_1] <;> decide) (by rw [certAct1_61441]; decide)
set_option maxRecDepth 16000 in
def rejectWord204 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0x111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_1] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord205 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf000000000000, 0xf00f00ffff111111111111] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord206 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf000000000000, 0xf00f00ffff111111111111] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord207 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf000000000000, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord208 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf222222222222, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_34, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord209 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xfff000333333333333, 0x111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_241, certAct2_1] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord210 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xfff00f222222222222, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord211 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xfff00f222222222222, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord212 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xfff00f222222222222, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord213 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xffffff333333333333, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_255, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord214 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xffffff333333333333, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_255, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord215 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xffffff333333333333, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_255, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord216 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_16]; decide)
set_option maxRecDepth 16000 in
def rejectWord217 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf00000000000000000 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_128]; decide)
set_option maxRecDepth 16000 in
def rejectWord218 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_512]; decide)
set_option maxRecDepth 16000 in
def rejectWord219 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0000000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_8192]; decide)
set_option maxRecDepth 16000 in
def rejectWord220 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0fff00000f666666666666 3 (by simp only [List.all_cons, List.all_nil, certAct3_8946, certAct3_4383] <;> decide) (by rw [certAct3_12066]; decide)
set_option maxRecDepth 16000 in
def rejectWord221 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0ffffff00f666666666666 3 (by simp only [List.all_cons, List.all_nil, certAct3_8946, certAct3_4383] <;> decide) (by rw [certAct3_12274]; decide)
set_option maxRecDepth 16000 in
def rejectWord222 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff0ff00f00f333333333333 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_13107]; decide)
set_option maxRecDepth 16000 in
def rejectWord223 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff0ff00ffff333333333333 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_13119]; decide)
set_option maxRecDepth 16000 in
def rejectWord224 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff0fffff00f333333333333 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_13299]; decide)
set_option maxRecDepth 16000 in
def rejectWord225 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf00000000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_16384]; decide)
set_option maxRecDepth 16000 in
def rejectWord226 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf000000f0fff555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_17487]; decide)
set_option maxRecDepth 16000 in
def rejectWord227 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf00000fff0f0666666666666 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_17652]; decide)
set_option maxRecDepth 16000 in
def rejectWord228 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0f00f0ff0f0555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_21845]; decide)
set_option maxRecDepth 16000 in
def rejectWord229 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0f00f0fffff555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_21855]; decide)
set_option maxRecDepth 16000 in
def rejectWord230 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff00f00f00ff666666666666 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_26214]; decide)
set_option maxRecDepth 16000 in
def rejectWord231 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff00f0fff0ff666666666666 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_26358]; decide)
set_option maxRecDepth 16000 in
def rejectWord232 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0ff0f00f0faaaaaaaaaaaa 3 (by simp only [List.all_cons, List.all_nil, certAct3_8946, certAct3_4383] <;> decide) (by rw [certAct3_43690]; decide)
set_option maxRecDepth 16000 in
def rejectWord233 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff000000fff999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61455]; decide)
set_option maxRecDepth 16000 in
def rejectWord234 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff000fff000aaaaaaaaaaaa 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord235 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff00f00f000999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61713]; decide)
set_option maxRecDepth 16000 in
def rejectWord236 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff00f00ffff999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61727]; decide)
set_option maxRecDepth 16000 in
def rejectWord237 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff0f000000faaaaaaaaaaaa 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61986]; decide)
set_option maxRecDepth 16000 in
def rejectWord238 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff0f0fff00faaaaaaaaaaaa 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_62194]; decide)
set_option maxRecDepth 16000 in
def rejectWord239 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff0000f00f0cccccccccccc 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord240 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord241 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xffffff000000cccccccccccc 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_65280]; decide)
set_option maxRecDepth 16000 in
def rejectWord242 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0x111111111111] 0xf000000f00f0555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383, certAct1_1] <;> decide) (by rw [certAct1_17477]; decide)
set_option maxRecDepth 16000 in
def rejectWord243 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0x111111111111] 0xfff000000000999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_8946, certAct1_4383, certAct1_1] <;> decide) (by rw [certAct1_61441]; decide)
set_option maxRecDepth 16000 in
def rejectWord244 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0x111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4383, certAct2_1] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord245 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord246 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord247 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord248 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xffffff333333333333] 0xf00000ffffff777777777777 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_17663]; decide)
set_option maxRecDepth 16000 in
def rejectWord249 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xffffff333333333333] 0xfff000ffffffbbbbbbbbbbbb 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_61695]; decide)
set_option maxRecDepth 16000 in
def rejectWord250 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord251 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00fffffff333333333333, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4607, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord252 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xf0f00f0fffff555555555555 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_21855]; decide)
set_option maxRecDepth 16000 in
def rejectWord253 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xf0f00fffffff777777777777 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_22015]; decide)
set_option maxRecDepth 16000 in
def rejectWord254 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xfff00f00ffff999999999999 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_61727]; decide)
set_option maxRecDepth 16000 in
def rejectWord255 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xfff00fffffffbbbbbbbbbbbb 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_61951]; decide)
set_option maxRecDepth 16000 in
def rejectWord256 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8946, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord257 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xf000000f0fff555555555555 43 (by simp only [List.all_cons, List.all_nil, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_17487]; decide)
set_option maxRecDepth 16000 in
def rejectWord258 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xf0ff0f00f0faaaaaaaaaaaa 43 (by simp only [List.all_cons, List.all_nil, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_43690]; decide)
set_option maxRecDepth 16000 in
def rejectWord259 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xf0ff0f00fffbbbbbbbbbbbb 43 (by simp only [List.all_cons, List.all_nil, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_43695]; decide)
set_option maxRecDepth 16000 in
def rejectWord260 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xf0ff0ffff0faaaaaaaaaaaa 43 (by simp only [List.all_cons, List.all_nil, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_43770]; decide)
set_option maxRecDepth 16000 in
def rejectWord261 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xf00f00ff0ff0cccccccccccc 43 (by simp only [List.all_cons, List.all_nil, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_52428]; decide)
set_option maxRecDepth 16000 in
def rejectWord262 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xf00f00ff0fffdddddddddddd 43 (by simp only [List.all_cons, List.all_nil, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_52431]; decide)
set_option maxRecDepth 16000 in
def rejectWord263 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xffff00f00f00888888888888 43 (by simp only [List.all_cons, List.all_nil, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord264 : RejectedWord := makeRejected [0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xffff00f00fff999999999999 43 (by simp only [List.all_cons, List.all_nil, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_63631]; decide)
set_option maxRecDepth 16000 in
def rejectWord265 : RejectedWord := makeRejected [0xf00f0fff00f333333333333, 0xf00f0fff00f222222222222, 0x111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8947, certAct2_8946, certAct2_1] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord266 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xffffff333333333333, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_255, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord267 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xffffff333333333333, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_255, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord268 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xffffff333333333333, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_255, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord269 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xf00f00ffff111111111111, 0xffffff333333333333] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_4383, certAct2_255] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord270 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xf00f0000fff333333333333, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_8751, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord271 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xf00f0000fff333333333333, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_8751, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord272 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xf00f0000fff333333333333, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_8751, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord273 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf00f00000000000000 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_136]; decide)
set_option maxRecDepth 16000 in
def rejectWord274 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0000000000000000000000 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_8192]; decide)
set_option maxRecDepth 16000 in
def rejectWord275 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff00f0fff0ff666666666666 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_26358]; decide)
set_option maxRecDepth 16000 in
def rejectWord276 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff00f0ffffff777777777777 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_26367]; decide)
set_option maxRecDepth 16000 in
def rejectWord277 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff0f0fff00faaaaaaaaaaaa 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_62194]; decide)
set_option maxRecDepth 16000 in
def rejectWord278 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff0f0ffffffbbbbbbbbbbbb 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_62207]; decide)
set_option maxRecDepth 16000 in
def rejectWord279 : RejectedWord := makeRejected [0xf00f0ffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_8959, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord280 : RejectedWord := makeRejected [0xff0ff00f00f333333333333, 0xf000000000000, 0xf00f00ffff111111111111] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_13107, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord281 : RejectedWord := makeRejected [0xff0ff00f00f333333333333, 0xf000000000000, 0xf00f00ffff111111111111] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_13107, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord282 : RejectedWord := makeRejected [0xff0ff00f00f333333333333, 0xf000000000000, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_13107, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord283 : RejectedWord := makeRejected [0xff0ff00f00f333333333333, 0xfff00f222222222222, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_13107, certAct2_242, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord284 : RejectedWord := makeRejected [0xff0ff00f00f333333333333, 0xf00f00ffff111111111111, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_13107, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord285 : RejectedWord := makeRejected [0xff0ff00f00f333333333333, 0xf00f00ffff111111111111, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_13107, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord286 : RejectedWord := makeRejected [0xff0ff00f00f333333333333, 0xf00f00ffff111111111111, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_13107, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord287 : RejectedWord := makeRejected [0xff0ff00ffff333333333333, 0xf000000000000, 0xf00f00ffff111111111111] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_13119, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord288 : RejectedWord := makeRejected [0xff0ff00ffff333333333333, 0xf000000000000, 0xf00f00ffff111111111111] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_13119, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord289 : RejectedWord := makeRejected [0xff0ff00ffff333333333333, 0xf000000000000, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_13119, certAct2_2, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord290 : RejectedWord := makeRejected [0xff0ff00ffff333333333333, 0xf00f00ffff111111111111, 0xf000000000000] 0xf000000f00ff444444444444 2 (by simp only [List.all_cons, List.all_nil, certAct2_13119, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_17478]; decide)
set_option maxRecDepth 16000 in
def rejectWord291 : RejectedWord := makeRejected [0xff0ff00ffff333333333333, 0xf00f00ffff111111111111, 0xf000000000000] 0xfff00000000f888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_13119, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord292 : RejectedWord := makeRejected [0xff0ff00ffff333333333333, 0xf00f00ffff111111111111, 0xf000000000000] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_13119, certAct2_4383, certAct2_2] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord293 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_13311, certAct2_4607, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord294 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf00f00000000000000 2 (by simp only [List.all_cons, List.all_nil, certAct2_13311, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_136]; decide)
set_option maxRecDepth 16000 in
def rejectWord295 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_13311, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_768]; decide)
set_option maxRecDepth 16000 in
def rejectWord296 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff000000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_13311, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_12288]; decide)
set_option maxRecDepth 16000 in
def rejectWord297 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0f00f0fffff555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_13311, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_21855]; decide)
set_option maxRecDepth 16000 in
def rejectWord298 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff00f0fff0ff666666666666 1 (by simp only [List.all_cons, List.all_nil, certAct1_13311, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_26358]; decide)
set_option maxRecDepth 16000 in
def rejectWord299 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff0ffffffff777777777777 1 (by simp only [List.all_cons, List.all_nil, certAct1_13311, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_30719]; decide)
set_option maxRecDepth 16000 in
def rejectWord300 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfffffffffffbbbbbbbbbbbb 3 (by simp only [List.all_cons, List.all_nil, certAct3_13311, certAct3_8946, certAct3_4383] <;> decide) (by rw [certAct3_48127]; decide)
set_option maxRecDepth 16000 in
def rejectWord301 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff00f00ffff999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_13311, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61727]; decide)
set_option maxRecDepth 16000 in
def rejectWord302 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff0f0fff00faaaaaaaaaaaa 1 (by simp only [List.all_cons, List.all_nil, certAct1_13311, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_62194]; decide)
set_option maxRecDepth 16000 in
def rejectWord303 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff0ffffffffbbbbbbbbbbbb 1 (by simp only [List.all_cons, List.all_nil, certAct1_13311, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_62463]; decide)
set_option maxRecDepth 16000 in
def rejectWord304 : RejectedWord := makeRejected [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_13311, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord305 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf000000000000] 0xfff00000000f888888888888 13 (by simp only [List.all_cons, List.all_nil, certAct13_20292, certAct13_2] <;> decide) (by rw [certAct13_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord306 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xffffff333333333333] 0xf00ffffff0f0666666666666 12 (by simp only [List.all_cons, List.all_nil, certAct12_20292, certAct12_255] <;> decide) (by rw [certAct12_20468]; decide)
set_option maxRecDepth 16000 in
def rejectWord307 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xffffff333333333333] 0xfff000fff000aaaaaaaaaaaa 12 (by simp only [List.all_cons, List.all_nil, certAct12_20292, certAct12_255] <;> decide) (by rw [certAct12_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord308 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0000fff333333333333, 0xf000000000000] 0xfff00000000f888888888888 13 (by simp only [List.all_cons, List.all_nil, certAct13_20292, certAct13_8751, certAct13_2] <;> decide) (by rw [certAct13_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord309 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0x111111111111] 0xfff000000000999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_1] <;> decide) (by rw [certAct1_61441]; decide)
set_option maxRecDepth 16000 in
def rejectWord310 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_256]; decide)
set_option maxRecDepth 16000 in
def rejectWord311 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_512]; decide)
set_option maxRecDepth 16000 in
def rejectWord312 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf00000000000000000000000 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_16384]; decide)
set_option maxRecDepth 16000 in
def rejectWord313 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0f00f0ff0f0555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_21845]; decide)
set_option maxRecDepth 16000 in
def rejectWord314 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0f00f0fffff555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_21855]; decide)
set_option maxRecDepth 16000 in
def rejectWord315 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0ffff0ff0f0555555555555 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_24405]; decide)
set_option maxRecDepth 16000 in
def rejectWord316 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff00f00f00ff666666666666 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_26214]; decide)
set_option maxRecDepth 16000 in
def rejectWord317 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff00f0fff0ff666666666666 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_26358]; decide)
set_option maxRecDepth 16000 in
def rejectWord318 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff0fff0f00ff666666666666 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_28518]; decide)
set_option maxRecDepth 16000 in
def rejectWord319 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff000000fff999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61455]; decide)
set_option maxRecDepth 16000 in
def rejectWord320 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff000fff000aaaaaaaaaaaa 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61680]; decide)
set_option maxRecDepth 16000 in
def rejectWord321 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff00f00f000999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61713]; decide)
set_option maxRecDepth 16000 in
def rejectWord322 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff00f00ffff999999999999 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61727]; decide)
set_option maxRecDepth 16000 in
def rejectWord323 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff0f000000faaaaaaaaaaaa 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_61986]; decide)
set_option maxRecDepth 16000 in
def rejectWord324 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff0f0fff00faaaaaaaaaaaa 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_62194]; decide)
set_option maxRecDepth 16000 in
def rejectWord325 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xfff0000f00f0cccccccccccc 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_62532]; decide)
set_option maxRecDepth 16000 in
def rejectWord326 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xffffff000000cccccccccccc 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_65280]; decide)
set_option maxRecDepth 16000 in
def rejectWord327 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xffffff0f00f0cccccccccccc 1 (by simp only [List.all_cons, List.all_nil, certAct1_20292, certAct1_8946, certAct1_4383] <;> decide) (by rw [certAct1_65348]; decide)
set_option maxRecDepth 16000 in
def rejectWord328 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xf00fffff0ff0cccccccccccc 43 (by simp only [List.all_cons, List.all_nil, certAct43_20292, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_53196]; decide)
set_option maxRecDepth 16000 in
def rejectWord329 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xffff00f00f00888888888888 43 (by simp only [List.all_cons, List.all_nil, certAct43_20292, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord330 : RejectedWord := makeRejected [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xffff00f00fff999999999999 43 (by simp only [List.all_cons, List.all_nil, certAct43_20292, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_63631]; decide)
set_option maxRecDepth 16000 in
def rejectWord331 : RejectedWord := makeRejected [0xf00fff0f00ff444444444444, 0xf00fff0f00f0444444444444, 0xf000000000000] 0xfff00000000f888888888888 13 (by simp only [List.all_cons, List.all_nil, certAct13_20294, certAct13_20292, certAct13_2] <;> decide) (by rw [certAct13_61442]; decide)
set_option maxRecDepth 16000 in
def rejectWord332 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xf0000000000000 4 (by simp only [List.all_cons, List.all_nil, certAct4_34959] <;> decide) (by rw [certAct4_4]; decide)
set_option maxRecDepth 16000 in
def rejectWord333 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xf00000000000000000 43 (by simp only [List.all_cons, List.all_nil, certAct43_34959] <;> decide) (by rw [certAct43_128]; decide)
set_option maxRecDepth 16000 in
def rejectWord334 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xf00000000000000000000 4 (by simp only [List.all_cons, List.all_nil, certAct4_34959] <;> decide) (by rw [certAct4_2048]; decide)
set_option maxRecDepth 16000 in
def rejectWord335 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xfff000fff555555555555 4 (by simp only [List.all_cons, List.all_nil, certAct4_34959] <;> decide) (by rw [certAct4_3855]; decide)
set_option maxRecDepth 16000 in
def rejectWord336 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xf00f0000fff333333333333 43 (by simp only [List.all_cons, List.all_nil, certAct43_34959] <;> decide) (by rw [certAct43_8751]; decide)
set_option maxRecDepth 16000 in
def rejectWord337 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xf000000f0fff555555555555 4 (by simp only [List.all_cons, List.all_nil, certAct4_34959] <;> decide) (by rw [certAct4_17487]; decide)
set_option maxRecDepth 16000 in
def rejectWord338 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xf00fff0f00f0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_34959] <;> decide) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord339 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0x888888888888 43 (by simp only [List.all_cons, List.all_nil, certAct43_34959] <;> decide) (by rw [certAct43_32768]; decide)
set_option maxRecDepth 16000 in
def rejectWord340 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xffff00f00cccccccccccc 4 (by simp only [List.all_cons, List.all_nil, certAct4_34959] <;> decide) (by rw [certAct4_36744]; decide)
set_option maxRecDepth 16000 in
def rejectWord341 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xffff00fffdddddddddddd 4 (by simp only [List.all_cons, List.all_nil, certAct4_34959] <;> decide) (by rw [certAct4_36751]; decide)
set_option maxRecDepth 16000 in
def rejectWord342 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xf0ff0f00f0faaaaaaaaaaaa 43 (by simp only [List.all_cons, List.all_nil, certAct43_34959] <;> decide) (by rw [certAct43_43690]; decide)
set_option maxRecDepth 16000 in
def rejectWord343 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xf0ff0f00fffbbbbbbbbbbbb 43 (by simp only [List.all_cons, List.all_nil, certAct43_34959] <;> decide) (by rw [certAct43_43695]; decide)
set_option maxRecDepth 16000 in
def rejectWord344 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xf00f00ff0ff0cccccccccccc 4 (by simp only [List.all_cons, List.all_nil, certAct4_34959] <;> decide) (by rw [certAct4_52428]; decide)
set_option maxRecDepth 16000 in
def rejectWord345 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xf00f00ff0fffdddddddddddd 4 (by simp only [List.all_cons, List.all_nil, certAct4_34959] <;> decide) (by rw [certAct4_52431]; decide)
set_option maxRecDepth 16000 in
def rejectWord346 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xffff00f00f00888888888888 43 (by simp only [List.all_cons, List.all_nil, certAct43_34959] <;> decide) (by rw [certAct43_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord347 : RejectedWord := makeRejected [0xf00f00fff999999999999] 0xffff00f00fff999999999999 43 (by simp only [List.all_cons, List.all_nil, certAct43_34959] <;> decide) (by rw [certAct43_63631]; decide)
set_option maxRecDepth 16000 in
def rejectWord348 : RejectedWord := makeRejected [0xf00ff0ff0888888888888, 0xf00f0000000000000, 0xffffff333333333333] 0xf00f0fff00f222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_35020, certAct12_68, certAct12_255] <;> decide) (by rw [certAct12_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord349 : RejectedWord := makeRejected [0xf00ff0ff0888888888888, 0xf00f0000000000000, 0xffffff333333333333] 0xf00000fff0f0666666666666 12 (by simp only [List.all_cons, List.all_nil, certAct12_35020, certAct12_68, certAct12_255] <;> decide) (by rw [certAct12_17652]; decide)
set_option maxRecDepth 16000 in
def rejectWord350 : RejectedWord := makeRejected [0xf00ffffffbbbbbbbbbbbb, 0xffffff333333333333] 0xf00f0fff00f222222222222 12 (by simp only [List.all_cons, List.all_nil, certAct12_35071, certAct12_255] <;> decide) (by rw [certAct12_8946]; decide)
set_option maxRecDepth 16000 in
def rejectWord351 : RejectedWord := makeRejected [0xff0ff0ffff999999999999, 0xf00f00ffff111111111111, 0xf00f00fff999999999999] 0xf00fff0f00f0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_39327, certAct4_4383, certAct4_34959] <;> decide) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord352 : RejectedWord := makeRejected [0xff0ff0ffff999999999999, 0xf00f00fff999999999999] 0xf00fff0f00f0444444444444 4 (by simp only [List.all_cons, List.all_nil, certAct4_39327, certAct4_34959] <;> decide) (by rw [certAct4_20292]; decide)
set_option maxRecDepth 16000 in
def rejectWord353 : RejectedWord := makeRejected [0xf0ff0ffffffbbbbbbbbbbbb, 0xf00f0fff00f222222222222, 0xf00f00fff999999999999] 0xffff00f00f00888888888888 43 (by simp only [List.all_cons, List.all_nil, certAct43_43775, certAct43_8946, certAct43_34959] <;> decide) (by rw [certAct43_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord354 : RejectedWord := makeRejected [0xf00f00ff0ff0cccccccccccc, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0f00f0ff0f0555555555555 2 (by simp only [List.all_cons, List.all_nil, certAct2_52428, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_21845]; decide)
set_option maxRecDepth 16000 in
def rejectWord355 : RejectedWord := makeRejected [0xf00f00ff0ff0cccccccccccc, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf0f00f0fffff555555555555 2 (by simp only [List.all_cons, List.all_nil, certAct2_52428, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_21855]; decide)
set_option maxRecDepth 16000 in
def rejectWord356 : RejectedWord := makeRejected [0xf00f00ff0ff0cccccccccccc, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff00f00f00ff666666666666 2 (by simp only [List.all_cons, List.all_nil, certAct2_52428, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_26214]; decide)
set_option maxRecDepth 16000 in
def rejectWord357 : RejectedWord := makeRejected [0xf00f00ff0ff0cccccccccccc, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xff00f0fff0ff666666666666 2 (by simp only [List.all_cons, List.all_nil, certAct2_52428, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_26358]; decide)
set_option maxRecDepth 16000 in
def rejectWord358 : RejectedWord := makeRejected [0xf00f00ff0ff0cccccccccccc, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xf00000000000888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_52428, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_49152]; decide)
set_option maxRecDepth 16000 in
def rejectWord359 : RejectedWord := makeRejected [0xf00f00ff0ff0cccccccccccc, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xffff00f00f00888888888888 2 (by simp only [List.all_cons, List.all_nil, certAct2_52428, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_63624]; decide)
set_option maxRecDepth 16000 in
def rejectWord360 : RejectedWord := makeRejected [0xf00f00ff0ff0cccccccccccc, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0xffff00ff0ff0cccccccccccc 2 (by simp only [List.all_cons, List.all_nil, certAct2_52428, certAct2_8946, certAct2_4383] <;> decide) (by rw [certAct2_64716]; decide)
set_option maxRecDepth 16000 in
def rejectWord361 : RejectedWord := makeRejected [0xffff00f00f00888888888888, 0xf00fff0f00f0444444444444, 0xffffff333333333333] 0xffff00ffff00aaaaaaaaaaaa 12 (by simp only [List.all_cons, List.all_nil, certAct12_63624, certAct12_20292, certAct12_255] <;> decide) (by rw [certAct12_63736]; decide)

set_option maxRecDepth 16000 in
def rejectLookup (k : Nat) : RejectedWord := (if k < 2003413970 then (if k < 985323081 then (if k < 409708109 then (if k < 147816303 then (if k < 38509890 then (if k < 4552158 then (if k < 96000 then (if k < 6000 then rejectWord4 else rejectWord5) else (if k < 498191 then rejectWord6 else (if k < 1536000 then rejectWord63 else rejectWord7))) else (if k < 17748130 then (if k < 5238765 then rejectWord167 else (if k < 5283522 then rejectWord88 else rejectWord218)) else (if k < 19648621 then rejectWord280 else (if k < 24576000 then rejectWord243 else rejectWord9)))) else (if k < 106605182 then (if k < 78643200 then (if k < 73164877 then rejectWord289 else rejectWord266) else (if k < 87177102 then rejectWord0 else (if k < 94871326 then rejectWord44 else rejectWord231))) else (if k < 125941390 then (if k < 114097020 then rejectWord236 else (if k < 118696506 then rejectWord46 else rejectWord321)) else (if k < 133195160 then rejectWord229 else (if k < 133262897 then rejectWord145 else rejectWord108))))) else (if k < 293408988 then (if k < 210302833 then (if k < 172428451 then (if k < 169061749 then rejectWord89 else rejectWord340) else (if k < 180302411 then rejectWord273 else (if k < 203203948 then rejectWord96 else rejectWord259))) else (if k < 266714758 then (if k < 223242647 then rejectWord288 else (if k < 263340464 then rejectWord127 else rejectWord78)) else (if k < 267401365 then rejectWord166 else (if k < 281811221 then rejectWord86 else rejectWord242)))) else (if k < 393216000 then (if k < 352095354 then (if k < 310014594 then rejectWord237 else (if k < 331851748 then rejectWord319 else rejectWord178)) else (if k < 357695981 then rejectWord95 else (if k < 364494794 then rejectWord21 else rejectWord141))) else (if k < 398920134 then (if k < 393867007 then rejectWord12 else (if k < 397474071 then rejectWord333 else rejectWord305)) else (if k < 402155108 then rejectWord253 else (if k < 409587653 then rejectWord11 else rejectWord154)))))) else (if k < 710256020 then (if k < 522634791 then (if k < 459071240 then (if k < 425773885 then (if k < 419963757 then rejectWord174 else rejectWord182) else (if k < 431729419 then rejectWord28 else (if k < 456715878 then rejectWord278 else rejectWord254))) else (if k < 498549754 then (if k < 464699607 then rejectWord179 else (if k < 472465433 then rejectWord151 else rejectWord287)) else (if k < 509011735 then rejectWord308 else (if k < 518047334 then rejectWord14 else rejectWord195)))) else (if k < 656761062 then (if k < 612086832 then (if k < 572705996 then rejectWord348 else rejectWord3) else (if k < 614257954 then rejectWord293 else (if k < 614612288 then rejectWord94 else rejectWord139))) else (if k < 666462788 then (if k < 659833316 then rejectWord148 else (if k < 660437570 then rejectWord332 else rejectWord120)) else (if k < 689840277 then rejectWord347 else (if k < 697899650 then rejectWord194 else rejectWord322))))) else (if k < 847195980 then (if k < 742953137 then (if k < 710809393 then (if k < 710339154 then rejectWord50 else rejectWord354) else (if k < 724367645 then rejectWord131 else (if k < 740702534 then rejectWord239 else rejectWord74))) else (if k < 823736983 then (if k < 755111217 then rejectWord320 else (if k < 792343118 then rejectWord313 else rejectWord117)) else (if k < 840093965 then rejectWord330 else (if k < 846255444 then rejectWord233 else rejectWord51)))) else (if k < 942452549 then (if k < 915510850 then (if k < 857788074 then rejectWord310 else (if k < 901362056 then rejectWord300 else rejectWord68)) else (if k < 924559123 then rejectWord301 else (if k < 924626860 then rejectWord256 else rejectWord251))) else (if k < 975962554 then (if k < 948327719 then rejectWord48 else (if k < 952002877 then rejectWord228 else rejectWord193)) else (if k < 983710092 then rejectWord183 else (if k < 984314346 then rejectWord336 else rejectWord129))))))) else (if k < 1456911480 then (if k < 1284773368 then (if k < 1145411992 then (if k < 1059512042 then (if k < 1002865134 then (if k < 992925168 then rejectWord67 else rejectWord106) else (if k < 1029794394 then rejectWord73 else (if k < 1057672454 then rejectWord249 else rejectWord130))) else (if k < 1093224147 then (if k < 1067356165 then rejectWord54 else (if k < 1092619893 then rejectWord69 else rejectWord337)) else (if k < 1093291884 then rejectWord134 else (if k < 1120970832 then rejectWord103 else rejectWord359)))) else (if k < 1226094489 then (if k < 1169621528 then (if k < 1165138641 then rejectWord8 else rejectWord329) else (if k < 1198528733 then rejectWord137 else (if k < 1208881452 then rejectWord172 else rejectWord34))) else (if k < 1247060421 then (if k < 1233475025 then rejectWord128 else (if k < 1238687573 then rejectWord17 else rejectWord39)) else (if k < 1258291200 then rejectWord163 else (if k < 1267725989 then rejectWord1 else rejectWord81))))) else (if k < 1358006396 then (if k < 1320025353 then (if k < 1291672899 then (if k < 1290441818 then rejectWord100 else rejectWord248) else (if k < 1299088221 then rejectWord56 else (if k < 1311801396 then rejectWord323 else rejectWord225))) else (if k < 1344592016 then (if k < 1334918766 then rejectWord55 else (if k < 1340433373 then rejectWord230 else rejectWord43)) else (if k < 1348350964 then rejectWord122 else (if k < 1348896511 then rejectWord303 else rejectWord109)))) else (if k < 1414463790 then (if k < 1413739080 then (if k < 1383354095 then rejectWord361 else (if k < 1383782488 then rejectWord304 else rejectWord25)) else (if k < 1413859536 then rejectWord45 else (if k < 1413910417 then rejectWord346 else rejectWord53))) else (if k < 1454580066 then (if k < 1414531527 then rejectWord150 else (if k < 1418853364 then rejectWord110 else rejectWord162)) else (if k < 1454751403 then rejectWord244 else (if k < 1455372513 then rejectWord247 else rejectWord250)))))) else (if k < 1768222188 then (if k < 1583360097 then (if k < 1506775944 then (if k < 1477953888 then (if k < 1459250663 then rejectWord328 else rejectWord277) else (if k < 1495144825 then rejectWord165 else (if k < 1503993986 then rejectWord33 else rejectWord80))) else (if k < 1548562882 then (if k < 1522566366 then rejectWord171 else (if k < 1524216313 then rejectWord90 else rejectWord286)) else (if k < 1577183524 then rejectWord334 else (if k < 1582755843 then rejectWord59 else rejectWord257)))) else (if k < 1696009256 then (if k < 1603263575 then (if k < 1585961292 then rejectWord226 else (if k < 1595090003 then rejectWord126 else rejectWord220)) else (if k < 1626544346 then rejectWord215 else (if k < 1681015964 then rejectWord246 else rejectWord161))) else (if k < 1748976467 then (if k < 1738491731 then rejectWord285 else (if k < 1747229817 then rejectWord189 else rejectWord234)) else (if k < 1759723612 then rejectWord58 else (if k < 1768101732 then rejectWord60 else rejectWord42))))) else (if k < 1874111253 then (if k < 1824010401 then (if k < 1775056518 then (if k < 1768826442 then rejectWord338 else rejectWord136) else (if k < 1806113204 then rejectWord214 else (if k < 1808874956 then rejectWord176 else rejectWord187))) else (if k < 1841252120 then (if k < 1839693714 then rejectWord294 else (if k < 1840314824 then rejectWord49 else rejectWord101)) else (if k < 1854375798 then rejectWord274 else (if k < 1861226690 then rejectWord30 else rejectWord61)))) else (if k < 1913278799 then (if k < 1888706946 then (if k < 1877273625 then rejectWord116 else (if k < 1879048307 then rejectWord252 else rejectWord20)) else (if k < 1912350284 then rejectWord245 else (if k < 1913133648 then rejectWord180 else rejectWord19))) else (if k < 1963907623 then (if k < 1932770954 then rejectWord125 else (if k < 1958171856 then rejectWord235 else rejectWord284)) else (if k < 1978933616 then rejectWord121 else (if k < 1996488709 then rejectWord292 else rejectWord15)))))))) else (if k < 3231925288 then (if k < 2628821536 then (if k < 2290823984 then (if k < 2113621446 then (if k < 2046634814 then (if k < 2037219118 then (if k < 2011139067 then rejectWord123 else rejectWord57) else (if k < 2037919196 then rejectWord213 else (if k < 2044922067 then rejectWord351 else rejectWord264))) else (if k < 2077575584 then (if k < 2071434631 then rejectWord262 else (if k < 2073685334 then rejectWord147 else rejectWord355)) else (if k < 2080937867 then rejectWord343 else (if k < 2092271162 then rejectWord87 else rejectWord84)))) else (if k < 2164500106 then (if k < 2150726559 then (if k < 2118457397 then rejectWord52 else rejectWord314) else (if k < 2151427798 then rejectWord291 else (if k < 2158662868 then rejectWord238 else rejectWord352))) else (if k < 2229979048 then (if k < 2186485385 then rejectWord153 else (if k < 2190342573 then rejectWord345 else rejectWord295)) else (if k < 2276445294 then rejectWord175 else (if k < 2281319402 then rejectWord71 else rejectWord325))))) else (if k < 2424483745 then (if k < 2381833767 then (if k < 2336068597 then (if k < 2333638615 then rejectWord26 else rejectWord22) else (if k < 2348912348 then rejectWord297 else (if k < 2357569360 then rejectWord208 else rejectWord99))) else (if k < 2402024667 then (if k < 2385443328 then rejectWord31 else (if k < 2394993762 then rejectWord276 else rejectWord212)) else (if k < 2405021716 then rejectWord190 else (if k < 2412889159 then rejectWord202 else rejectWord290)))) else (if k < 2464458672 then (if k < 2443163674 then (if k < 2425013417 then rejectWord133 else (if k < 2440591617 then rejectWord155 else rejectWord24)) else (if k < 2458471060 then rejectWord169 else (if k < 2461859182 then rejectWord201 else rejectWord222))) else (if k < 2566786705 then (if k < 2470500658 then rejectWord283 else (if k < 2495679587 then rejectWord261 else rejectWord358)) else (if k < 2567781725 then rejectWord211 else (if k < 2577477815 then rejectWord331 else rejectWord223)))))) else (if k < 2893221413 then (if k < 2707691778 then (if k < 2665535027 then (if k < 2634185524 then (if k < 2630264003 then rejectWord275 else rejectWord200) else (if k < 2655966256 then rejectWord192 else (if k < 2662537978 then rejectWord40 else rejectWord191))) else (if k < 2688054237 then (if k < 2683617547 then rejectWord203 else (if k < 2684768479 then rejectWord227 else rejectWord216)) else (if k < 2701904345 then rejectWord241 else (if k < 2701972082 then rejectWord186 else rejectWord177)))) else (if k < 2804226300 then (if k < 2741885505 then (if k < 2709343734 then rejectWord311 else rejectWord315) else (if k < 2746290463 then rejectWord62 else (if k < 2799822590 then rejectWord102 else rejectWord10))) else (if k < 2852692767 then (if k < 2828949305 then rejectWord27 else (if k < 2843766905 then rejectWord210 else rejectWord35)) else (if k < 2881279016 then rejectWord79 else (if k < 2892426603 then rejectWord119 else rejectWord199))))) else (if k < 3110832613 then (if k < 2999935768 then (if k < 2911184927 then (if k < 2901416399 then rejectWord324 else rejectWord312) else (if k < 2938768227 then rejectWord29 else (if k < 2952790036 then rejectWord307 else rejectWord2))) else (if k < 3020218195 then (if k < 3014887082 then rejectWord158 else (if k < 3020150458 then rejectWord97 else rejectWord144)) else (if k < 3069159137 then rejectWord107 else (if k < 3089487279 then rejectWord114 else rejectWord360)))) else (if k < 3136264561 then (if k < 3134630307 then (if k < 3114778391 then rejectWord302 else (if k < 3129311874 then rejectWord41 else rejectWord23)) else (if k < 3135234561 then rejectWord342 else (if k < 3136196824 then rejectWord142 else rejectWord135))) else (if k < 3187753352 then (if k < 3138695906 then rejectWord104 else (if k < 3148447940 then rejectWord170 else rejectWord111)) else (if k < 3193262764 then rejectWord272 else (if k < 3209545243 then rejectWord72 else rejectWord356))))))) else (if k < 3676316984 then (if k < 3472446898 then (if k < 3359546295 then (if k < 3260449079 then (if k < 3232717735 then (if k < 3232096625 then rejectWord156 else rejectWord160) else (if k < 3254317306 then rejectWord173 else (if k < 3256291516 then rejectWord316 else rejectWord219))) else (if k < 3333400064 then (if k < 3265131917 then rejectWord159 else (if k < 3298678806 then rejectWord47 else rejectWord124)) else (if k < 3348054025 then rejectWord132 else (if k < 3352378672 then rejectWord318 else rejectWord83)))) else (if k < 3434153276 then (if k < 3398713419 then (if k < 3380608797 then rejectWord271 else rejectWord113) else (if k < 3408961251 then rejectWord198 else (if k < 3420392054 then rejectWord112 else rejectWord188))) else (if k < 3447221915 then (if k < 3436229701 then rejectWord146 else (if k < 3442309865 then rejectWord38 else rejectWord138)) else (if k < 3453108813 then rejectWord339 else (if k < 3461248961 then rejectWord221 else rejectWord66))))) else (if k < 3547482909 then (if k < 3498693799 then (if k < 3473171608 then (if k < 3472567354 then rejectWord204 else rejectWord263) else (if k < 3476385570 then rejectWord240 else (if k < 3488665276 then rejectWord349 else rejectWord36))) else (if k < 3517631132 then (if k < 3499076338 then rejectWord185 else (if k < 3500591514 then rejectWord326 else rejectWord327)) else (if k < 3518806661 then rejectWord260 else (if k < 3520316949 then rejectWord76 else rejectWord157)))) else (if k < 3621708895 then (if k < 3589377940 then (if k < 3570506362 then rejectWord37 else (if k < 3571297423 then rejectWord197 else rejectWord265)) else (if k < 3593442442 then rejectWord224 else (if k < 3594046696 then rejectWord344 else rejectWord143))) else (if k < 3649641418 then (if k < 3630305210 then rejectWord270 else (if k < 3638162065 then rejectWord184 else rejectWord306)) else (if k < 3664674832 then rejectWord181 else (if k < 3673009203 then rejectWord70 else rejectWord118)))))) else (if k < 3984636375 then (if k < 3777222551 then (if k < 3692337866 then (if k < 3678031569 then (if k < 3676889307 then rejectWord299 else rejectWord353) else (if k < 3684889178 then rejectWord152 else (if k < 3690243801 then rejectWord85 else rejectWord140))) else (if k < 3731154482 then (if k < 3706893606 then rejectWord105 else (if k < 3716632292 then rejectWord350 else rejectWord341)) else (if k < 3741031421 then rejectWord65 else (if k < 3745729897 then rejectWord75 else rejectWord18)))) else (if k < 3892812307 then (if k < 3832668962 then (if k < 3786285563 then rejectWord115 else (if k < 3809294968 then rejectWord269 else rejectWord207)) else (if k < 3867086181 then rejectWord196 else (if k < 3878759878 then rejectWord296 else rejectWord282))) else (if k < 3940178127 then (if k < 3923012012 then rejectWord32 else (if k < 3934176625 then rejectWord98 else rejectWord268)) else (if k < 3981087911 then rejectWord91 else (if k < 3984032121 then rejectWord206 else rejectWord258))))) else (if k < 4105969568 then (if k < 4026739436 then (if k < 3993317082 then (if k < 3986932689 then rejectWord232 else rejectWord82) else (if k < 4018020223 then rejectWord64 else (if k < 4025054031 then rejectWord357 else rejectWord309))) else (if k < 4058987890 then (if k < 4040188435 then rejectWord279 else (if k < 4050552821 then rejectWord209 else rejectWord281)) else (if k < 4062792286 then rejectWord255 else (if k < 4081645092 then rejectWord317 else rejectWord164)))) else (if k < 4200691438 then (if k < 4171056675 then (if k < 4126257570 then rejectWord267 else (if k < 4127726506 then rejectWord77 else rejectWord168)) else (if k < 4172338984 then rejectWord335 else (if k < 4198933303 then rejectWord93 else rejectWord16))) else (if k < 4243250511 then (if k < 4205167405 then rejectWord92 else (if k < 4212151232 then rejectWord13 else rejectWord149)) else (if k < 4278688226 then rejectWord205 else (if k < 4280403486 then rejectWord217 else rejectWord298)))))))))

set_option maxRecDepth 16000 in
def allowed (rev : List W) (z : W) : Bool :=
  let q := rejectLookup (rejectKey rev z)
  !(q.val == z && q.rev == rev)

set_option maxRecDepth 16000 in
theorem allowed_of_min (rev : List W) (z : W)
    (h : ∀ i : Fin 48, (∀ w ∈ rev, aut i w = w) → z.toNat ≤ (aut i z).toNat) :
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
    (fun e' w ys => allowed rev (BitVec.ofNat 96 w) && cacheNext
      (fun e'' w' zs => symSearch allowed m k (BitVec.ofNat 96 w' :: rev) e'' w' zs) tab e' w ys) a b r)

set_option maxRecDepth 16000 in
theorem cachedBranch_eq (m k : Nat) (rev : List W) (tab : List (Nat × Nat × List W))
    (h : tab.all (fun t => !(symSearch allowed m k (BitVec.ofNat 96 t.2.1 :: rev) t.1 t.2.1 t.2.2)) = true) :
    cachedBranch m k rev tab = symSearch allowed (m+1) k rev := by
  have hc := cacheNext_eq (fun e w zs => symSearch allowed m k (BitVec.ofNat 96 w :: rev) e w zs) tab h
  funext e last ws
  simp only [cachedBranch, symSearch, hc]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode29 : symSearch allowed 3 6 [0xf00f00fff999999999999] 1 0xf00f00fff999999999999 [0xf00f00fff999999999999, 0xfff111111111111, 0xf00f00f00888888888888, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f00f000111111111111, 0xf00f000000f222222222222, 0xf000000f00f0444444444444] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode28 : symSearch allowed 3 6 [0xf000000000000] 1 0xf000000000000 [0xf000000000000, 0xfff111111111111, 0xf00f000000f222222222222, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f00f000111111111111, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode27 : symSearch allowed 3 6 [0xf00f00ffff111111111111] 1 0xf00f00ffff111111111111 [0xf00f00ffff111111111111, 0xfff111111111111, 0xf00f00f000111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode26 : symSearch allowed 3 6 [0xf00f00ffff111111111111] 2 0xf00f00ffff111111111111 [0xf00f00ffff111111111111, 0xf00f00f000111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode25 : symSearch allowed 2 6 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 0 0xf00f0fff00f222222222222 [0xf00f0fff00f222222222222, 0xfff000222222222222, 0xf00f000000f222222222222, 0xf00f00ffff111111111111, 0xfff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode24 : symSearch allowed 2 6 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 1 0xf00f0fff00f222222222222 [0xf00f0fff00f222222222222, 0xf00f000000f222222222222, 0xf00f00ffff111111111111, 0xfff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode23 : symSearch allowed 2 6 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 1 0xf00f0fff00f222222222222 [0xf00f0fff00f222222222222, 0xfff000222222222222, 0xf00f00ffff111111111111, 0xfff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode22 : symSearch allowed 2 6 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 2 0xf00f0fff00f222222222222 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode21 : symSearch allowed 2 6 [0xf000000000000, 0xf00f00ffff111111111111] 0 0xf000000000000 [0xf000000000000, 0xf00f00ffff111111111111, 0xf00f000000f222222222222, 0xfff111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode20 : symSearch allowed 2 6 [0xf00fffffff333333333333, 0xf00f00ffff111111111111] 0 0xf00fffffff333333333333 [0xf00fffffff333333333333, 0xf00f00ffff111111111111, 0xfff000222222222222, 0xfff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable19 : List (Nat × Nat × List W) := [
  (0, 0xf00fffffff333333333333, [0xf00fffffff333333333333, 0xf00f00ffff111111111111, 0xfff000222222222222, 0xfff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (0, 0xf000000000000, [0xf000000000000, 0xf00f00ffff111111111111, 0xf00f000000f222222222222, 0xfff111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (2, 0xf00f0fff00f222222222222, [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (1, 0xf00f0fff00f222222222222, [0xf00f0fff00f222222222222, 0xfff000222222222222, 0xf00f00ffff111111111111, 0xfff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (1, 0xf00f0fff00f222222222222, [0xf00f0fff00f222222222222, 0xf00f000000f222222222222, 0xf00f00ffff111111111111, 0xfff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (0, 0xf00f0fff00f222222222222, [0xf00f0fff00f222222222222, 0xfff000222222222222, 0xf00f000000f222222222222, 0xf00f00ffff111111111111, 0xfff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888])]

set_option maxRecDepth 16000 in
theorem contextGood19 : contextTable19.all (fun t => !(symSearch allowed 2 6 (BitVec.ofNat 96 t.2.1 :: [0xf00f00ffff111111111111]) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable19
  exact (allContextCons (congrArg Bool.not numericNode20) (allContextCons (congrArg Bool.not numericNode21) (allContextCons (congrArg Bool.not numericNode22) (allContextCons (congrArg Bool.not numericNode23) (allContextCons (congrArg Bool.not numericNode24) (allContextCons (congrArg Bool.not numericNode25) rfl))))))

set_option maxRecDepth 16000 in
theorem contextEq19 : cachedBranch 2 6 [0xf00f00ffff111111111111] contextTable19 = symSearch allowed 3 6 [0xf00f00ffff111111111111] := cachedBranch_eq 2 6 [0xf00f00ffff111111111111] contextTable19 contextGood19

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode19 : symSearch allowed 3 6 [0xf00f00ffff111111111111] 2 0xf00f00ffff111111111111 [0xf00f00ffff111111111111, 0xfff111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by
  rw [← contextEq19]
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode18 : symSearch allowed 2 6 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 1 0xf00f0fff00f222222222222 [0xf00f0fff00f222222222222, 0xfff000222222222222, 0xf00f000000f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode17 : symSearch allowed 2 6 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 2 0xf00f0fff00f222222222222 [0xf00f0fff00f222222222222, 0xf00f000000f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode16 : symSearch allowed 2 6 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 2 0xf00f0fff00f222222222222 [0xf00f0fff00f222222222222, 0xfff000222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode15 : symSearch allowed 1 6 [0xf00f00ff0ff0cccccccccccc, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 1 0xf00f00ff0ff0cccccccccccc [0xf00f00ff0ff0cccccccccccc, 0xf000000f00f0444444444444, 0xf00f00f00888888888888, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode14 : symSearch allowed 1 6 [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 1 0xf00fff0f00f0444444444444 [0xf00fff0f00f0444444444444, 0xfff000000444444444444, 0xf000000f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000000888888888888, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode13 : symSearch allowed 1 6 [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 2 0xf00fff0f00f0444444444444 [0xf00fff0f00f0444444444444, 0xf000000f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000000888888888888, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode12 : symSearch allowed 1 6 [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 2 0xf00fff0f00f0444444444444 [0xf00fff0f00f0444444444444, 0xfff000000444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000000888888888888, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode11 : symSearch allowed 1 6 [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 3 0xf00fff0f00f0444444444444 [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000000888888888888, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode10 : symSearch allowed 1 6 [0xf0ff0ffff0faaaaaaaaaaaa, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 1 0xf0ff0ffff0faaaaaaaaaaaa [0xf0ff0ffff0faaaaaaaaaaaa, 0xf00f0fff00f222222222222, 0xf00f00f00888888888888, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode9 : symSearch allowed 1 6 [0xf0000000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 1 0xf0000000000000000 [0xf0000000000000000, 0xf00f0fff00f222222222222, 0xf000000f00f0444444444444, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode8 : symSearch allowed 1 6 [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 1 0xff0ffffffff333333333333 [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode7 : symSearch allowed 1 6 [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 1 0xf00f000000000000 [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable6 : List (Nat × Nat × List W) := [
  (1, 0xf00f000000000000, [0xf00f000000000000, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (1, 0xff0ffffffff333333333333, [0xff0ffffffff333333333333, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (1, 0xf0000000000000000, [0xf0000000000000000, 0xf00f0fff00f222222222222, 0xf000000f00f0444444444444, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f00f00888888888888]),
  (1, 0xf0ff0ffff0faaaaaaaaaaaa, [0xf0ff0ffff0faaaaaaaaaaaa, 0xf00f0fff00f222222222222, 0xf00f00f00888888888888, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444]),
  (3, 0xf00fff0f00f0444444444444, [0xf00fff0f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000000888888888888, 0xf00f00f00888888888888]),
  (2, 0xf00fff0f00f0444444444444, [0xf00fff0f00f0444444444444, 0xfff000000444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000000888888888888, 0xf00f00f00888888888888]),
  (2, 0xf00fff0f00f0444444444444, [0xf00fff0f00f0444444444444, 0xf000000f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000000888888888888, 0xf00f00f00888888888888]),
  (1, 0xf00fff0f00f0444444444444, [0xf00fff0f00f0444444444444, 0xfff000000444444444444, 0xf000000f00f0444444444444, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000000888888888888, 0xf00f00f00888888888888]),
  (1, 0xf00f00ff0ff0cccccccccccc, [0xf00f00ff0ff0cccccccccccc, 0xf000000f00f0444444444444, 0xf00f00f00888888888888, 0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888])]

set_option maxRecDepth 16000 in
theorem contextGood6 : contextTable6.all (fun t => !(symSearch allowed 1 6 (BitVec.ofNat 96 t.2.1 :: [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111]) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable6
  exact (allContextCons (congrArg Bool.not numericNode7) (allContextCons (congrArg Bool.not numericNode8) (allContextCons (congrArg Bool.not numericNode9) (allContextCons (congrArg Bool.not numericNode10) (allContextCons (congrArg Bool.not numericNode11) (allContextCons (congrArg Bool.not numericNode12) (allContextCons (congrArg Bool.not numericNode13) (allContextCons (congrArg Bool.not numericNode14) (allContextCons (congrArg Bool.not numericNode15) rfl)))))))))

set_option maxRecDepth 16000 in
theorem contextEq6 : cachedBranch 1 6 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] contextTable6 = symSearch allowed 2 6 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] := cachedBranch_eq 1 6 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] contextTable6 contextGood6

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode6 : symSearch allowed 2 6 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111] 3 0xf00f0fff00f222222222222 [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by
  rw [← contextEq6]
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode5 : symSearch allowed 2 6 [0xf000000000000, 0xf00f00ffff111111111111] 1 0xf000000000000 [0xf000000000000, 0xf00f00ffff111111111111, 0xf00f000000f222222222222, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode4 : symSearch allowed 2 6 [0xf00fffffff333333333333, 0xf00f00ffff111111111111] 1 0xf00fffffff333333333333 [0xf00fffffff333333333333, 0xf00f00ffff111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable3 : List (Nat × Nat × List W) := [
  (1, 0xf00fffffff333333333333, [0xf00fffffff333333333333, 0xf00f00ffff111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (1, 0xf000000000000, [0xf000000000000, 0xf00f00ffff111111111111, 0xf00f000000f222222222222, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (3, 0xf00f0fff00f222222222222, [0xf00f0fff00f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (2, 0xf00f0fff00f222222222222, [0xf00f0fff00f222222222222, 0xfff000222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (2, 0xf00f0fff00f222222222222, [0xf00f0fff00f222222222222, 0xf00f000000f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (1, 0xf00f0fff00f222222222222, [0xf00f0fff00f222222222222, 0xfff000222222222222, 0xf00f000000f222222222222, 0xf00f00ffff111111111111, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf000000f00f0444444444444, 0xf00f00f00888888888888])]

set_option maxRecDepth 16000 in
theorem contextGood3 : contextTable3.all (fun t => !(symSearch allowed 2 6 (BitVec.ofNat 96 t.2.1 :: [0xf00f00ffff111111111111]) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable3
  exact (allContextCons (congrArg Bool.not numericNode4) (allContextCons (congrArg Bool.not numericNode5) (allContextCons (congrArg Bool.not numericNode6) (allContextCons (congrArg Bool.not numericNode16) (allContextCons (congrArg Bool.not numericNode17) (allContextCons (congrArg Bool.not numericNode18) rfl))))))

set_option maxRecDepth 16000 in
theorem contextEq3 : cachedBranch 2 6 [0xf00f00ffff111111111111] contextTable3 = symSearch allowed 3 6 [0xf00f00ffff111111111111] := cachedBranch_eq 2 6 [0xf00f00ffff111111111111] contextTable3 contextGood3

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode3 : symSearch allowed 3 6 [0xf00f00ffff111111111111] 3 0xf00f00ffff111111111111 [0xf00f00ffff111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by
  rw [← contextEq3]
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode2 : symSearch allowed 3 6 [0x111111111111] 1 0x111111111111 [0x111111111111, 0xfff111111111111, 0xf00f00f000111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem numericNode1 : symSearch allowed 3 6 [0xffffff333333333333] 1 0xffffff333333333333 [0xffffff333333333333, 0xfff111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f00f000111111111111, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888] = false := by decide +kernel

set_option maxRecDepth 16000 in
def contextTable0 : List (Nat × Nat × List W) := [
  (1, 0xffffff333333333333, [0xffffff333333333333, 0xfff111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f00f000111111111111, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (1, 0x111111111111, [0x111111111111, 0xfff111111111111, 0xf00f00f000111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (3, 0xf00f00ffff111111111111, [0xf00f00ffff111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (2, 0xf00f00ffff111111111111, [0xf00f00ffff111111111111, 0xfff111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (2, 0xf00f00ffff111111111111, [0xf00f00ffff111111111111, 0xf00f00f000111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (1, 0xf00f00ffff111111111111, [0xf00f00ffff111111111111, 0xfff111111111111, 0xf00f00f000111111111111, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f000000f222222222222, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (1, 0xf000000000000, [0xf000000000000, 0xfff111111111111, 0xf00f000000f222222222222, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f00f000111111111111, 0xf000000f00f0444444444444, 0xf00f00f00888888888888]),
  (1, 0xf00f00fff999999999999, [0xf00f00fff999999999999, 0xfff111111111111, 0xf00f00f00888888888888, 0xfff000222222222222, 0xfff000000444444444444, 0xfff000000000888888888888, 0xf00f00f000111111111111, 0xf00f000000f222222222222, 0xf000000f00f0444444444444])]

set_option maxRecDepth 16000 in
theorem contextGood0 : contextTable0.all (fun t => !(symSearch allowed 3 6 (BitVec.ofNat 96 t.2.1 :: []) t.1 t.2.1 t.2.2)) = true := by
  unfold contextTable0
  exact (allContextCons (congrArg Bool.not numericNode1) (allContextCons (congrArg Bool.not numericNode2) (allContextCons (congrArg Bool.not numericNode3) (allContextCons (congrArg Bool.not numericNode19) (allContextCons (congrArg Bool.not numericNode26) (allContextCons (congrArg Bool.not numericNode27) (allContextCons (congrArg Bool.not numericNode28) (allContextCons (congrArg Bool.not numericNode29) rfl))))))))

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

end PEqualNP.Outside.L_meta_8977

set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_8977 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (31710 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_8977.no_small C hm hs hr
