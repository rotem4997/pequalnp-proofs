import PEqualNP.Defs

/- Adapted from the checked live-circuit normalization and search in L-meta-6349. -/

namespace PEqualNP.Outside.L_meta_8973

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

def invCount (key : α → ℕ) : List (α × α × α) → ℕ
  | [] => 0
  | g :: gs => (gs.filter (fun h => decide (key h.2.2 < key g.2.2))).length + invCount key gs

theorem invCount_swap_lt (key : α → ℕ) (pre suf : List (α × α × α)) (g₁ g₂ : α × α × α)
    (hlt : key g₂.2.2 < key g₁.2.2) :
    invCount key (pre ++ g₂ :: g₁ :: suf) < invCount key (pre ++ g₁ :: g₂ :: suf) := by
  induction pre with
  | nil =>
    simp only [List.nil_append, invCount, List.filter_cons]
    have h1 : decide (key g₂.2.2 < key g₁.2.2) = true := decide_eq_true hlt
    have h2 : decide (key g₁.2.2 < key g₂.2.2) = false := decide_eq_false (by omega)
    simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, List.length_cons]
    omega
  | cons x xs ih =>
    simp only [List.cons_append, invCount]
    have hperm : (xs ++ g₂ :: g₁ :: suf).Perm (xs ++ g₁ :: g₂ :: suf) :=
      List.Perm.append_left xs (List.Perm.swap g₁ g₂ suf)
    have hlen : ((xs ++ g₂ :: g₁ :: suf).filter (fun h => decide (key h.2.2 < key x.2.2))).length =
                ((xs ++ g₁ :: g₂ :: suf).filter (fun h => decide (key h.2.2 < key x.2.2))).length :=
      (hperm.filter _).length_eq
    omega

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

theorem normalize_aux {ops : α → α → Finset α} {goal : α} (key : α → ℕ) (av : Finset α) :
    ∀ (m inv : ℕ) (gs : List (α × α × α)) (s : Finset α),
      gs.length ≤ m → invCount key gs ≤ inv → s ⊆ av → liveChain ops goal gs s →
      ∃ gs' : List (α × α × α), gs'.length ≤ m ∧ chainOrd key 0 gs' ∧
        ∃ s' ⊆ av, liveChain ops goal gs' s' := by
  intro m
  induction m with
  | zero =>
    intro inv gs s hlen _ hsub hrun
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hnil
    exact ⟨[], Nat.le_refl 0, trivial, s, hsub, hrun⟩
  | succ m ihm =>
    intro inv
    induction inv with
    | zero =>
      intro gs s hlen hinv hsub hrun
      rcases find_violation key 0 gs (fun _ _ _ => Or.inr (Or.inr (Nat.zero_le _))) with
        hord | ⟨pre, g₁, g₂, suf, rfl, h1, h2, hlt⟩
      · exact ⟨gs, hlen, hord, s, hsub, hrun⟩
      · exfalso
        have hpos : 0 < invCount key (pre ++ g₁ :: g₂ :: suf) :=
          Nat.lt_of_le_of_lt (Nat.zero_le _) (invCount_swap_lt key pre suf g₁ g₂ hlt)
        omega
    | succ inv ihi =>
      intro gs s hlen hinv hsub hrun
      rcases find_violation key 0 gs (fun _ _ _ => Or.inr (Or.inr (Nat.zero_le _))) with
        hord | ⟨pre, g₁, g₂, suf, rfl, h1, h2, hlt⟩
      · exact ⟨gs, hlen, hord, s, hsub, hrun⟩
      · have hne1 : g₂.1 ≠ g₁.2.2 := fun heq => h1 (congrArg key heq)
        have hne2 : g₂.2.1 ≠ g₁.2.2 := fun heq => h2 (congrArg key heq)
        rcases swap_in_chain pre g₁ g₂ suf hrun hne1 hne2 with hswap | hshort
        · have hlt' := invCount_swap_lt key pre suf g₁ g₂ hlt
          have hlen' : (pre ++ g₂ :: g₁ :: suf).length ≤ m + 1 := by
            simp only [List.length_append, List.length_cons] at hlen ⊢; omega
          exact ihi (pre ++ g₂ :: g₁ :: suf) s hlen' (by omega) hsub hswap
        · have hbm : build ops goal m av := by
            have hle : pre.length + suf.length + 1 ≤ m := by
              simp only [List.length_append, List.length_cons] at hlen; omega
            have hb1 : build ops goal (pre.length + suf.length + 1) av := build_mono hsub hshort
            clear hshort hsub hrun hlen ihm ihi hinv h1 h2 hlt hne1 hne2
            induction hle with
            | refl => exact hb1
            | step _ ih => exact Or.inl ih
          obtain ⟨gs', hlen', s', hsub', hrun'⟩ := compress_chain hbm
          obtain ⟨gs'', hlen'', hord'', s'', hsub'', hrun''⟩ :=
            ihm (invCount key gs') gs' s' hlen' (Nat.le_refl _) hsub' hrun'
          exact ⟨gs'', Nat.le_succ_of_le hlen'', hord'', s'', hsub'', hrun''⟩

theorem normalize_build {ops : α → α → Finset α} {goal : α} (key : α → ℕ)
    {k : ℕ} {av : Finset α} (h : build ops goal k av) :
    ∃ gs : List (α × α × α), gs.length ≤ k ∧ chainOrd key 0 gs ∧
      ∃ s ⊆ av, liveChain ops goal gs s := by
  obtain ⟨gs, hlen, s, hsub, hrun⟩ := compress_chain h
  exact normalize_aux key av k (invCount key gs) gs s hlen (Nat.le_refl _) hsub hrun

theorem chain_score {ops : α → α → Finset α} {goal : α} (val : α → Nat)
    (sub : ∀ a b, ∀ z ∈ ops a b, val z ≤ val a + val b)
    {gs : List (α × α × α)} {s : Finset α}
    (h : liveChain ops goal gs s) (hc : s.card = gs.length + 1) :
    val goal ≤ s.sum val := by
  induction gs generalizing s with
  | nil =>
    change s = {goal} at h
    simp [h]
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨_, _, _, hgate, hout, rest, rfl, tail⟩
    have hz : z ∉ rest := fun hm => hout (by simp [hm])
    have hnext := chain_card tail
    rw [Finset.card_insert_of_notMem hz] at hnext
    simp only [List.length_cons] at hc
    have ha₀ := Finset.card_insert_le a (insert b rest)
    have hb₀ := Finset.card_insert_le b rest
    have ha : a ∉ insert b rest := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at hc
      omega
    have hb : b ∉ rest := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at ha₀
      rw [Finset.insert_eq_of_mem hm] at hc
      omega
    have ih' := ih tail (by rw [Finset.card_insert_of_notMem hz]; omega)
    rw [Finset.sum_insert hz] at ih'
    rw [Finset.sum_insert ha, Finset.sum_insert hb]
    have hz' := sub a b z hgate
    omega

theorem sum_list_score (val : α → Nat) {ws : List α} (hn : ws.Nodup) :
    ws.toFinset.sum val = (ws.map val).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    obtain ⟨hw, hws⟩ := List.nodup_cons.mp hn
    simp [Finset.sum_insert, hw, ih hws]

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
  [0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28]

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

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

structure ScorePoints where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat

def wireScore (q : ScorePoints) (w : W) : Nat :=
  let x := w.toNat
  value6 (x.testBit q.a) (x.testBit q.b) (x.testBit q.c)
    (x.testBit q.d) (x.testBit q.e) (x.testBit q.f)

theorem score_ops (q : ScorePoints) (a b : W) (z : W) (hz : z ∈ basicOps a b) :
    wireScore q z ≤ wireScore q a + wireScore q b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  rcases hz.1 with rfl | rfl
  · simpa only [wireScore, BitVec.toNat_and, Nat.testBit_and] using value6_and
      (a.toNat.testBit q.a) (a.toNat.testBit q.b) (a.toNat.testBit q.c)
      (a.toNat.testBit q.d) (a.toNat.testBit q.e) (a.toNat.testBit q.f)
      (b.toNat.testBit q.a) (b.toNat.testBit q.b) (b.toNat.testBit q.c)
      (b.toNat.testBit q.d) (b.toNat.testBit q.e) (b.toNat.testBit q.f)
  · simpa only [wireScore, BitVec.toNat_or, Nat.testBit_or] using value6_or
      (a.toNat.testBit q.a) (a.toNat.testBit q.b) (a.toNat.testBit q.c)
      (a.toNat.testBit q.d) (a.toNat.testBit q.e) (a.toNat.testBit q.f)
      (b.toNat.testBit q.a) (b.toNat.testBit q.b) (b.toNat.testBit q.c)
      (b.toNat.testBit q.d) (b.toNat.testBit q.e) (b.toNat.testBit q.f)

def enoughScore (q : ScorePoints) : List W → Nat → Bool
  | [], need => need == 0
  | w :: ws, need =>
    let v := wireScore q w
    if need ≤ v then true else enoughScore q ws (need - v)

theorem enoughScore_of_sum (q : ScorePoints) (ws : List W) (need : Nat)
    (h : need ≤ (ws.map (wireScore q)).sum) : enoughScore q ws need = true := by
  induction ws generalizing need with
  | nil => simp at h; simp [enoughScore, h]
  | cons w ws ih =>
    simp only [List.map_cons, List.sum_cons] at h
    dsimp only [enoughScore]
    split
    · rfl
    · apply ih; omega

def scorePool : List ScorePoints :=
  [⟨112, 64, 118, 0, 1, 4⟩,
   ⟨82, 88, 106, 3, 1, 4⟩,
   ⟨76, 64, 88, 1, 0, 5⟩,
   ⟨100, 106, 118, 4, 0, 3⟩,
   ⟨94, 106, 112, 4, 1, 3⟩,
   ⟨70, 64, 82, 1, 0, 4⟩]

theorem pool_score : ∀ q ∈ scorePool, wireScore q goal = 3 := by
  intro q hq
  simp only [scorePool, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def scoreGuard (extra : Nat) (ws : List W) : Bool :=
  extra != 0 || scorePool.all (fun q => enoughScore q ws 3)

theorem scoreGuard_ok {n extra : Nat} {ws : List W} {gs : List (W × W × W)}
    (hn : ws.Nodup) (hlen : gs.length ≤ n) (room : extra + ws.length = n + 1)
    (h : liveChain basicOps goal gs ws.toFinset) : scoreGuard extra ws = true := by
  by_cases he : extra = 0
  · subst extra
    simp only [scoreGuard, ne_eq, bne_self_eq_false, Bool.false_or, List.all_eq_true]
    intro q hq
    apply enoughScore_of_sum
    have hcard := chain_card h
    rw [List.toFinset_card_of_nodup hn] at hcard
    have exactCard : ws.toFinset.card = gs.length + 1 := by
      rw [List.toFinset_card_of_nodup hn]
      omega
    have hsum := chain_score (wireScore q) (score_ops q) h exactCard
    rw [sum_list_score _ hn, pool_score q hq] at hsum
    exact hsum
  · simp [scoreGuard, he]

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
  | k + 3, extra, last, ws => scoreGuard extra ws && (ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra last (optimized (k + 2)) a b r))

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
        have pass := scoreGuard_ok hn hlen room h
        cases gs with
        | nil =>
          simp only [optimized, pass, Bool.true_and]
          simp [singleton_list hn h]
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
          simp only [optimized, pass, Bool.true_and, Bool.or_eq_true, List.any_eq_true]
          right
          rcases hm with direct | swap
          · exact ⟨(a, b, r), direct, go hp hs hz hg_ord⟩
          · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
              (ops_swap a b ▸ hz) (by rcases hg_ord with h | h | h; exact .inr (.inl h); exact .inl h; exact .inr (.inr h))⟩

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (14285 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) := [(0, 0), (0, 2), (0, 3), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1)]

def negL : List (Fin 4 × Fin 4) := [(0, 1), (1, 0), (1, 1), (2, 3), (3, 2), (3, 3)]

def samp (k : Fin 128) : Fin 4 × Fin 4 :=
  if k.val < 64 then negL.getD (k.val % 6) (0, 0) else posL.getD (((k.val - 64) / 6) % 10) (0, 0)

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


abbrev SearchState := Nat × Nat × List W
def stateResult (d : Nat) (s : SearchState) : Bool := optimized d s.1 s.2.1 s.2.2

def coverNext (d : Nat) (states : List SearchState) (e l : Nat) (ws : List W) : Bool :=
  if (e,l,ws) ∈ states then false else optimized d e l ws

theorem coverNext_eq {d : Nat} {states : List SearchState}
    (h : states.all (fun s => !(stateResult d s)) = true) :
    coverNext d states = optimized d := by
  funext e l ws
  unfold coverNext
  split
  next hm =>
    have hh := List.all_eq_true.mp h (e,l,ws) hm
    change !(optimized d e l ws) = true at hh
    cases hc : optimized d e l ws
    · rfl
    · simp [hc] at hh
  next => rfl

def coverLayer (d : Nat) (s : SearchState) (states : List SearchState) : Bool :=
  scoreGuard s.1 s.2.2 && (s.2.2 == [goal] ||
    (pairs s.2.2).any (fun (a,b,r) => dispatch s.1 s.2.1 (coverNext d states) a b r))

theorem coverResult {k : Nat} {s : SearchState} {states : List SearchState}
    (h : states.all (fun w => !(stateResult (k+2) w)) = true)
    (hl : coverLayer (k+2) s states = false) : stateResult (k+3) s = false := by
  unfold coverLayer at hl
  rw [coverNext_eq h] at hl
  exact hl

def cw0 : W := 0xf00000000000003f0000000000000000
def cw1 : W := 0xf00000000003ffff1041041041041041
def cw2 : W := 0xf03f000fc000003f2082082082082082
def cw3 : W := 0x3ffc00006186186186186186
def cw4 : W := 0xffffc00000008208208208208208
def cw5 : W := 0xfff0000000000000c30c30c30c30c30
def cw6 : W := 0xfc003f0000000005145145145145145
def cw7 : W := 0xfc0000fc0fc00410410410410410
def cw8 : W := 0x3f03f0008a28a28a28a28a28
def cw9 : W := 0xf00000003ffc003f6186186186186186
def cw10 : W := 0xf000ffffc000003f8208208208208208
def cw11 : W := 0xffff00000000003f0c30c30c30c30c30
def cw12 : W := 0xffc003f00000003f5145145145145145
def cw13 : W := 0xf000fc0000fc0fff0410410410410410
def cw14 : W := 0xf00000003f03f03f8a28a28a28a28a28
def cw15 : W := 0xf03f000fc003ffff30c30c30c30c30c3
def cw16 : W := 0xf00000003fffffff71c71c71c71c71c7
def cw17 : W := 0xffc003f00003ffff5145145145145145
def cw18 : W := 0xf03f000ffffc003f6186186186186186
def cw19 : W := 0xffff03ffc000003f71c71c71c71c71c7
def cw20 : W := 0x4104104104104104
def cw21 : W := 0xffc003f03fffffff71c71c71c71c71c7
def cw22 : W := 0x3f0000000000000000000000000
def cw23 : W := 0xffc0ffffc003ffffd34d34d34d34d34d
def cw24 : W := 0xfc00000000000000000000000000000
def cw25 : W := 0xffff03f00003ffff5d75d75d75d75d75
def cw26 : W := 0xffff03ffc003ffff71c71c71c71c71c7
def cw27 : W := 0xfc00000000000000000
def cw28 : W := 0xffc0fff000ffffff5555555555555555
def cw29 : W := 0x3f0000000000000000000
def cw30 : W := 0xffc003f03f03ffffdb6db6db6db6db6d
def cw31 : W := 0xffff000fc000003f2cb2cb2cb2cb2cb2
def cw32 : W := 0x3ffc0fc06186186186186186
def cw33 : W := 0xffffc0000fc08208208208208208
def cw34 : W := 0xfff000000000fc00c30c30c30c30c30
def cw35 : W := 0xf03f000fc0000fff2082082082082082
def cw36 : W := 0xfc003f000000fc05145145145145145
def cw37 : W := 0x3f03ffc08a28a28a28a28a28
def cw38 : W := 0xf000fc0000ffffff1451451451451451
def cw39 : W := 0xffffc0000fc0fc00c30c30c30c30c30
def cw40 : W := 0xfc003fffffc08e38e38e38e38e38
def cw41 : W := 0xfc003f03ffc000071c71c71c71c71c7
def cw42 : W := 0xfffffffc00000008e38e38e38e38e38
def cw43 : W := 0xffffff03f0008a28a28a28a28a28
def cw44 : W := 0xfff00003f03f0008e38e38e38e38e38
def cw45 : W := 0x3ffff0006186186186186186
def cw46 : W := 0xffffc003f0008208208208208208
def cw47 : W := 0xfff00000003f0000c30c30c30c30c30
def cw48 : W := 0xf03f000fc003f03f2082082082082082
def cw49 : W := 0xfc003f00003f0005145145145145145
def cw50 : W := 0xfc0000ffffc00410410410410410
def cw51 : W := 0xf00000003f03ffff9a69a69a69a69a69
def cw52 : W := 0xf000ffffc003ffff9249249249249249
def cw53 : W := 0x3f0000000000000000000000
def cw54 : W := 0xf03f000fffffffff71c71c71c71c71c7
def cw55 : W := 0xfc00000000000000000000000
def cw56 : W := 0xf03ffffffffc003fe38e38e38e38e38e
def cw57 : W := 0x3f0000000000000000000000000000
def cw58 : W := 0xffff000ffffc003f6db6db6db6db6db6
def cw59 : W := 0xffff03fffffc003f71c71c71c71c71c7
def cw60 : W := 0xfc00000000000000000000
def cw61 : W := 0xf03ffc0ffffc0fff6596596596596596
def cw62 : W := 0xf03f000ffffff03febaebaebaebaebae
def cw63 : W := 0xffff00000003ffff1c71c71c71c71c71
def cw64 : W := 0xf03fffffc000003fa28a28a28a28a28a
def cw65 : W := 0xf03ffc0fc0fc0fff2492492492492492
def cw66 : W := 0x1041041041041041
def cw67 : W := 0xfc0fffffffc0000f3cf3cf3cf3cf3cf
def cw68 : W := 0xfff03f03ffc00007df7df7df7df7df7
def cw69 : W := 0x2082082082082082
def cw70 : W := 0xfc0fff03ffc0fc075d75d75d75d75d7
def cw71 : W := 0xfc003f03ffff000fbefbefbefbefbef
def cw72 : W := 0xfc0000000fc00000000000000000000
def cw73 : W := 0xffffff03ffc0fc07df7df7df7df7df7
def cw74 : W := 0xfffffc0000ffffff1c71c71c71c71c71
def cw75 : W := 0xfc00000000000000000000000000
def cw76 : W := 0xfffffffc0fc0fc08e38e38e38e38e38
def cw77 : W := 0xfffffc0fc0fc0fff2cb2cb2cb2cb2cb2
def cw78 : W := 0x820820820820820
def cw79 : W := 0xffffc003fffffc08e38e38e38e38e38
def cw80 : W := 0xf03f000fff03f03faaaaaaaaaaaaaaaa
def cw81 : W := 0xfc000003f0000000000000000000000
def cw82 : W := 0xfff03f03ffff000ffffffffffffffff
def cw83 : W := 0xffff00003f03ffff9e79e79e79e79e79
def cw84 : W := 0x8208208208208208
def cw85 : W := 0xfffffffff03f0008e38e38e38e38e38
def cw86 : W := 0xffff000fff03f03faebaebaebaebaeba
def cw87 : W := 0x410410410410410
def cw88 : W := 0xfff00003ffc00006db6db6db6db6db6
def cw89 : W := 0xfc0ffffc0000000d34d34d34d34d34d
def cw90 : W := 0xfff03f0000000005d75d75d75d75d75
def cw91 : W := 0xfc0fff000fc0fc05555555555555555
def cw92 : W := 0xf000000000ffffff1041041041041041
def cw93 : W := 0xffffc0fc00008208208208208208
def cw94 : W := 0xfff000000fc00000c30c30c30c30c30
def cw95 : W := 0xf03f000fc0fc003f2082082082082082
def cw96 : W := 0xfc003f000fc00005145145145145145
def cw97 : W := 0x3ffff0008a28a28a28a28a28
def cw98 : W := 0xfc003ffc0fc06596596596596596
def cw99 : W := 0xf00000003f03ffff1041041041041041
def cw100 : W := 0xffffff0000008208208208208208
def cw101 : W := 0xfff00003f0000000c30c30c30c30c30
def cw102 : W := 0xf03f000fff00003f2082082082082082
def cw103 : W := 0xfc003f03f0000005145145145145145
def cw104 : W := 0xfc003ffc0fc00410410410410410
def cw105 : W := 0x3ffff000ebaebaebaebaebae
def cw106 : W := 0xfffffffc0000e38e38e38e38e38e
def cw107 : W := 0xffffffffc003ffff9e79e79e79e79e79
def cw108 : W := 0xffffffffffc0000efbefbefbefbefbe
def cw109 : W := 0x3f000fc00000000000000000000000
def cw110 : W := 0xffffffffc000003faebaebaebaebaeba
def cw111 : W := 0xfc003f0000000000000000000000000
def cw112 : W := 0xfffffffc0000000df7df7df7df7df7d
def cw113 : W := 0xfc00000000000410410410410410
def cw114 : W := 0x8a28a28a28a28a28
def cw115 : W := 0xf000000fc003ffff1041041041041041
def cw116 : W := 0xffffc00006186186186186186
def cw117 : W := 0xfff000fc00000000c30c30c30c30c30
def cw118 : W := 0xfc003ffc00000005145145145145145
def cw119 : W := 0xfc0fc0fc0fc00410410410410410
def cw120 : W := 0xfff03f0008a28a28a28a28a28
def cw121 : W := 0xf00003f00003ffff1041041041041041
def cw122 : W := 0x3f03ffc00006186186186186186
def cw123 : W := 0xfff03f0000000000c30c30c30c30c30
def cw124 : W := 0xf03f03ffc000003f2082082082082082
def cw125 : W := 0xfff000fc0fc00410410410410410
def cw126 : W := 0x3f03f03f0008a28a28a28a28a28
def cw127 : W := 0xf000fc000003ffff1041041041041041
def cw128 : W := 0xfc003ffc00006186186186186186
def cw129 : W := 0xf000fc003fffffff71c71c71c71c71c7
def cw130 : W := 0xf03ffc0ffffc003f6186186186186186
def cw131 : W := 0xfc0fff03ffc000071c71c71c71c71c7
def cw132 : W := 0xffffc0fc0fc08618618618618618
def cw133 : W := 0xffffc00000000000c30c30c30c30c30
def cw134 : W := 0xf03ffc0fc000003f2082082082082082
def cw135 : W := 0xfc0fff0000000005145145145145145
def cw136 : W := 0xfc003f03f0008a28a28a28a28a28
def cw137 : W := 0xffffffffffc08e38e38e38e38e38
def cw138 : W := 0x3ffc00000000000000000000
def cw139 : W := 0xf000ffffff03ffff9a69a69a69a69a69
def cw140 : W := 0xfffffffff000ebaebaebaebaebae
def cw141 : W := 0xffffffffff03ffff9e79e79e79e79e79
def cw142 : W := 0xffffffffffff000efbefbefbefbefbe
def cw143 : W := 0xffffffffff03f03faebaebaebaebaeba
def cw144 : W := 0xfffffffff03f000df7df7df7df7df7d
def cw145 : W := 0xfffffffffffffc08e38e38e38e38e38
def cw146 : W := 0xf03fffffff03f03faaaaaaaaaaaaaaaa
def cw147 : W := 0xfc0ffffff03f000db6db6db6db6db6d
def cw148 : W := 0xf000ffffff03f03f8a28a28a28a28a28
def cw149 : W := 0x3f03f0000000000000000000000
def cw150 : W := 0xfc0fffffffff000fbefbefbefbefbef
def cw151 : W := 0xfc00000000000820820820820820
def cw152 : W := 0xffffc003ffc0fc06db6db6db6db6db6
def cw153 : W := 0xffffff000fc0fc05d75d75d75d75d75
def cw154 : W := 0xfc003f03f03f000db6db6db6db6db6d
def cw155 : W := 0xf03f00000003ffff1041041041041041
def cw156 : W := 0x3f00003ffc00006186186186186186
def cw157 : W := 0x3fffffc00000008208208208208208
def cw158 : W := 0xfff03f0000000005145145145145145
def cw159 : W := 0x3ffc0000fc0fc00410410410410410
def cw160 : W := 0x3f00003f03f0008a28a28a28a28a28
def cw161 : W := 0xffc000000003ffff1041041041041041
def cw162 : W := 0xfc000003ffc00006186186186186186
def cw163 : W := 0xfc0ffffc00000008208208208208208
def cw164 : W := 0xffff000fc000003f2082082082082082
def cw165 : W := 0xfc0fc0000fc0fc00410410410410410
def cw166 : W := 0xfc000003f03f0008a28a28a28a28a28
def cw167 : W := 0x3ffc00000000000000000
def cw168 : W := 0xfffffc003fffffff9e79e79e79e79e79
def cw169 : W := 0xffffc003fffffc0efbefbefbefbefbe
def cw170 : W := 0xfc00000000008208208208208208
def cw171 : W := 0xfffffc0fffffffffaebaebaebaebaeba
def cw172 : W := 0xffffff03fffffc0df7df7df7df7df7d
def cw173 : W := 0xfffffc0000fc0fff0c30c30c30c30c30
def cw174 : W := 0xfff00003ffff000efbefbefbefbefbe
def cw175 : W := 0xfff03f03f03f000df7df7df7df7df7d
def cw176 : W := 0xffff00003f03f03f8e38e38e38e38e38
def cw177 : W := 0x3f00003f0000000000000000000000
def cw178 : W := 0xffff000ffffff03fefbefbefbefbefbe
def cw179 : W := 0xf000fc003fffffff9e79e79e79e79e79
def cw180 : W := 0xfc003fffffc0efbefbefbefbefbe
def cw181 : W := 0xc30c30c30c30c30
def cw182 : W := 0xf03ffc0fffffffffaebaebaebaebaeba
def cw183 : W := 0xfc0fff03fffffc0df7df7df7df7df7d
def mc0 : SearchState := (1,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw3,cw4,cw5,cw6,cw7,cw8])
def mc1 : SearchState := (1,0xf00000003ffc003f6186186186186186,[cw9,cw1,cw2,cw4,cw5,cw6,cw7,cw8])
def mc2 : SearchState := (0,0xf00000003ffc003f6186186186186186,[cw9,cw0,cw1,cw2,cw4,cw5,cw6,cw7,cw8])
def mc3 : SearchState := (0,0xf00000003ffc003f6186186186186186,[cw9,cw3,cw1,cw2,cw4,cw5,cw6,cw7,cw8])
def mc4 : SearchState := (1,0xf000ffffc000003f8208208208208208,[cw10,cw1,cw2,cw3,cw5,cw6,cw7,cw8])
def mc5 : SearchState := (0,0xf000ffffc000003f8208208208208208,[cw10,cw0,cw1,cw2,cw3,cw5,cw6,cw7,cw8])
def mc6 : SearchState := (0,0xf000ffffc000003f8208208208208208,[cw10,cw4,cw1,cw2,cw3,cw5,cw6,cw7,cw8])
def mc7 : SearchState := (1,0xffff00000000003f0c30c30c30c30c30,[cw11,cw1,cw2,cw3,cw4,cw6,cw7,cw8])
def mc8 : SearchState := (0,0xffff00000000003f0c30c30c30c30c30,[cw11,cw0,cw1,cw2,cw3,cw4,cw6,cw7,cw8])
def mc9 : SearchState := (0,0xffff00000000003f0c30c30c30c30c30,[cw11,cw5,cw1,cw2,cw3,cw4,cw6,cw7,cw8])
def mc10 : SearchState := (1,0xffc003f00000003f5145145145145145,[cw12,cw1,cw2,cw3,cw4,cw5,cw7,cw8])
def mc11 : SearchState := (0,0xffc003f00000003f5145145145145145,[cw12,cw0,cw1,cw2,cw3,cw4,cw5,cw7,cw8])
def mc12 : SearchState := (0,0xffc003f00000003f5145145145145145,[cw12,cw6,cw1,cw2,cw3,cw4,cw5,cw7,cw8])
def mc13 : SearchState := (1,0xf000fc0000fc0fff0410410410410410,[cw13,cw1,cw2,cw3,cw4,cw5,cw6,cw8])
def mc14 : SearchState := (0,0xf000fc0000fc0fff0410410410410410,[cw13,cw0,cw1,cw2,cw3,cw4,cw5,cw6,cw8])
def mc15 : SearchState := (0,0xf000fc0000fc0fff0410410410410410,[cw13,cw7,cw1,cw2,cw3,cw4,cw5,cw6,cw8])
def mc16 : SearchState := (1,0xf00000003f03f03f8a28a28a28a28a28,[cw14,cw1,cw2,cw3,cw4,cw5,cw6,cw7])
def mc17 : SearchState := (0,0xf00000003f03f03f8a28a28a28a28a28,[cw14,cw0,cw1,cw2,cw3,cw4,cw5,cw6,cw7])
def mc18 : SearchState := (0,0xf00000003f03f03f8a28a28a28a28a28,[cw14,cw8,cw1,cw2,cw3,cw4,cw5,cw6,cw7])
def mc19 : SearchState := (1,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw0,cw3,cw4,cw5,cw6,cw7,cw8])
def mc20 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw0,cw3,cw4,cw5,cw6,cw7,cw8])
def mc21 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw2,cw0,cw3,cw4,cw5,cw6,cw7,cw8])
def mc22 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw0,cw2,cw4,cw5,cw6,cw7,cw8])
def mc23 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw0,cw2,cw4,cw5,cw6,cw7,cw8])
def mc24 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw3,cw0,cw2,cw4,cw5,cw6,cw7,cw8])
def mc25 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw0,cw2,cw3,cw4,cw5,cw7,cw8])
def mc26 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw0,cw2,cw3,cw4,cw5,cw7,cw8])
def mc27 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw0,cw2,cw3,cw4,cw5,cw7,cw8])
def mc28 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw0,cw1,cw4,cw5,cw6,cw7,cw8])
def mc29 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw0,cw1,cw4,cw5,cw6,cw7,cw8])
def mc30 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw0,cw1,cw4,cw5,cw6,cw7,cw8])
def mc31 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw0,cw1,cw3,cw4,cw5,cw7,cw8])
def mc32 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw0,cw1,cw3,cw4,cw5,cw7,cw8])
def mc33 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw6,cw0,cw1,cw3,cw4,cw5,cw7,cw8])
def mc34 : SearchState := (3,0xffc003f00003ffff5145145145145145,[cw17,cw3,cw4,cw5,cw2,cw7,cw8])
def mc35 : SearchState := (1,0x4104104104104104,[cw20,cw17,cw3,cw4,cw5,cw2,cw7,cw8])
def mc36 : SearchState := (2,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw17,cw4,cw5,cw2,cw7,cw8])
def mc37 : SearchState := (1,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw17,cw3,cw4,cw5,cw2,cw7,cw8])
def mc38 : SearchState := (1,0x3f0000000000000000000000000,[cw22,cw17,cw4,cw3,cw5,cw2,cw7,cw8])
def mc39 : SearchState := (1,0xffc0ffffc003ffffd34d34d34d34d34d,[cw23,cw17,cw4,cw3,cw5,cw2,cw7,cw8])
def mc40 : SearchState := (1,0xfc00000000000000000000000000000,[cw24,cw17,cw5,cw3,cw4,cw2,cw7,cw8])
def mc41 : SearchState := (1,0xffff03f00003ffff5d75d75d75d75d75,[cw25,cw17,cw5,cw3,cw4,cw2,cw7,cw8])
def mc42 : SearchState := (1,0xf00000000000003f0000000000000000,[cw0,cw17,cw2,cw3,cw4,cw5,cw7,cw8])
def mc43 : SearchState := (1,0xffff03ffc003ffff71c71c71c71c71c7,[cw26,cw17,cw2,cw3,cw4,cw5,cw7,cw8])
def mc44 : SearchState := (1,0xfc00000000000000000,[cw27,cw17,cw7,cw3,cw4,cw5,cw2,cw8])
def mc45 : SearchState := (1,0xffc0fff000ffffff5555555555555555,[cw28,cw17,cw7,cw3,cw4,cw5,cw2,cw8])
def mc46 : SearchState := (1,0x3f0000000000000000000,[cw29,cw17,cw8,cw3,cw4,cw5,cw2,cw7])
def mc47 : SearchState := (1,0xffc003f03f03ffffdb6db6db6db6db6d,[cw30,cw17,cw8,cw3,cw4,cw5,cw2,cw7])
def mc48 : SearchState := (1,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw2,cw17,cw3,cw4,cw7,cw8])
def mc49 : SearchState := (1,0xfc00000000000000000,[cw27,cw1,cw7,cw3,cw4,cw5,cw2,cw6,cw8])
def mc50 : SearchState := (1,0x3ffc0fc06186186186186186,[cw32,cw1,cw7,cw4,cw5,cw2,cw6,cw8])
def mc51 : SearchState := (0,0x3ffc0fc06186186186186186,[cw32,cw27,cw1,cw7,cw4,cw5,cw2,cw6,cw8])
def mc52 : SearchState := (0,0x3ffc0fc06186186186186186,[cw32,cw3,cw1,cw7,cw4,cw5,cw2,cw6,cw8])
def mc53 : SearchState := (1,0xffffc0000fc08208208208208208,[cw33,cw1,cw7,cw3,cw5,cw2,cw6,cw8])
def mc54 : SearchState := (0,0xffffc0000fc08208208208208208,[cw33,cw27,cw1,cw7,cw3,cw5,cw2,cw6,cw8])
def mc55 : SearchState := (0,0xffffc0000fc08208208208208208,[cw33,cw4,cw1,cw7,cw3,cw5,cw2,cw6,cw8])
def mc56 : SearchState := (1,0xfff000000000fc00c30c30c30c30c30,[cw34,cw1,cw7,cw3,cw4,cw2,cw6,cw8])
def mc57 : SearchState := (0,0xfff000000000fc00c30c30c30c30c30,[cw34,cw27,cw1,cw7,cw3,cw4,cw2,cw6,cw8])
def mc58 : SearchState := (0,0xfff000000000fc00c30c30c30c30c30,[cw34,cw5,cw1,cw7,cw3,cw4,cw2,cw6,cw8])
def mc59 : SearchState := (1,0xf03f000fc0000fff2082082082082082,[cw35,cw1,cw7,cw3,cw4,cw5,cw6,cw8])
def mc60 : SearchState := (0,0xf03f000fc0000fff2082082082082082,[cw35,cw27,cw1,cw7,cw3,cw4,cw5,cw6,cw8])
def mc61 : SearchState := (0,0xf03f000fc0000fff2082082082082082,[cw35,cw2,cw1,cw7,cw3,cw4,cw5,cw6,cw8])
def mc62 : SearchState := (1,0xfc003f000000fc05145145145145145,[cw36,cw1,cw7,cw3,cw4,cw5,cw2,cw8])
def mc63 : SearchState := (0,0xfc003f000000fc05145145145145145,[cw36,cw27,cw1,cw7,cw3,cw4,cw5,cw2,cw8])
def mc64 : SearchState := (0,0xfc003f000000fc05145145145145145,[cw36,cw6,cw1,cw7,cw3,cw4,cw5,cw2,cw8])
def mc65 : SearchState := (1,0x3f03ffc08a28a28a28a28a28,[cw37,cw1,cw7,cw3,cw4,cw5,cw2,cw6])
def mc66 : SearchState := (0,0x3f03ffc08a28a28a28a28a28,[cw37,cw27,cw1,cw7,cw3,cw4,cw5,cw2,cw6])
def mc67 : SearchState := (0,0x3f03ffc08a28a28a28a28a28,[cw37,cw8,cw1,cw7,cw3,cw4,cw5,cw2,cw6])
def mc68 : SearchState := (1,0xf000fc0000ffffff1451451451451451,[cw38,cw27,cw3,cw4,cw5,cw2,cw6,cw8])
def mc69 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw27,cw3,cw4,cw5,cw2,cw6,cw8])
def mc70 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw7,cw27,cw3,cw4,cw5,cw2,cw6,cw8])
def mc71 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw27,cw7,cw4,cw5,cw2,cw6,cw8])
def mc72 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw27,cw7,cw3,cw4,cw5,cw2,cw8])
def mc73 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw27,cw7,cw3,cw4,cw5,cw2,cw8])
def mc74 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw27,cw7,cw3,cw4,cw5,cw2,cw8])
def mc75 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw27,cw1,cw3,cw4,cw2,cw6,cw8])
def mc76 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw27,cw1,cw3,cw4,cw2,cw6,cw8])
def mc77 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw27,cw1,cw3,cw4,cw2,cw6,cw8])
def mc78 : SearchState := (0,0xfc003fffffc08e38e38e38e38e38,[cw40,cw7,cw27,cw1,cw3,cw4,cw5,cw2,cw6])
def mc79 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw27,cw1,cw7,cw4,cw5,cw6,cw8])
def mc80 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw27,cw1,cw7,cw4,cw5,cw6,cw8])
def mc81 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw27,cw1,cw7,cw4,cw5,cw6,cw8])
def mc82 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw27,cw1,cw7,cw4,cw5,cw2,cw8])
def mc83 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw27,cw1,cw7,cw4,cw5,cw2,cw8])
def mc84 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw27,cw1,cw7,cw4,cw5,cw2,cw8])
def mc85 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw27,cw1,cw7,cw3,cw2,cw6,cw8])
def mc86 : SearchState := (1,0xffffff03f0008a28a28a28a28a28,[cw43,cw27,cw1,cw7,cw3,cw5,cw2,cw6])
def mc87 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw4,cw27,cw1,cw7,cw3,cw5,cw2,cw6])
def mc88 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw8,cw27,cw1,cw7,cw3,cw5,cw2,cw6])
def mc89 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw27,cw1,cw7,cw3,cw4,cw2,cw6])
def mc90 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw27,cw1,cw7,cw3,cw4,cw2,cw6])
def mc91 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw27,cw1,cw7,cw3,cw4,cw2,cw6])
def mc92 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw27,cw1,cw7,cw3,cw4,cw5,cw8])
def mc93 : SearchState := (1,0x3f0000000000000000000,[cw29,cw1,cw8,cw3,cw4,cw5,cw2,cw6,cw7])
def mc94 : SearchState := (1,0x3ffff0006186186186186186,[cw45,cw1,cw8,cw4,cw5,cw2,cw6,cw7])
def mc95 : SearchState := (0,0x3ffff0006186186186186186,[cw45,cw29,cw1,cw8,cw4,cw5,cw2,cw6,cw7])
def mc96 : SearchState := (0,0x3ffff0006186186186186186,[cw45,cw3,cw1,cw8,cw4,cw5,cw2,cw6,cw7])
def mc97 : SearchState := (1,0xffffc003f0008208208208208208,[cw46,cw1,cw8,cw3,cw5,cw2,cw6,cw7])
def mc98 : SearchState := (0,0xffffc003f0008208208208208208,[cw46,cw29,cw1,cw8,cw3,cw5,cw2,cw6,cw7])
def mc99 : SearchState := (0,0xffffc003f0008208208208208208,[cw46,cw4,cw1,cw8,cw3,cw5,cw2,cw6,cw7])
def mc100 : SearchState := (1,0xfff00000003f0000c30c30c30c30c30,[cw47,cw1,cw8,cw3,cw4,cw2,cw6,cw7])
def mc101 : SearchState := (0,0xfff00000003f0000c30c30c30c30c30,[cw47,cw29,cw1,cw8,cw3,cw4,cw2,cw6,cw7])
def mc102 : SearchState := (0,0xfff00000003f0000c30c30c30c30c30,[cw47,cw5,cw1,cw8,cw3,cw4,cw2,cw6,cw7])
def mc103 : SearchState := (1,0xf03f000fc003f03f2082082082082082,[cw48,cw1,cw8,cw3,cw4,cw5,cw6,cw7])
def mc104 : SearchState := (0,0xf03f000fc003f03f2082082082082082,[cw48,cw29,cw1,cw8,cw3,cw4,cw5,cw6,cw7])
def mc105 : SearchState := (0,0xf03f000fc003f03f2082082082082082,[cw48,cw2,cw1,cw8,cw3,cw4,cw5,cw6,cw7])
def mc106 : SearchState := (1,0xfc003f00003f0005145145145145145,[cw49,cw1,cw8,cw3,cw4,cw5,cw2,cw7])
def mc107 : SearchState := (0,0xfc003f00003f0005145145145145145,[cw49,cw29,cw1,cw8,cw3,cw4,cw5,cw2,cw7])
def mc108 : SearchState := (0,0xfc003f00003f0005145145145145145,[cw49,cw6,cw1,cw8,cw3,cw4,cw5,cw2,cw7])
def mc109 : SearchState := (1,0xfc0000ffffc00410410410410410,[cw50,cw1,cw8,cw3,cw4,cw5,cw2,cw6])
def mc110 : SearchState := (0,0xfc0000ffffc00410410410410410,[cw50,cw29,cw1,cw8,cw3,cw4,cw5,cw2,cw6])
def mc111 : SearchState := (0,0xfc0000ffffc00410410410410410,[cw50,cw7,cw1,cw8,cw3,cw4,cw5,cw2,cw6])
def mc112 : SearchState := (1,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw29,cw3,cw4,cw5,cw2,cw6,cw7])
def mc113 : SearchState := (0,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw1,cw29,cw3,cw4,cw5,cw2,cw6,cw7])
def mc114 : SearchState := (0,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw8,cw29,cw3,cw4,cw5,cw2,cw6,cw7])
def mc115 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw29,cw8,cw4,cw5,cw2,cw6,cw7])
def mc116 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw4,cw29,cw8,cw3,cw5,cw2,cw6,cw7])
def mc117 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw29,cw8,cw3,cw4,cw5,cw2,cw7])
def mc118 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw29,cw8,cw3,cw4,cw5,cw2,cw7])
def mc119 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw29,cw8,cw3,cw4,cw5,cw2,cw7])
def mc120 : SearchState := (0,0x3f0000000000000000000000,[cw53,cw3,cw29,cw1,cw4,cw5,cw2,cw6,cw7])
def mc121 : SearchState := (1,0xffffff03f0008a28a28a28a28a28,[cw43,cw29,cw1,cw3,cw5,cw2,cw6,cw7])
def mc122 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw8,cw29,cw1,cw3,cw5,cw2,cw6,cw7])
def mc123 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw4,cw29,cw1,cw3,cw5,cw2,cw6,cw7])
def mc124 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw29,cw1,cw3,cw4,cw2,cw6,cw7])
def mc125 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw29,cw1,cw3,cw4,cw2,cw6,cw7])
def mc126 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw29,cw1,cw3,cw4,cw2,cw6,cw7])
def mc127 : SearchState := (0,0xfc003fffffc08e38e38e38e38e38,[cw40,cw7,cw29,cw1,cw3,cw4,cw5,cw2,cw6])
def mc128 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw29,cw1,cw8,cw4,cw5,cw6,cw7])
def mc129 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw29,cw1,cw8,cw4,cw5,cw6,cw7])
def mc130 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw29,cw1,cw8,cw4,cw5,cw6,cw7])
def mc131 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw29,cw1,cw8,cw4,cw5,cw2,cw7])
def mc132 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw29,cw1,cw8,cw4,cw5,cw2,cw7])
def mc133 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw29,cw1,cw8,cw4,cw5,cw2,cw7])
def mc134 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw29,cw1,cw8,cw3,cw2,cw6,cw7])
def mc135 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw29,cw1,cw8,cw3,cw4,cw2,cw6])
def mc136 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw29,cw1,cw8,cw3,cw4,cw2,cw6])
def mc137 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw29,cw1,cw8,cw3,cw4,cw2,cw6])
def mc138 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw29,cw1,cw8,cw3,cw4,cw5,cw7])
def mc139 : SearchState := (3,0xf03f000ffffc003f6186186186186186,[cw18,cw1,cw4,cw5,cw6,cw7,cw8])
def mc140 : SearchState := (1,0xf00000000000003f0000000000000000,[cw0,cw18,cw1,cw4,cw5,cw6,cw7,cw8])
def mc141 : SearchState := (1,0xf03f000fffffffff71c71c71c71c71c7,[cw54,cw18,cw1,cw4,cw5,cw6,cw7,cw8])
def mc142 : SearchState := (1,0xfc00000000000000000000000,[cw55,cw18,cw4,cw1,cw5,cw6,cw7,cw8])
def mc143 : SearchState := (1,0xf03ffffffffc003fe38e38e38e38e38e,[cw56,cw18,cw4,cw1,cw5,cw6,cw7,cw8])
def mc144 : SearchState := (1,0x3f0000000000000000000000000000,[cw57,cw18,cw5,cw1,cw4,cw6,cw7,cw8])
def mc145 : SearchState := (1,0xffff000ffffc003f6db6db6db6db6db6,[cw58,cw18,cw5,cw1,cw4,cw6,cw7,cw8])
def mc146 : SearchState := (1,0x4104104104104104,[cw20,cw18,cw6,cw1,cw4,cw5,cw7,cw8])
def mc147 : SearchState := (2,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw18,cw1,cw4,cw5,cw7,cw8])
def mc148 : SearchState := (1,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw18,cw6,cw1,cw4,cw5,cw7,cw8])
def mc149 : SearchState := (1,0xfc00000000000000000000,[cw60,cw18,cw7,cw1,cw4,cw5,cw6,cw8])
def mc150 : SearchState := (1,0xf03ffc0ffffc0fff6596596596596596,[cw61,cw18,cw7,cw1,cw4,cw5,cw6,cw8])
def mc151 : SearchState := (1,0x3f0000000000000000000000,[cw53,cw18,cw8,cw1,cw4,cw5,cw6,cw7])
def mc152 : SearchState := (1,0xf03f000ffffff03febaebaebaebaebae,[cw62,cw18,cw8,cw1,cw4,cw5,cw6,cw7])
def mc153 : SearchState := (1,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw5,cw18,cw4,cw6,cw7,cw8])
def mc154 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw18,cw4,cw5,cw7,cw8])
def mc155 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw18,cw4,cw5,cw7,cw8])
def mc156 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw1,cw4,cw5,cw6,cw7,cw8])
def mc157 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw18,cw1,cw2,cw4,cw5,cw6,cw7,cw8])
def mc158 : SearchState := (1,0xf03f000fffffffff71c71c71c71c71c7,[cw54,cw1,cw2,cw4,cw5,cw6,cw7,cw8])
def mc159 : SearchState := (0,0xf03f000fffffffff71c71c71c71c71c7,[cw54,cw18,cw1,cw2,cw4,cw5,cw6,cw7,cw8])
def mc160 : SearchState := (0,0xfc00000000000000000000000,[cw55,cw18,cw4,cw2,cw1,cw5,cw6,cw7,cw8])
def mc161 : SearchState := (0,0xf03ffffffffc003fe38e38e38e38e38e,[cw56,cw18,cw4,cw2,cw1,cw5,cw6,cw7,cw8])
def mc162 : SearchState := (0,0x3f0000000000000000000000000000,[cw57,cw18,cw5,cw2,cw1,cw4,cw6,cw7,cw8])
def mc163 : SearchState := (0,0xffff000ffffc003f6db6db6db6db6db6,[cw58,cw18,cw5,cw2,cw1,cw4,cw6,cw7,cw8])
def mc164 : SearchState := (0,0x4104104104104104,[cw20,cw18,cw6,cw2,cw1,cw4,cw5,cw7,cw8])
def mc165 : SearchState := (2,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw2,cw1,cw4,cw5,cw7,cw8])
def mc166 : SearchState := (1,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw18,cw2,cw1,cw4,cw5,cw7,cw8])
def mc167 : SearchState := (1,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw6,cw2,cw1,cw4,cw5,cw7,cw8])
def mc168 : SearchState := (0,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw18,cw6,cw2,cw1,cw4,cw5,cw7,cw8])
def mc169 : SearchState := (0,0xfc00000000000000000000,[cw60,cw18,cw7,cw2,cw1,cw4,cw5,cw6,cw8])
def mc170 : SearchState := (0,0xf03ffc0ffffc0fff6596596596596596,[cw61,cw18,cw7,cw2,cw1,cw4,cw5,cw6,cw8])
def mc171 : SearchState := (0,0x3f0000000000000000000000,[cw53,cw18,cw8,cw2,cw1,cw4,cw5,cw6,cw7])
def mc172 : SearchState := (0,0xf03f000ffffff03febaebaebaebaebae,[cw62,cw18,cw8,cw2,cw1,cw4,cw5,cw6,cw7])
def mc173 : SearchState := (1,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw18,cw1,cw5,cw6,cw7,cw8])
def mc174 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw2,cw4,cw18,cw1,cw5,cw6,cw7,cw8])
def mc175 : SearchState := (1,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw18,cw1,cw4,cw6,cw7,cw8])
def mc176 : SearchState := (0,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw2,cw5,cw18,cw1,cw4,cw6,cw7,cw8])
def mc177 : SearchState := (2,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw18,cw1,cw4,cw5,cw7,cw8])
def mc178 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw18,cw1,cw4,cw5,cw7,cw8])
def mc179 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw6,cw18,cw1,cw4,cw5,cw7,cw8])
def mc180 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw18,cw1,cw4,cw5,cw7,cw8])
def mc181 : SearchState := (1,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw7,cw18,cw1,cw4,cw5,cw6,cw8])
def mc182 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw18,cw1,cw4,cw5,cw6,cw8])
def mc183 : SearchState := (0,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw5,cw18,cw2,cw4,cw6,cw7,cw8])
def mc184 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw18,cw2,cw4,cw5,cw7,cw8])
def mc185 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw18,cw2,cw4,cw5,cw7,cw8])
def mc186 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw18,cw2,cw4,cw5,cw7,cw8])
def mc187 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw18,cw2,cw4,cw5,cw7,cw8])
def mc188 : SearchState := (3,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw1,cw4,cw5,cw2,cw7,cw8])
def mc189 : SearchState := (1,0x1041041041041041,[cw66,cw41,cw1,cw4,cw5,cw2,cw7,cw8])
def mc190 : SearchState := (2,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw1,cw4,cw5,cw2,cw7,cw8])
def mc191 : SearchState := (1,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw41,cw1,cw4,cw5,cw2,cw7,cw8])
def mc192 : SearchState := (1,0x3f0000000000000000000000000,[cw22,cw41,cw4,cw1,cw5,cw2,cw7,cw8])
def mc193 : SearchState := (1,0xfc0fffffffc0000f3cf3cf3cf3cf3cf,[cw67,cw41,cw4,cw1,cw5,cw2,cw7,cw8])
def mc194 : SearchState := (1,0xfc00000000000000000000000000000,[cw24,cw41,cw5,cw1,cw4,cw2,cw7,cw8])
def mc195 : SearchState := (1,0xfff03f03ffc00007df7df7df7df7df7,[cw68,cw41,cw5,cw1,cw4,cw2,cw7,cw8])
def mc196 : SearchState := (1,0x2082082082082082,[cw69,cw41,cw2,cw1,cw4,cw5,cw7,cw8])
def mc197 : SearchState := (1,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw41,cw2,cw1,cw4,cw5,cw7,cw8])
def mc198 : SearchState := (1,0xfc00000000000000000000,[cw60,cw41,cw7,cw1,cw4,cw5,cw2,cw8])
def mc199 : SearchState := (1,0xfc0fff03ffc0fc075d75d75d75d75d7,[cw70,cw41,cw7,cw1,cw4,cw5,cw2,cw8])
def mc200 : SearchState := (1,0x3f0000000000000000000000,[cw53,cw41,cw8,cw1,cw4,cw5,cw2,cw7])
def mc201 : SearchState := (1,0xfc003f03ffff000fbefbefbefbefbef,[cw71,cw41,cw8,cw1,cw4,cw5,cw2,cw7])
def mc202 : SearchState := (1,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw41,cw5,cw2,cw7,cw8])
def mc203 : SearchState := (1,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw5,cw41,cw4,cw2,cw7,cw8])
def mc204 : SearchState := (1,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw41,cw4,cw5,cw7,cw8])
def mc205 : SearchState := (1,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw41,cw4,cw5,cw7,cw8])
def mc206 : SearchState := (1,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw41,cw4,cw5,cw2,cw8])
def mc207 : SearchState := (1,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw1,cw8,cw41,cw4,cw5,cw2,cw7])
def mc208 : SearchState := (2,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw41,cw1,cw2,cw7,cw8])
def mc209 : SearchState := (1,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw5,cw41,cw1,cw2,cw7,cw8])
def mc210 : SearchState := (1,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw41,cw1,cw5,cw7,cw8])
def mc211 : SearchState := (1,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw2,cw41,cw1,cw4,cw7,cw8])
def mc212 : SearchState := (3,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw41,cw1,cw4,cw2,cw8])
def mc213 : SearchState := (1,0xfc0000000fc00000000000000000000,[cw72,cw39,cw41,cw1,cw4,cw2,cw8])
def mc214 : SearchState := (1,0xffffff03ffc0fc07df7df7df7df7df7,[cw73,cw39,cw41,cw1,cw4,cw2,cw8])
def mc215 : SearchState := (1,0xfc00000000000000000,[cw27,cw39,cw1,cw41,cw4,cw2,cw8])
def mc216 : SearchState := (1,0xfffffc0000ffffff1c71c71c71c71c71,[cw74,cw39,cw1,cw41,cw4,cw2,cw8])
def mc217 : SearchState := (1,0xfc00000000000000000000000000,[cw75,cw39,cw4,cw41,cw1,cw2,cw8])
def mc218 : SearchState := (1,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw39,cw4,cw41,cw1,cw2,cw8])
def mc219 : SearchState := (1,0x3f0000000000000000000000000000,[cw57,cw39,cw2,cw41,cw1,cw4,cw8])
def mc220 : SearchState := (1,0xfffffc0fc0fc0fff2cb2cb2cb2cb2cb2,[cw77,cw39,cw2,cw41,cw1,cw4,cw8])
def mc221 : SearchState := (1,0x820820820820820,[cw78,cw39,cw8,cw41,cw1,cw4,cw2])
def mc222 : SearchState := (2,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw39,cw41,cw1,cw4,cw2])
def mc223 : SearchState := (1,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw39,cw8,cw41,cw1,cw4,cw2])
def mc224 : SearchState := (2,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw1,cw39,cw4,cw2,cw8])
def mc225 : SearchState := (1,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw41,cw1,cw39,cw4,cw2,cw8])
def mc226 : SearchState := (2,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw2,cw39,cw1,cw4,cw8])
def mc227 : SearchState := (1,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw41,cw2,cw39,cw1,cw4,cw8])
def mc228 : SearchState := (1,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw39,cw41,cw2,cw8])
def mc229 : SearchState := (1,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw39,cw41,cw4,cw8])
def mc230 : SearchState := (1,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw39,cw41,cw4,cw8])
def mc231 : SearchState := (1,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw1,cw8,cw39,cw41,cw4,cw2])
def mc232 : SearchState := (1,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw39,cw41,cw1,cw8])
def mc233 : SearchState := (1,0xf03f000fff03f03faaaaaaaaaaaaaaaa,[cw80,cw2,cw8,cw39,cw41,cw1,cw4])
def mc234 : SearchState := (2,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw41,cw1,cw4,cw2,cw8])
def mc235 : SearchState := (2,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw41,cw1,cw4,cw2,cw8])
def mc236 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw7,cw41,cw1,cw4,cw2,cw8])
def mc237 : SearchState := (3,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw41,cw1,cw4,cw2,cw7])
def mc238 : SearchState := (1,0xfc000003f0000000000000000000000,[cw81,cw44,cw41,cw1,cw4,cw2,cw7])
def mc239 : SearchState := (1,0xfff03f03ffff000ffffffffffffffff,[cw82,cw44,cw41,cw1,cw4,cw2,cw7])
def mc240 : SearchState := (1,0x3f0000000000000000000,[cw29,cw44,cw1,cw41,cw4,cw2,cw7])
def mc241 : SearchState := (1,0xffff00003f03ffff9e79e79e79e79e79,[cw83,cw44,cw1,cw41,cw4,cw2,cw7])
def mc242 : SearchState := (1,0x8208208208208208,[cw84,cw44,cw4,cw41,cw1,cw2,cw7])
def mc243 : SearchState := (2,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw4,cw41,cw1,cw2,cw7])
def mc244 : SearchState := (1,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw44,cw4,cw41,cw1,cw2,cw7])
def mc245 : SearchState := (1,0x3f0000000000000000000000000000,[cw57,cw44,cw2,cw41,cw1,cw4,cw7])
def mc246 : SearchState := (1,0xffff000fff03f03faebaebaebaebaeba,[cw86,cw44,cw2,cw41,cw1,cw4,cw7])
def mc247 : SearchState := (1,0x410410410410410,[cw87,cw44,cw7,cw41,cw1,cw4,cw2])
def mc248 : SearchState := (2,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw7,cw41,cw1,cw4,cw2])
def mc249 : SearchState := (1,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw44,cw7,cw41,cw1,cw4,cw2])
def mc250 : SearchState := (2,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw1,cw44,cw4,cw2,cw7])
def mc251 : SearchState := (1,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw41,cw1,cw44,cw4,cw2,cw7])
def mc252 : SearchState := (2,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw2,cw44,cw1,cw4,cw7])
def mc253 : SearchState := (1,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw41,cw2,cw44,cw1,cw4,cw7])
def mc254 : SearchState := (1,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw44,cw41,cw2,cw7])
def mc255 : SearchState := (1,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw44,cw41,cw4,cw7])
def mc256 : SearchState := (1,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw44,cw41,cw4,cw7])
def mc257 : SearchState := (1,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw44,cw41,cw4,cw2])
def mc258 : SearchState := (1,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw44,cw41,cw1,cw7])
def mc259 : SearchState := (1,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw44,cw41,cw1,cw4])
def mc260 : SearchState := (2,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw41,cw1,cw4,cw2,cw7])
def mc261 : SearchState := (2,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw41,cw1,cw4,cw2,cw7])
def mc262 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw8,cw41,cw1,cw4,cw2,cw7])
def mc263 : SearchState := (1,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw41,cw1,cw4,cw5,cw8])
def mc264 : SearchState := (1,0xf03f000fff03f03faaaaaaaaaaaaaaaa,[cw80,cw2,cw8,cw41,cw1,cw4,cw5,cw7])
def mc265 : SearchState := (2,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw1,cw4,cw5,cw2,cw7,cw8])
def mc266 : SearchState := (0,0x1041041041041041,[cw66,cw41,cw1,cw3,cw4,cw5,cw2,cw7,cw8])
def mc267 : SearchState := (1,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw1,cw3,cw4,cw5,cw2,cw7,cw8])
def mc268 : SearchState := (0,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw41,cw1,cw3,cw4,cw5,cw2,cw7,cw8])
def mc269 : SearchState := (0,0x3f0000000000000000000000000,[cw22,cw41,cw4,cw3,cw1,cw5,cw2,cw7,cw8])
def mc270 : SearchState := (0,0xfc0fffffffc0000f3cf3cf3cf3cf3cf,[cw67,cw41,cw4,cw3,cw1,cw5,cw2,cw7,cw8])
def mc271 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw41,cw5,cw3,cw1,cw4,cw2,cw7,cw8])
def mc272 : SearchState := (0,0xfff03f03ffc00007df7df7df7df7df7,[cw68,cw41,cw5,cw3,cw1,cw4,cw2,cw7,cw8])
def mc273 : SearchState := (0,0x2082082082082082,[cw69,cw41,cw2,cw3,cw1,cw4,cw5,cw7,cw8])
def mc274 : SearchState := (1,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw2,cw3,cw1,cw4,cw5,cw7,cw8])
def mc275 : SearchState := (0,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw41,cw2,cw3,cw1,cw4,cw5,cw7,cw8])
def mc276 : SearchState := (0,0xfc00000000000000000000,[cw60,cw41,cw7,cw3,cw1,cw4,cw5,cw2,cw8])
def mc277 : SearchState := (0,0xfc0fff03ffc0fc075d75d75d75d75d7,[cw70,cw41,cw7,cw3,cw1,cw4,cw5,cw2,cw8])
def mc278 : SearchState := (0,0x3f0000000000000000000000,[cw53,cw41,cw8,cw3,cw1,cw4,cw5,cw2,cw7])
def mc279 : SearchState := (0,0xfc003f03ffff000fbefbefbefbefbef,[cw71,cw41,cw8,cw3,cw1,cw4,cw5,cw2,cw7])
def mc280 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw41,cw4,cw5,cw2,cw7,cw8])
def mc281 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw3,cw1,cw41,cw4,cw5,cw2,cw7,cw8])
def mc282 : SearchState := (1,0xfff00003ffc00006db6db6db6db6db6,[cw88,cw5,cw41,cw1,cw4,cw2,cw7,cw8])
def mc283 : SearchState := (0,0xfff00003ffc00006db6db6db6db6db6,[cw88,cw3,cw5,cw41,cw1,cw4,cw2,cw7,cw8])
def mc284 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw41,cw1,cw4,cw5,cw7,cw8])
def mc285 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw41,cw1,cw4,cw5,cw7,cw8])
def mc286 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw41,cw1,cw4,cw5,cw7,cw8])
def mc287 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw41,cw1,cw4,cw5,cw7,cw8])
def mc288 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw41,cw3,cw5,cw2,cw7,cw8])
def mc289 : SearchState := (0,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw5,cw41,cw3,cw4,cw2,cw7,cw8])
def mc290 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw41,cw3,cw4,cw5,cw7,cw8])
def mc291 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw41,cw3,cw4,cw5,cw7,cw8])
def mc292 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw41,cw3,cw4,cw5,cw2,cw8])
def mc293 : SearchState := (0,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw1,cw8,cw41,cw3,cw4,cw5,cw2,cw7])
def mc294 : SearchState := (1,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw41,cw3,cw1,cw2,cw7,cw8])
def mc295 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw5,cw41,cw3,cw1,cw2,cw7,cw8])
def mc296 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw41,cw3,cw1,cw5,cw7,cw8])
def mc297 : SearchState := (0,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw2,cw41,cw3,cw1,cw4,cw7,cw8])
def mc298 : SearchState := (2,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw41,cw3,cw1,cw4,cw2,cw8])
def mc299 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw41,cw3,cw1,cw4,cw2,cw8])
def mc300 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw41,cw3,cw1,cw4,cw2,cw8])
def mc301 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw7,cw41,cw3,cw1,cw4,cw2,cw8])
def mc302 : SearchState := (2,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw41,cw3,cw1,cw4,cw2,cw7])
def mc303 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw41,cw3,cw1,cw4,cw2,cw7])
def mc304 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw41,cw3,cw1,cw4,cw2,cw7])
def mc305 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw8,cw41,cw3,cw1,cw4,cw2,cw7])
def mc306 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw41,cw3,cw1,cw4,cw5,cw8])
def mc307 : SearchState := (0,0xf03f000fff03f03faaaaaaaaaaaaaaaa,[cw80,cw2,cw8,cw41,cw3,cw1,cw4,cw5,cw7])
def mc308 : SearchState := (2,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw1,cw4,cw5,cw2,cw7,cw8])
def mc309 : SearchState := (0,0x1041041041041041,[cw66,cw41,cw1,cw6,cw4,cw5,cw2,cw7,cw8])
def mc310 : SearchState := (1,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw1,cw6,cw4,cw5,cw2,cw7,cw8])
def mc311 : SearchState := (0,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw41,cw1,cw6,cw4,cw5,cw2,cw7,cw8])
def mc312 : SearchState := (0,0x3f0000000000000000000000000,[cw22,cw41,cw4,cw6,cw1,cw5,cw2,cw7,cw8])
def mc313 : SearchState := (0,0xfc0fffffffc0000f3cf3cf3cf3cf3cf,[cw67,cw41,cw4,cw6,cw1,cw5,cw2,cw7,cw8])
def mc314 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw41,cw5,cw6,cw1,cw4,cw2,cw7,cw8])
def mc315 : SearchState := (0,0xfff03f03ffc00007df7df7df7df7df7,[cw68,cw41,cw5,cw6,cw1,cw4,cw2,cw7,cw8])
def mc316 : SearchState := (0,0x2082082082082082,[cw69,cw41,cw2,cw6,cw1,cw4,cw5,cw7,cw8])
def mc317 : SearchState := (1,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw2,cw6,cw1,cw4,cw5,cw7,cw8])
def mc318 : SearchState := (0,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw41,cw2,cw6,cw1,cw4,cw5,cw7,cw8])
def mc319 : SearchState := (0,0xfc00000000000000000000,[cw60,cw41,cw7,cw6,cw1,cw4,cw5,cw2,cw8])
def mc320 : SearchState := (0,0xfc0fff03ffc0fc075d75d75d75d75d7,[cw70,cw41,cw7,cw6,cw1,cw4,cw5,cw2,cw8])
def mc321 : SearchState := (0,0x3f0000000000000000000000,[cw53,cw41,cw8,cw6,cw1,cw4,cw5,cw2,cw7])
def mc322 : SearchState := (0,0xfc003f03ffff000fbefbefbefbefbef,[cw71,cw41,cw8,cw6,cw1,cw4,cw5,cw2,cw7])
def mc323 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw41,cw4,cw5,cw2,cw7,cw8])
def mc324 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw41,cw4,cw5,cw2,cw7,cw8])
def mc325 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw41,cw4,cw5,cw2,cw7,cw8])
def mc326 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw1,cw41,cw4,cw5,cw2,cw7,cw8])
def mc327 : SearchState := (1,0xfc0ffffc0000000d34d34d34d34d34d,[cw89,cw4,cw41,cw1,cw5,cw2,cw7,cw8])
def mc328 : SearchState := (0,0xfc0ffffc0000000d34d34d34d34d34d,[cw89,cw6,cw4,cw41,cw1,cw5,cw2,cw7,cw8])
def mc329 : SearchState := (1,0xfff03f0000000005d75d75d75d75d75,[cw90,cw5,cw41,cw1,cw4,cw2,cw7,cw8])
def mc330 : SearchState := (0,0xfff03f0000000005d75d75d75d75d75,[cw90,cw6,cw5,cw41,cw1,cw4,cw2,cw7,cw8])
def mc331 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw41,cw1,cw4,cw5,cw7,cw8])
def mc332 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw6,cw2,cw41,cw1,cw4,cw5,cw7,cw8])
def mc333 : SearchState := (1,0xfc0fff000fc0fc05555555555555555,[cw91,cw7,cw41,cw1,cw4,cw5,cw2,cw8])
def mc334 : SearchState := (0,0xfc0fff000fc0fc05555555555555555,[cw91,cw6,cw7,cw41,cw1,cw4,cw5,cw2,cw8])
def mc335 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw41,cw6,cw5,cw2,cw7,cw8])
def mc336 : SearchState := (0,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw5,cw41,cw6,cw4,cw2,cw7,cw8])
def mc337 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw41,cw6,cw4,cw5,cw7,cw8])
def mc338 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw41,cw6,cw4,cw5,cw7,cw8])
def mc339 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw41,cw6,cw4,cw5,cw2,cw8])
def mc340 : SearchState := (0,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw1,cw8,cw41,cw6,cw4,cw5,cw2,cw7])
def mc341 : SearchState := (1,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw41,cw6,cw1,cw2,cw7,cw8])
def mc342 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw5,cw41,cw6,cw1,cw2,cw7,cw8])
def mc343 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw41,cw6,cw1,cw5,cw7,cw8])
def mc344 : SearchState := (0,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw2,cw41,cw6,cw1,cw4,cw7,cw8])
def mc345 : SearchState := (2,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw41,cw6,cw1,cw4,cw2,cw8])
def mc346 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw41,cw6,cw1,cw4,cw2,cw8])
def mc347 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw41,cw6,cw1,cw4,cw2,cw8])
def mc348 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw7,cw41,cw6,cw1,cw4,cw2,cw8])
def mc349 : SearchState := (2,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw41,cw6,cw1,cw4,cw2,cw7])
def mc350 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw41,cw6,cw1,cw4,cw2,cw7])
def mc351 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw41,cw6,cw1,cw4,cw2,cw7])
def mc352 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw8,cw41,cw6,cw1,cw4,cw2,cw7])
def mc353 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw41,cw6,cw1,cw4,cw5,cw8])
def mc354 : SearchState := (0,0xf03f000fff03f03faaaaaaaaaaaaaaaa,[cw80,cw2,cw8,cw41,cw6,cw1,cw4,cw5,cw7])
def mc355 : SearchState := (1,0xfc00000000000000000000,[cw60,cw3,cw7,cw1,cw4,cw5,cw2,cw6,cw8])
def mc356 : SearchState := (1,0xf000000000ffffff1041041041041041,[cw92,cw3,cw7,cw4,cw5,cw2,cw6,cw8])
def mc357 : SearchState := (0,0xf000000000ffffff1041041041041041,[cw92,cw60,cw3,cw7,cw4,cw5,cw2,cw6,cw8])
def mc358 : SearchState := (0,0xf000000000ffffff1041041041041041,[cw92,cw1,cw3,cw7,cw4,cw5,cw2,cw6,cw8])
def mc359 : SearchState := (1,0xffffc0fc00008208208208208208,[cw93,cw3,cw7,cw1,cw5,cw2,cw6,cw8])
def mc360 : SearchState := (0,0xffffc0fc00008208208208208208,[cw93,cw60,cw3,cw7,cw1,cw5,cw2,cw6,cw8])
def mc361 : SearchState := (0,0xffffc0fc00008208208208208208,[cw93,cw4,cw3,cw7,cw1,cw5,cw2,cw6,cw8])
def mc362 : SearchState := (1,0xfff000000fc00000c30c30c30c30c30,[cw94,cw3,cw7,cw1,cw4,cw2,cw6,cw8])
def mc363 : SearchState := (0,0xfff000000fc00000c30c30c30c30c30,[cw94,cw60,cw3,cw7,cw1,cw4,cw2,cw6,cw8])
def mc364 : SearchState := (0,0xfff000000fc00000c30c30c30c30c30,[cw94,cw5,cw3,cw7,cw1,cw4,cw2,cw6,cw8])
def mc365 : SearchState := (1,0xf03f000fc0fc003f2082082082082082,[cw95,cw3,cw7,cw1,cw4,cw5,cw6,cw8])
def mc366 : SearchState := (0,0xf03f000fc0fc003f2082082082082082,[cw95,cw60,cw3,cw7,cw1,cw4,cw5,cw6,cw8])
def mc367 : SearchState := (0,0xf03f000fc0fc003f2082082082082082,[cw95,cw2,cw3,cw7,cw1,cw4,cw5,cw6,cw8])
def mc368 : SearchState := (1,0xfc003f000fc00005145145145145145,[cw96,cw3,cw7,cw1,cw4,cw5,cw2,cw8])
def mc369 : SearchState := (0,0xfc003f000fc00005145145145145145,[cw96,cw60,cw3,cw7,cw1,cw4,cw5,cw2,cw8])
def mc370 : SearchState := (0,0xfc003f000fc00005145145145145145,[cw96,cw6,cw3,cw7,cw1,cw4,cw5,cw2,cw8])
def mc371 : SearchState := (1,0x3ffff0008a28a28a28a28a28,[cw97,cw3,cw7,cw1,cw4,cw5,cw2,cw6])
def mc372 : SearchState := (0,0x3ffff0008a28a28a28a28a28,[cw97,cw60,cw3,cw7,cw1,cw4,cw5,cw2,cw6])
def mc373 : SearchState := (0,0x3ffff0008a28a28a28a28a28,[cw97,cw8,cw3,cw7,cw1,cw4,cw5,cw2,cw6])
def mc374 : SearchState := (1,0xfc003ffc0fc06596596596596596,[cw98,cw60,cw1,cw4,cw5,cw2,cw6,cw8])
def mc375 : SearchState := (0,0xfc003ffc0fc06596596596596596,[cw98,cw3,cw60,cw1,cw4,cw5,cw2,cw6,cw8])
def mc376 : SearchState := (0,0xfc003ffc0fc06596596596596596,[cw98,cw7,cw60,cw1,cw4,cw5,cw2,cw6,cw8])
def mc377 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw60,cw7,cw4,cw5,cw2,cw6,cw8])
def mc378 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw60,cw7,cw1,cw4,cw5,cw6,cw8])
def mc379 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw60,cw7,cw1,cw4,cw5,cw6,cw8])
def mc380 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw60,cw7,cw1,cw4,cw5,cw6,cw8])
def mc381 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw60,cw7,cw1,cw4,cw5,cw2,cw8])
def mc382 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw60,cw7,cw1,cw4,cw5,cw2,cw8])
def mc383 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw60,cw7,cw1,cw4,cw5,cw2,cw8])
def mc384 : SearchState := (0,0x3f0000000000000000000000,[cw53,cw8,cw60,cw7,cw1,cw4,cw5,cw2,cw6])
def mc385 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw60,cw3,cw1,cw4,cw2,cw6,cw8])
def mc386 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw60,cw3,cw1,cw4,cw2,cw6,cw8])
def mc387 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw60,cw3,cw1,cw4,cw2,cw6,cw8])
def mc388 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw60,cw3,cw1,cw4,cw5,cw6,cw8])
def mc389 : SearchState := (0,0xfc003fffffc08e38e38e38e38e38,[cw40,cw7,cw60,cw3,cw1,cw4,cw5,cw2,cw6])
def mc390 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw60,cw3,cw7,cw4,cw5,cw2,cw8])
def mc391 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw60,cw3,cw7,cw4,cw5,cw2,cw8])
def mc392 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw60,cw3,cw7,cw4,cw5,cw2,cw8])
def mc393 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw60,cw3,cw7,cw1,cw2,cw6,cw8])
def mc394 : SearchState := (1,0xffffff03f0008a28a28a28a28a28,[cw43,cw60,cw3,cw7,cw1,cw5,cw2,cw6])
def mc395 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw4,cw60,cw3,cw7,cw1,cw5,cw2,cw6])
def mc396 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw8,cw60,cw3,cw7,cw1,cw5,cw2,cw6])
def mc397 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw60,cw3,cw7,cw1,cw4,cw2,cw6])
def mc398 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw60,cw3,cw7,cw1,cw4,cw2,cw6])
def mc399 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw60,cw3,cw7,cw1,cw4,cw2,cw6])
def mc400 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw60,cw3,cw7,cw1,cw4,cw5,cw8])
def mc401 : SearchState := (1,0x3f0000000000000000000000,[cw53,cw3,cw8,cw1,cw4,cw5,cw2,cw6,cw7])
def mc402 : SearchState := (1,0xf00000003f03ffff1041041041041041,[cw99,cw3,cw8,cw4,cw5,cw2,cw6,cw7])
def mc403 : SearchState := (0,0xf00000003f03ffff1041041041041041,[cw99,cw53,cw3,cw8,cw4,cw5,cw2,cw6,cw7])
def mc404 : SearchState := (0,0xf00000003f03ffff1041041041041041,[cw99,cw1,cw3,cw8,cw4,cw5,cw2,cw6,cw7])
def mc405 : SearchState := (1,0xffffff0000008208208208208208,[cw100,cw3,cw8,cw1,cw5,cw2,cw6,cw7])
def mc406 : SearchState := (0,0xffffff0000008208208208208208,[cw100,cw53,cw3,cw8,cw1,cw5,cw2,cw6,cw7])
def mc407 : SearchState := (0,0xffffff0000008208208208208208,[cw100,cw4,cw3,cw8,cw1,cw5,cw2,cw6,cw7])
def mc408 : SearchState := (1,0xfff00003f0000000c30c30c30c30c30,[cw101,cw3,cw8,cw1,cw4,cw2,cw6,cw7])
def mc409 : SearchState := (0,0xfff00003f0000000c30c30c30c30c30,[cw101,cw53,cw3,cw8,cw1,cw4,cw2,cw6,cw7])
def mc410 : SearchState := (0,0xfff00003f0000000c30c30c30c30c30,[cw101,cw5,cw3,cw8,cw1,cw4,cw2,cw6,cw7])
def mc411 : SearchState := (1,0xf03f000fff00003f2082082082082082,[cw102,cw3,cw8,cw1,cw4,cw5,cw6,cw7])
def mc412 : SearchState := (0,0xf03f000fff00003f2082082082082082,[cw102,cw53,cw3,cw8,cw1,cw4,cw5,cw6,cw7])
def mc413 : SearchState := (0,0xf03f000fff00003f2082082082082082,[cw102,cw2,cw3,cw8,cw1,cw4,cw5,cw6,cw7])
def mc414 : SearchState := (1,0xfc003f03f0000005145145145145145,[cw103,cw3,cw8,cw1,cw4,cw5,cw2,cw7])
def mc415 : SearchState := (0,0xfc003f03f0000005145145145145145,[cw103,cw53,cw3,cw8,cw1,cw4,cw5,cw2,cw7])
def mc416 : SearchState := (0,0xfc003f03f0000005145145145145145,[cw103,cw6,cw3,cw8,cw1,cw4,cw5,cw2,cw7])
def mc417 : SearchState := (1,0xfc003ffc0fc00410410410410410,[cw104,cw3,cw8,cw1,cw4,cw5,cw2,cw6])
def mc418 : SearchState := (0,0xfc003ffc0fc00410410410410410,[cw104,cw53,cw3,cw8,cw1,cw4,cw5,cw2,cw6])
def mc419 : SearchState := (0,0xfc003ffc0fc00410410410410410,[cw104,cw7,cw3,cw8,cw1,cw4,cw5,cw2,cw6])
def mc420 : SearchState := (1,0x3ffff000ebaebaebaebaebae,[cw105,cw53,cw1,cw4,cw5,cw2,cw6,cw7])
def mc421 : SearchState := (0,0x3ffff000ebaebaebaebaebae,[cw105,cw3,cw53,cw1,cw4,cw5,cw2,cw6,cw7])
def mc422 : SearchState := (0,0x3ffff000ebaebaebaebaebae,[cw105,cw8,cw53,cw1,cw4,cw5,cw2,cw6,cw7])
def mc423 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw53,cw8,cw4,cw5,cw2,cw6,cw7])
def mc424 : SearchState := (0,0xfffffffc0000e38e38e38e38e38e,[cw106,cw4,cw53,cw8,cw1,cw5,cw2,cw6,cw7])
def mc425 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw53,cw8,cw1,cw4,cw5,cw6,cw7])
def mc426 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw53,cw8,cw1,cw4,cw5,cw6,cw7])
def mc427 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw53,cw8,cw1,cw4,cw5,cw6,cw7])
def mc428 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw53,cw8,cw1,cw4,cw5,cw2,cw7])
def mc429 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw53,cw8,cw1,cw4,cw5,cw2,cw7])
def mc430 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw53,cw8,cw1,cw4,cw5,cw2,cw7])
def mc431 : SearchState := (1,0xffffff03f0008a28a28a28a28a28,[cw43,cw53,cw3,cw1,cw5,cw2,cw6,cw7])
def mc432 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw8,cw53,cw3,cw1,cw5,cw2,cw6,cw7])
def mc433 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw4,cw53,cw3,cw1,cw5,cw2,cw6,cw7])
def mc434 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw53,cw3,cw1,cw4,cw2,cw6,cw7])
def mc435 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw53,cw3,cw1,cw4,cw2,cw6,cw7])
def mc436 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw53,cw3,cw1,cw4,cw2,cw6,cw7])
def mc437 : SearchState := (0,0xf03f000fff03f03faaaaaaaaaaaaaaaa,[cw80,cw2,cw53,cw3,cw1,cw4,cw5,cw6,cw7])
def mc438 : SearchState := (0,0xfc003fffffc08e38e38e38e38e38,[cw40,cw7,cw53,cw3,cw1,cw4,cw5,cw2,cw6])
def mc439 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw53,cw3,cw8,cw4,cw5,cw2,cw7])
def mc440 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw53,cw3,cw8,cw4,cw5,cw2,cw7])
def mc441 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw53,cw3,cw8,cw4,cw5,cw2,cw7])
def mc442 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw53,cw3,cw8,cw1,cw2,cw6,cw7])
def mc443 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw53,cw3,cw8,cw1,cw4,cw2,cw6])
def mc444 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw53,cw3,cw8,cw1,cw4,cw2,cw6])
def mc445 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw53,cw3,cw8,cw1,cw4,cw2,cw6])
def mc446 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw53,cw3,cw8,cw1,cw4,cw5,cw7])
def mc447 : SearchState := (2,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw1,cw3,cw2,cw6,cw7,cw8])
def mc448 : SearchState := (0,0xffffffffc003ffff9e79e79e79e79e79,[cw107,cw42,cw1,cw4,cw3,cw2,cw6,cw7,cw8])
def mc449 : SearchState := (0,0xffffffffffc0000efbefbefbefbefbe,[cw108,cw42,cw3,cw4,cw1,cw2,cw6,cw7,cw8])
def mc450 : SearchState := (0,0x3f000fc00000000000000000000000,[cw109,cw42,cw2,cw4,cw1,cw3,cw6,cw7,cw8])
def mc451 : SearchState := (0,0xffffffffc000003faebaebaebaebaeba,[cw110,cw42,cw2,cw4,cw1,cw3,cw6,cw7,cw8])
def mc452 : SearchState := (1,0xfc003f0000000000000000000000000,[cw111,cw42,cw4,cw1,cw3,cw2,cw7,cw8])
def mc453 : SearchState := (0,0xfc003f0000000000000000000000000,[cw111,cw42,cw6,cw4,cw1,cw3,cw2,cw7,cw8])
def mc454 : SearchState := (0,0xfffffffc0000000df7df7df7df7df7d,[cw112,cw42,cw6,cw4,cw1,cw3,cw2,cw7,cw8])
def mc455 : SearchState := (0,0xfc00000000000410410410410410,[cw113,cw42,cw7,cw4,cw1,cw3,cw2,cw6,cw8])
def mc456 : SearchState := (1,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw7,cw4,cw1,cw3,cw2,cw6,cw8])
def mc457 : SearchState := (0,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw42,cw7,cw4,cw1,cw3,cw2,cw6,cw8])
def mc458 : SearchState := (0,0x8a28a28a28a28a28,[cw114,cw42,cw8,cw4,cw1,cw3,cw2,cw6,cw7])
def mc459 : SearchState := (2,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw4,cw1,cw3,cw2,cw6,cw7])
def mc460 : SearchState := (1,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw42,cw4,cw1,cw3,cw2,cw6,cw7])
def mc461 : SearchState := (1,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw8,cw4,cw1,cw3,cw2,cw6,cw7])
def mc462 : SearchState := (0,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw42,cw8,cw4,cw1,cw3,cw2,cw6,cw7])
def mc463 : SearchState := (1,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw42,cw3,cw2,cw6,cw7,cw8])
def mc464 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw4,cw1,cw42,cw3,cw2,cw6,cw7,cw8])
def mc465 : SearchState := (1,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw2,cw42,cw1,cw3,cw6,cw7,cw8])
def mc466 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw42,cw1,cw3,cw6,cw7,cw8])
def mc467 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw42,cw4,cw2,cw6,cw7,cw8])
def mc468 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw42,cw4,cw2,cw6,cw7,cw8])
def mc469 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw42,cw4,cw3,cw6,cw7,cw8])
def mc470 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw42,cw4,cw3,cw6,cw7,cw8])
def mc471 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw42,cw4,cw3,cw2,cw7,cw8])
def mc472 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw42,cw4,cw3,cw2,cw7,cw8])
def mc473 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw42,cw4,cw3,cw2,cw7,cw8])
def mc474 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw42,cw4,cw3,cw2,cw7,cw8])
def mc475 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw42,cw4,cw3,cw2,cw6,cw8])
def mc476 : SearchState := (0,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw1,cw8,cw42,cw4,cw3,cw2,cw6,cw7])
def mc477 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw42,cw4,cw1,cw6,cw7,cw8])
def mc478 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw42,cw4,cw1,cw6,cw7,cw8])
def mc479 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw42,cw4,cw1,cw6,cw7,cw8])
def mc480 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw42,cw4,cw1,cw6,cw7,cw8])
def mc481 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw42,cw4,cw1,cw3,cw7,cw8])
def mc482 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw42,cw4,cw1,cw3,cw7,cw8])
def mc483 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw42,cw4,cw1,cw3,cw6,cw8])
def mc484 : SearchState := (0,0xf03f000fff03f03faaaaaaaaaaaaaaaa,[cw80,cw2,cw8,cw42,cw4,cw1,cw3,cw6,cw7])
def mc485 : SearchState := (1,0xfc00000000000000000000000,[cw55,cw4,cw2,cw1,cw3,cw5,cw6,cw7,cw8])
def mc486 : SearchState := (1,0xf000000fc003ffff1041041041041041,[cw115,cw4,cw2,cw3,cw5,cw6,cw7,cw8])
def mc487 : SearchState := (0,0xf000000fc003ffff1041041041041041,[cw115,cw55,cw4,cw2,cw3,cw5,cw6,cw7,cw8])
def mc488 : SearchState := (0,0xf000000fc003ffff1041041041041041,[cw115,cw1,cw4,cw2,cw3,cw5,cw6,cw7,cw8])
def mc489 : SearchState := (1,0xffffc00006186186186186186,[cw116,cw4,cw2,cw1,cw5,cw6,cw7,cw8])
def mc490 : SearchState := (0,0xffffc00006186186186186186,[cw116,cw55,cw4,cw2,cw1,cw5,cw6,cw7,cw8])
def mc491 : SearchState := (0,0xffffc00006186186186186186,[cw116,cw3,cw4,cw2,cw1,cw5,cw6,cw7,cw8])
def mc492 : SearchState := (1,0xfff000fc00000000c30c30c30c30c30,[cw117,cw4,cw2,cw1,cw3,cw6,cw7,cw8])
def mc493 : SearchState := (0,0xfff000fc00000000c30c30c30c30c30,[cw117,cw55,cw4,cw2,cw1,cw3,cw6,cw7,cw8])
def mc494 : SearchState := (0,0xfff000fc00000000c30c30c30c30c30,[cw117,cw5,cw4,cw2,cw1,cw3,cw6,cw7,cw8])
def mc495 : SearchState := (1,0xfc003ffc00000005145145145145145,[cw118,cw4,cw2,cw1,cw3,cw5,cw7,cw8])
def mc496 : SearchState := (0,0xfc003ffc00000005145145145145145,[cw118,cw55,cw4,cw2,cw1,cw3,cw5,cw7,cw8])
def mc497 : SearchState := (0,0xfc003ffc00000005145145145145145,[cw118,cw6,cw4,cw2,cw1,cw3,cw5,cw7,cw8])
def mc498 : SearchState := (1,0xfc0fc0fc0fc00410410410410410,[cw119,cw4,cw2,cw1,cw3,cw5,cw6,cw8])
def mc499 : SearchState := (0,0xfc0fc0fc0fc00410410410410410,[cw119,cw55,cw4,cw2,cw1,cw3,cw5,cw6,cw8])
def mc500 : SearchState := (0,0xfc0fc0fc0fc00410410410410410,[cw119,cw7,cw4,cw2,cw1,cw3,cw5,cw6,cw8])
def mc501 : SearchState := (1,0xfff03f0008a28a28a28a28a28,[cw120,cw4,cw2,cw1,cw3,cw5,cw6,cw7])
def mc502 : SearchState := (0,0xfff03f0008a28a28a28a28a28,[cw120,cw55,cw4,cw2,cw1,cw3,cw5,cw6,cw7])
def mc503 : SearchState := (0,0xfff03f0008a28a28a28a28a28,[cw120,cw8,cw4,cw2,cw1,cw3,cw5,cw6,cw7])
def mc504 : SearchState := (1,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw55,cw1,cw3,cw5,cw6,cw7,cw8])
def mc505 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw55,cw1,cw3,cw5,cw6,cw7,cw8])
def mc506 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw2,cw55,cw1,cw3,cw5,cw6,cw7,cw8])
def mc507 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw55,cw2,cw1,cw3,cw6,cw7,cw8])
def mc508 : SearchState := (1,0xffffff03f0008a28a28a28a28a28,[cw43,cw55,cw2,cw1,cw3,cw5,cw6,cw7])
def mc509 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw4,cw55,cw2,cw1,cw3,cw5,cw6,cw7])
def mc510 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw8,cw55,cw2,cw1,cw3,cw5,cw6,cw7])
def mc511 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw55,cw4,cw1,cw5,cw6,cw7,cw8])
def mc512 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw55,cw4,cw1,cw5,cw6,cw7,cw8])
def mc513 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw55,cw4,cw1,cw5,cw6,cw7,cw8])
def mc514 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw55,cw4,cw1,cw3,cw5,cw7,cw8])
def mc515 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw55,cw4,cw2,cw5,cw6,cw7,cw8])
def mc516 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw55,cw4,cw2,cw3,cw5,cw7,cw8])
def mc517 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw55,cw4,cw2,cw3,cw5,cw7,cw8])
def mc518 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw55,cw4,cw2,cw3,cw5,cw7,cw8])
def mc519 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw55,cw4,cw2,cw1,cw5,cw7,cw8])
def mc520 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw55,cw4,cw2,cw1,cw5,cw7,cw8])
def mc521 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw55,cw4,cw2,cw1,cw5,cw7,cw8])
def mc522 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw55,cw4,cw2,cw1,cw3,cw6,cw8])
def mc523 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw55,cw4,cw2,cw1,cw3,cw6,cw8])
def mc524 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw55,cw4,cw2,cw1,cw3,cw6,cw8])
def mc525 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw55,cw4,cw2,cw1,cw3,cw6,cw7])
def mc526 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw55,cw4,cw2,cw1,cw3,cw6,cw7])
def mc527 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw55,cw4,cw2,cw1,cw3,cw6,cw7])
def mc528 : SearchState := (0,0xfc003fffffc08e38e38e38e38e38,[cw40,cw7,cw55,cw4,cw2,cw1,cw3,cw5,cw6])
def mc529 : SearchState := (1,0x3f0000000000000000000000000,[cw22,cw4,cw6,cw1,cw3,cw5,cw2,cw7,cw8])
def mc530 : SearchState := (1,0xf00003f00003ffff1041041041041041,[cw121,cw4,cw6,cw3,cw5,cw2,cw7,cw8])
def mc531 : SearchState := (0,0xf00003f00003ffff1041041041041041,[cw121,cw22,cw4,cw6,cw3,cw5,cw2,cw7,cw8])
def mc532 : SearchState := (0,0xf00003f00003ffff1041041041041041,[cw121,cw1,cw4,cw6,cw3,cw5,cw2,cw7,cw8])
def mc533 : SearchState := (1,0x3f03ffc00006186186186186186,[cw122,cw4,cw6,cw1,cw5,cw2,cw7,cw8])
def mc534 : SearchState := (0,0x3f03ffc00006186186186186186,[cw122,cw22,cw4,cw6,cw1,cw5,cw2,cw7,cw8])
def mc535 : SearchState := (0,0x3f03ffc00006186186186186186,[cw122,cw3,cw4,cw6,cw1,cw5,cw2,cw7,cw8])
def mc536 : SearchState := (1,0xfff03f0000000000c30c30c30c30c30,[cw123,cw4,cw6,cw1,cw3,cw2,cw7,cw8])
def mc537 : SearchState := (0,0xfff03f0000000000c30c30c30c30c30,[cw123,cw22,cw4,cw6,cw1,cw3,cw2,cw7,cw8])
def mc538 : SearchState := (0,0xfff03f0000000000c30c30c30c30c30,[cw123,cw5,cw4,cw6,cw1,cw3,cw2,cw7,cw8])
def mc539 : SearchState := (1,0xf03f03ffc000003f2082082082082082,[cw124,cw4,cw6,cw1,cw3,cw5,cw7,cw8])
def mc540 : SearchState := (0,0xf03f03ffc000003f2082082082082082,[cw124,cw22,cw4,cw6,cw1,cw3,cw5,cw7,cw8])
def mc541 : SearchState := (0,0xf03f03ffc000003f2082082082082082,[cw124,cw2,cw4,cw6,cw1,cw3,cw5,cw7,cw8])
def mc542 : SearchState := (1,0xfff000fc0fc00410410410410410,[cw125,cw4,cw6,cw1,cw3,cw5,cw2,cw8])
def mc543 : SearchState := (0,0xfff000fc0fc00410410410410410,[cw125,cw22,cw4,cw6,cw1,cw3,cw5,cw2,cw8])
def mc544 : SearchState := (0,0xfff000fc0fc00410410410410410,[cw125,cw7,cw4,cw6,cw1,cw3,cw5,cw2,cw8])
def mc545 : SearchState := (1,0x3f03f03f0008a28a28a28a28a28,[cw126,cw4,cw6,cw1,cw3,cw5,cw2,cw7])
def mc546 : SearchState := (0,0x3f03f03f0008a28a28a28a28a28,[cw126,cw22,cw4,cw6,cw1,cw3,cw5,cw2,cw7])
def mc547 : SearchState := (0,0x3f03f03f0008a28a28a28a28a28,[cw126,cw8,cw4,cw6,cw1,cw3,cw5,cw2,cw7])
def mc548 : SearchState := (1,0xfc0ffffc0000000d34d34d34d34d34d,[cw89,cw22,cw1,cw3,cw5,cw2,cw7,cw8])
def mc549 : SearchState := (0,0xfc0ffffc0000000d34d34d34d34d34d,[cw89,cw4,cw22,cw1,cw3,cw5,cw2,cw7,cw8])
def mc550 : SearchState := (0,0xfc0ffffc0000000d34d34d34d34d34d,[cw89,cw6,cw22,cw1,cw3,cw5,cw2,cw7,cw8])
def mc551 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw22,cw6,cw3,cw5,cw2,cw7,cw8])
def mc552 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw22,cw6,cw1,cw3,cw2,cw7,cw8])
def mc553 : SearchState := (1,0xffffff03f0008a28a28a28a28a28,[cw43,cw22,cw6,cw1,cw3,cw5,cw2,cw7])
def mc554 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw4,cw22,cw6,cw1,cw3,cw5,cw2,cw7])
def mc555 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw8,cw22,cw6,cw1,cw3,cw5,cw2,cw7])
def mc556 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw22,cw4,cw3,cw5,cw2,cw7,cw8])
def mc557 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw22,cw4,cw3,cw5,cw2,cw7,cw8])
def mc558 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw22,cw4,cw3,cw5,cw2,cw7,cw8])
def mc559 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw22,cw4,cw1,cw5,cw2,cw7,cw8])
def mc560 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw22,cw4,cw1,cw5,cw2,cw7,cw8])
def mc561 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw22,cw4,cw1,cw5,cw2,cw7,cw8])
def mc562 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw5,cw22,cw4,cw1,cw3,cw2,cw7,cw8])
def mc563 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw22,cw4,cw1,cw3,cw5,cw7,cw8])
def mc564 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw22,cw4,cw6,cw5,cw2,cw7,cw8])
def mc565 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw22,cw4,cw6,cw1,cw5,cw7,cw8])
def mc566 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw22,cw4,cw6,cw1,cw5,cw7,cw8])
def mc567 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw22,cw4,cw6,cw1,cw5,cw7,cw8])
def mc568 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw22,cw4,cw6,cw1,cw3,cw2,cw8])
def mc569 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw22,cw4,cw6,cw1,cw3,cw2,cw8])
def mc570 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw22,cw4,cw6,cw1,cw3,cw2,cw8])
def mc571 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw22,cw4,cw6,cw1,cw3,cw2,cw7])
def mc572 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw22,cw4,cw6,cw1,cw3,cw2,cw7])
def mc573 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw22,cw4,cw6,cw1,cw3,cw2,cw7])
def mc574 : SearchState := (0,0xfc003fffffc08e38e38e38e38e38,[cw40,cw7,cw22,cw4,cw6,cw1,cw3,cw5,cw2])
def mc575 : SearchState := (1,0xfc00000000000000000000000000,[cw75,cw4,cw7,cw1,cw3,cw5,cw2,cw6,cw8])
def mc576 : SearchState := (1,0xf000fc000003ffff1041041041041041,[cw127,cw4,cw7,cw3,cw5,cw2,cw6,cw8])
def mc577 : SearchState := (0,0xf000fc000003ffff1041041041041041,[cw127,cw75,cw4,cw7,cw3,cw5,cw2,cw6,cw8])
def mc578 : SearchState := (0,0xf000fc000003ffff1041041041041041,[cw127,cw1,cw4,cw7,cw3,cw5,cw2,cw6,cw8])
def mc579 : SearchState := (1,0xfc003ffc00006186186186186186,[cw128,cw4,cw7,cw1,cw5,cw2,cw6,cw8])
def mc580 : SearchState := (0,0xf000fc003fffffff71c71c71c71c71c7,[cw129,cw1,cw4,cw7,cw5,cw2,cw6,cw8])
def mc581 : SearchState := (1,0xf03ffc0ffffc003f6186186186186186,[cw130,cw4,cw7,cw1,cw5,cw6,cw8])
def mc582 : SearchState := (0,0xf03ffc0ffffc003f6186186186186186,[cw130,cw128,cw4,cw7,cw1,cw5,cw6,cw8])
def mc583 : SearchState := (0,0xf03ffc0ffffc003f6186186186186186,[cw130,cw2,cw4,cw7,cw1,cw5,cw6,cw8])
def mc584 : SearchState := (1,0xfc0fff03ffc000071c71c71c71c71c7,[cw131,cw4,cw7,cw1,cw5,cw2,cw8])
def mc585 : SearchState := (0,0xfc0fff03ffc000071c71c71c71c71c7,[cw131,cw128,cw4,cw7,cw1,cw5,cw2,cw8])
def mc586 : SearchState := (0,0xfc0fff03ffc000071c71c71c71c71c7,[cw131,cw6,cw4,cw7,cw1,cw5,cw2,cw8])
def mc587 : SearchState := (1,0xffffc0fc0fc08618618618618618,[cw132,cw128,cw1,cw5,cw2,cw6,cw8])
def mc588 : SearchState := (0,0xffffc0fc0fc08618618618618618,[cw132,cw4,cw128,cw1,cw5,cw2,cw6,cw8])
def mc589 : SearchState := (0,0xffffc0fc0fc08618618618618618,[cw132,cw7,cw128,cw1,cw5,cw2,cw6,cw8])
def mc590 : SearchState := (1,0xfffffffc00000008e38e38e38e38e38,[cw42,cw128,cw7,cw1,cw2,cw6,cw8])
def mc591 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw128,cw7,cw1,cw2,cw6,cw8])
def mc592 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw5,cw128,cw7,cw1,cw2,cw6,cw8])
def mc593 : SearchState := (1,0xffffff03f0008a28a28a28a28a28,[cw43,cw128,cw7,cw1,cw5,cw2,cw6])
def mc594 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw4,cw128,cw7,cw1,cw5,cw2,cw6])
def mc595 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw8,cw128,cw7,cw1,cw5,cw2,cw6])
def mc596 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw128,cw4,cw1,cw2,cw6,cw8])
def mc597 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw128,cw4,cw1,cw2,cw6,cw8])
def mc598 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw128,cw4,cw1,cw2,cw6,cw8])
def mc599 : SearchState := (1,0xfc003fffffc08e38e38e38e38e38,[cw40,cw128,cw4,cw1,cw5,cw2,cw6])
def mc600 : SearchState := (0,0xfc003fffffc08e38e38e38e38e38,[cw40,cw7,cw128,cw4,cw1,cw5,cw2,cw6])
def mc601 : SearchState := (0,0xfc003fffffc08e38e38e38e38e38,[cw40,cw8,cw128,cw4,cw1,cw5,cw2,cw6])
def mc602 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw128,cw4,cw7,cw5,cw2,cw8])
def mc603 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw128,cw4,cw7,cw5,cw2,cw8])
def mc604 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw128,cw4,cw7,cw5,cw2,cw8])
def mc605 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw128,cw4,cw7,cw1,cw2,cw6])
def mc606 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw128,cw4,cw7,cw1,cw2,cw6])
def mc607 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw128,cw4,cw7,cw1,cw2,cw6])
def mc608 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw128,cw4,cw7,cw1,cw5,cw8])
def mc609 : SearchState := (0,0xfc003ffc00006186186186186186,[cw128,cw75,cw4,cw7,cw1,cw5,cw2,cw6,cw8])
def mc610 : SearchState := (0,0xfc003ffc00006186186186186186,[cw128,cw3,cw4,cw7,cw1,cw5,cw2,cw6,cw8])
def mc611 : SearchState := (1,0xffffc00000000000c30c30c30c30c30,[cw133,cw4,cw7,cw1,cw3,cw2,cw6,cw8])
def mc612 : SearchState := (0,0xffffc00000000000c30c30c30c30c30,[cw133,cw75,cw4,cw7,cw1,cw3,cw2,cw6,cw8])
def mc613 : SearchState := (0,0xffffc00000000000c30c30c30c30c30,[cw133,cw5,cw4,cw7,cw1,cw3,cw2,cw6,cw8])
def mc614 : SearchState := (1,0xf03ffc0fc000003f2082082082082082,[cw134,cw4,cw7,cw1,cw3,cw5,cw6,cw8])
def mc615 : SearchState := (0,0xf03ffc0fc000003f2082082082082082,[cw134,cw75,cw4,cw7,cw1,cw3,cw5,cw6,cw8])
def mc616 : SearchState := (0,0xf03ffc0fc000003f2082082082082082,[cw134,cw2,cw4,cw7,cw1,cw3,cw5,cw6,cw8])
def mc617 : SearchState := (1,0xfc0fff0000000005145145145145145,[cw135,cw4,cw7,cw1,cw3,cw5,cw2,cw8])
def mc618 : SearchState := (0,0xfc0fff0000000005145145145145145,[cw135,cw75,cw4,cw7,cw1,cw3,cw5,cw2,cw8])
def mc619 : SearchState := (0,0xfc0fff0000000005145145145145145,[cw135,cw6,cw4,cw7,cw1,cw3,cw5,cw2,cw8])
def mc620 : SearchState := (1,0xfc003f03f0008a28a28a28a28a28,[cw136,cw4,cw7,cw1,cw3,cw5,cw2,cw6])
def mc621 : SearchState := (0,0xfc003f03f0008a28a28a28a28a28,[cw136,cw75,cw4,cw7,cw1,cw3,cw5,cw2,cw6])
def mc622 : SearchState := (0,0xfc003f03f0008a28a28a28a28a28,[cw136,cw8,cw4,cw7,cw1,cw3,cw5,cw2,cw6])
def mc623 : SearchState := (1,0xffffc0fc0fc08618618618618618,[cw132,cw75,cw1,cw3,cw5,cw2,cw6,cw8])
def mc624 : SearchState := (1,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw75,cw1,cw3,cw2,cw6,cw8])
def mc625 : SearchState := (0,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw132,cw75,cw1,cw3,cw2,cw6,cw8])
def mc626 : SearchState := (0,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw5,cw75,cw1,cw3,cw2,cw6,cw8])
def mc627 : SearchState := (1,0xffffffffffc08e38e38e38e38e38,[cw137,cw75,cw1,cw3,cw5,cw2,cw6])
def mc628 : SearchState := (0,0xffffffffffc08e38e38e38e38e38,[cw137,cw132,cw75,cw1,cw3,cw5,cw2,cw6])
def mc629 : SearchState := (0,0xffffffffffc08e38e38e38e38e38,[cw137,cw8,cw75,cw1,cw3,cw5,cw2,cw6])
def mc630 : SearchState := (1,0xf000fc000003ffff1041041041041041,[cw127,cw132,cw3,cw5,cw2,cw6,cw8])
def mc631 : SearchState := (0,0xf000fc000003ffff1041041041041041,[cw127,cw75,cw132,cw3,cw5,cw2,cw6,cw8])
def mc632 : SearchState := (0,0xf000fc000003ffff1041041041041041,[cw127,cw1,cw132,cw3,cw5,cw2,cw6,cw8])
def mc633 : SearchState := (0,0xffffc00000000000c30c30c30c30c30,[cw133,cw75,cw132,cw1,cw3,cw2,cw6,cw8])
def mc634 : SearchState := (1,0xf03ffc0fc000003f2082082082082082,[cw134,cw132,cw1,cw3,cw5,cw6,cw8])
def mc635 : SearchState := (0,0xf03ffc0fc000003f2082082082082082,[cw134,cw75,cw132,cw1,cw3,cw5,cw6,cw8])
def mc636 : SearchState := (0,0xf03ffc0fc000003f2082082082082082,[cw134,cw2,cw132,cw1,cw3,cw5,cw6,cw8])
def mc637 : SearchState := (1,0xfc0fff0000000005145145145145145,[cw135,cw132,cw1,cw3,cw5,cw2,cw8])
def mc638 : SearchState := (0,0xfc0fff0000000005145145145145145,[cw135,cw75,cw132,cw1,cw3,cw5,cw2,cw8])
def mc639 : SearchState := (0,0xfc0fff0000000005145145145145145,[cw135,cw6,cw132,cw1,cw3,cw5,cw2,cw8])
def mc640 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw132,cw75,cw5,cw2,cw6,cw8])
def mc641 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw132,cw75,cw3,cw5,cw2,cw8])
def mc642 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw132,cw75,cw3,cw5,cw2,cw8])
def mc643 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw132,cw75,cw3,cw5,cw2,cw8])
def mc644 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw132,cw75,cw1,cw5,cw6,cw8])
def mc645 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw132,cw75,cw1,cw5,cw6,cw8])
def mc646 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw132,cw75,cw1,cw5,cw6,cw8])
def mc647 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw132,cw75,cw1,cw5,cw2,cw8])
def mc648 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw132,cw75,cw1,cw5,cw2,cw8])
def mc649 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw132,cw75,cw1,cw5,cw2,cw8])
def mc650 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw132,cw75,cw1,cw3,cw2,cw6])
def mc651 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw132,cw75,cw1,cw3,cw2,cw6])
def mc652 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw132,cw75,cw1,cw3,cw2,cw6])
def mc653 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw132,cw75,cw1,cw3,cw5,cw8])
def mc654 : SearchState := (0,0xffffc0fc0fc08618618618618618,[cw132,cw4,cw75,cw1,cw3,cw5,cw2,cw6,cw8])
def mc655 : SearchState := (0,0xffffc0fc0fc08618618618618618,[cw132,cw7,cw75,cw1,cw3,cw5,cw2,cw6,cw8])
def mc656 : SearchState := (1,0xfffffffc00000008e38e38e38e38e38,[cw42,cw75,cw7,cw1,cw3,cw2,cw6,cw8])
def mc657 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw75,cw7,cw1,cw3,cw2,cw6,cw8])
def mc658 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw5,cw75,cw7,cw1,cw3,cw2,cw6,cw8])
def mc659 : SearchState := (1,0xffffff03f0008a28a28a28a28a28,[cw43,cw75,cw7,cw1,cw3,cw5,cw2,cw6])
def mc660 : SearchState := (0,0xffffffffffc08e38e38e38e38e38,[cw137,cw43,cw75,cw1,cw3,cw5,cw2,cw6])
def mc661 : SearchState := (0,0xffffffffffc08e38e38e38e38e38,[cw137,cw7,cw75,cw1,cw3,cw5,cw2,cw6])
def mc662 : SearchState := (1,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw75,cw7,cw1,cw3,cw2,cw6])
def mc663 : SearchState := (0,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw43,cw75,cw7,cw1,cw3,cw2,cw6])
def mc664 : SearchState := (0,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw5,cw75,cw7,cw1,cw3,cw2,cw6])
def mc665 : SearchState := (1,0xf000fc000003ffff1041041041041041,[cw127,cw43,cw7,cw3,cw5,cw2,cw6])
def mc666 : SearchState := (0,0xf000fc000003ffff1041041041041041,[cw127,cw75,cw43,cw7,cw3,cw5,cw2,cw6])
def mc667 : SearchState := (0,0xf000fc000003ffff1041041041041041,[cw127,cw1,cw43,cw7,cw3,cw5,cw2,cw6])
def mc668 : SearchState := (1,0xffffc00000000000c30c30c30c30c30,[cw133,cw43,cw7,cw1,cw3,cw2,cw6])
def mc669 : SearchState := (0,0xffffc00000000000c30c30c30c30c30,[cw133,cw75,cw43,cw7,cw1,cw3,cw2,cw6])
def mc670 : SearchState := (0,0xffffc00000000000c30c30c30c30c30,[cw133,cw5,cw43,cw7,cw1,cw3,cw2,cw6])
def mc671 : SearchState := (1,0xf03ffc0fc000003f2082082082082082,[cw134,cw43,cw7,cw1,cw3,cw5,cw6])
def mc672 : SearchState := (0,0xf03ffc0fc000003f2082082082082082,[cw134,cw75,cw43,cw7,cw1,cw3,cw5,cw6])
def mc673 : SearchState := (0,0xf03ffc0fc000003f2082082082082082,[cw134,cw2,cw43,cw7,cw1,cw3,cw5,cw6])
def mc674 : SearchState := (1,0xfc0fff0000000005145145145145145,[cw135,cw43,cw7,cw1,cw3,cw5,cw2])
def mc675 : SearchState := (0,0xfc0fff0000000005145145145145145,[cw135,cw75,cw43,cw7,cw1,cw3,cw5,cw2])
def mc676 : SearchState := (0,0xfc0fff0000000005145145145145145,[cw135,cw6,cw43,cw7,cw1,cw3,cw5,cw2])
def mc677 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw43,cw75,cw1,cw3,cw2,cw6])
def mc678 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw43,cw75,cw1,cw3,cw2,cw6])
def mc679 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw43,cw75,cw1,cw3,cw2,cw6])
def mc680 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw43,cw75,cw7,cw5,cw2,cw6])
def mc681 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw43,cw75,cw7,cw3,cw5,cw2])
def mc682 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw43,cw75,cw7,cw3,cw5,cw2])
def mc683 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw43,cw75,cw7,cw3,cw5,cw2])
def mc684 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw43,cw75,cw7,cw1,cw5,cw6])
def mc685 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw43,cw75,cw7,cw1,cw5,cw6])
def mc686 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw43,cw75,cw7,cw1,cw5,cw6])
def mc687 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw43,cw75,cw7,cw1,cw5,cw2])
def mc688 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw43,cw75,cw7,cw1,cw5,cw2])
def mc689 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw43,cw75,cw7,cw1,cw5,cw2])
def mc690 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw43,cw75,cw7,cw1,cw3,cw5])
def mc691 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw4,cw75,cw7,cw1,cw3,cw5,cw2,cw6])
def mc692 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw8,cw75,cw7,cw1,cw3,cw5,cw2,cw6])
def mc693 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw75,cw4,cw1,cw3,cw2,cw6,cw8])
def mc694 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw75,cw4,cw1,cw3,cw2,cw6,cw8])
def mc695 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw75,cw4,cw1,cw3,cw2,cw6,cw8])
def mc696 : SearchState := (1,0xfc003fffffc08e38e38e38e38e38,[cw40,cw75,cw4,cw1,cw3,cw5,cw2,cw6])
def mc697 : SearchState := (0,0xffffffffffc08e38e38e38e38e38,[cw137,cw40,cw75,cw1,cw3,cw5,cw2,cw6])
def mc698 : SearchState := (0,0xffffffffffc08e38e38e38e38e38,[cw137,cw4,cw75,cw1,cw3,cw5,cw2,cw6])
def mc699 : SearchState := (0,0x3ffc00000000000000000000,[cw138,cw40,cw75,cw4,cw1,cw5,cw2,cw6])
def mc700 : SearchState := (1,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw75,cw4,cw1,cw3,cw2,cw6])
def mc701 : SearchState := (0,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw40,cw75,cw4,cw1,cw3,cw2,cw6])
def mc702 : SearchState := (0,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw5,cw75,cw4,cw1,cw3,cw2,cw6])
def mc703 : SearchState := (1,0xf000fc000003ffff1041041041041041,[cw127,cw40,cw4,cw3,cw5,cw2,cw6])
def mc704 : SearchState := (0,0xf000fc000003ffff1041041041041041,[cw127,cw75,cw40,cw4,cw3,cw5,cw2,cw6])
def mc705 : SearchState := (0,0xf000fc000003ffff1041041041041041,[cw127,cw1,cw40,cw4,cw3,cw5,cw2,cw6])
def mc706 : SearchState := (1,0xffffc00000000000c30c30c30c30c30,[cw133,cw40,cw4,cw1,cw3,cw2,cw6])
def mc707 : SearchState := (0,0xffffc00000000000c30c30c30c30c30,[cw133,cw75,cw40,cw4,cw1,cw3,cw2,cw6])
def mc708 : SearchState := (0,0xffffc00000000000c30c30c30c30c30,[cw133,cw5,cw40,cw4,cw1,cw3,cw2,cw6])
def mc709 : SearchState := (1,0xf03ffc0fc000003f2082082082082082,[cw134,cw40,cw4,cw1,cw3,cw5,cw6])
def mc710 : SearchState := (0,0xf03ffc0fc000003f2082082082082082,[cw134,cw75,cw40,cw4,cw1,cw3,cw5,cw6])
def mc711 : SearchState := (0,0xf03ffc0fc000003f2082082082082082,[cw134,cw2,cw40,cw4,cw1,cw3,cw5,cw6])
def mc712 : SearchState := (1,0xfc0fff0000000005145145145145145,[cw135,cw40,cw4,cw1,cw3,cw5,cw2])
def mc713 : SearchState := (0,0xfc0fff0000000005145145145145145,[cw135,cw75,cw40,cw4,cw1,cw3,cw5,cw2])
def mc714 : SearchState := (0,0xfc0fff0000000005145145145145145,[cw135,cw6,cw40,cw4,cw1,cw3,cw5,cw2])
def mc715 : SearchState := (1,0xfffffffc00000008e38e38e38e38e38,[cw42,cw40,cw75,cw1,cw3,cw2,cw6])
def mc716 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw40,cw75,cw1,cw3,cw2,cw6])
def mc717 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw5,cw40,cw75,cw1,cw3,cw2,cw6])
def mc718 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw40,cw75,cw4,cw5,cw2,cw6])
def mc719 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw40,cw75,cw4,cw3,cw5,cw2])
def mc720 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw40,cw75,cw4,cw3,cw5,cw2])
def mc721 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw40,cw75,cw4,cw3,cw5,cw2])
def mc722 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw40,cw75,cw4,cw1,cw5,cw6])
def mc723 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw40,cw75,cw4,cw1,cw5,cw6])
def mc724 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw40,cw75,cw4,cw1,cw5,cw6])
def mc725 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw40,cw75,cw4,cw1,cw5,cw2])
def mc726 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw40,cw75,cw4,cw1,cw5,cw2])
def mc727 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw40,cw75,cw4,cw1,cw5,cw2])
def mc728 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw40,cw75,cw4,cw1,cw3,cw5])
def mc729 : SearchState := (0,0xfc003fffffc08e38e38e38e38e38,[cw40,cw7,cw75,cw4,cw1,cw3,cw5,cw2,cw6])
def mc730 : SearchState := (0,0xfc003fffffc08e38e38e38e38e38,[cw40,cw8,cw75,cw4,cw1,cw3,cw5,cw2,cw6])
def mc731 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw75,cw4,cw7,cw5,cw2,cw6,cw8])
def mc732 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw75,cw4,cw7,cw3,cw5,cw2,cw8])
def mc733 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw75,cw4,cw7,cw3,cw5,cw2,cw8])
def mc734 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw75,cw4,cw7,cw3,cw5,cw2,cw8])
def mc735 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw75,cw4,cw7,cw1,cw5,cw6,cw8])
def mc736 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw75,cw4,cw7,cw1,cw5,cw6,cw8])
def mc737 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw75,cw4,cw7,cw1,cw5,cw6,cw8])
def mc738 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw75,cw4,cw7,cw1,cw5,cw2,cw8])
def mc739 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw75,cw4,cw7,cw1,cw5,cw2,cw8])
def mc740 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw75,cw4,cw7,cw1,cw5,cw2,cw8])
def mc741 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw75,cw4,cw7,cw1,cw3,cw2,cw6])
def mc742 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw75,cw4,cw7,cw1,cw3,cw2,cw6])
def mc743 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw75,cw4,cw7,cw1,cw3,cw2,cw6])
def mc744 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw75,cw4,cw7,cw1,cw3,cw5,cw8])
def mc745 : SearchState := (3,0xffffff03f0008a28a28a28a28a28,[cw43,cw1,cw3,cw5,cw2,cw6,cw7])
def mc746 : SearchState := (1,0x3f0000000000000000000,[cw29,cw43,cw1,cw3,cw5,cw2,cw6,cw7])
def mc747 : SearchState := (1,0xf000ffffff03ffff9a69a69a69a69a69,[cw139,cw43,cw1,cw3,cw5,cw2,cw6,cw7])
def mc748 : SearchState := (1,0x3f0000000000000000000000,[cw53,cw43,cw3,cw1,cw5,cw2,cw6,cw7])
def mc749 : SearchState := (1,0xfffffffff000ebaebaebaebaebae,[cw140,cw43,cw3,cw1,cw5,cw2,cw6,cw7])
def mc750 : SearchState := (1,0x820820820820820,[cw78,cw43,cw5,cw1,cw3,cw2,cw6,cw7])
def mc751 : SearchState := (2,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw43,cw1,cw3,cw2,cw6,cw7])
def mc752 : SearchState := (0,0x3f0000000000000000000,[cw29,cw85,cw1,cw43,cw3,cw2,cw6,cw7])
def mc753 : SearchState := (0,0xffffffffff03ffff9e79e79e79e79e79,[cw141,cw85,cw1,cw43,cw3,cw2,cw6,cw7])
def mc754 : SearchState := (0,0x3f0000000000000000000000,[cw53,cw85,cw3,cw43,cw1,cw2,cw6,cw7])
def mc755 : SearchState := (0,0xffffffffffff000efbefbefbefbefbe,[cw142,cw85,cw3,cw43,cw1,cw2,cw6,cw7])
def mc756 : SearchState := (0,0x3f000fc00000000000000000000000,[cw109,cw85,cw2,cw43,cw1,cw3,cw6,cw7])
def mc757 : SearchState := (0,0xffffffffff03f03faebaebaebaebaeba,[cw143,cw85,cw2,cw43,cw1,cw3,cw6,cw7])
def mc758 : SearchState := (1,0xfc003f0000000000000000000000000,[cw111,cw85,cw43,cw1,cw3,cw2,cw7])
def mc759 : SearchState := (0,0xfc003f0000000000000000000000000,[cw111,cw85,cw6,cw43,cw1,cw3,cw2,cw7])
def mc760 : SearchState := (0,0xfffffffff03f000df7df7df7df7df7d,[cw144,cw85,cw6,cw43,cw1,cw3,cw2,cw7])
def mc761 : SearchState := (0,0xfc00000000000410410410410410,[cw113,cw85,cw7,cw43,cw1,cw3,cw2,cw6])
def mc762 : SearchState := (1,0xfffffffffffffc08e38e38e38e38e38,[cw145,cw7,cw43,cw1,cw3,cw2,cw6])
def mc763 : SearchState := (0,0xfffffffffffffc08e38e38e38e38e38,[cw145,cw85,cw7,cw43,cw1,cw3,cw2,cw6])
def mc764 : SearchState := (1,0xf000ffffff03ffff9a69a69a69a69a69,[cw139,cw1,cw85,cw3,cw2,cw6,cw7])
def mc765 : SearchState := (0,0xf000ffffff03ffff9a69a69a69a69a69,[cw139,cw43,cw1,cw85,cw3,cw2,cw6,cw7])
def mc766 : SearchState := (1,0xf03fffffff03f03faaaaaaaaaaaaaaaa,[cw146,cw2,cw85,cw1,cw3,cw6,cw7])
def mc767 : SearchState := (0,0xf03fffffff03f03faaaaaaaaaaaaaaaa,[cw146,cw43,cw2,cw85,cw1,cw3,cw6,cw7])
def mc768 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw85,cw43,cw2,cw6,cw7])
def mc769 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw85,cw43,cw2,cw6,cw7])
def mc770 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw85,cw43,cw3,cw6,cw7])
def mc771 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw85,cw43,cw3,cw6,cw7])
def mc772 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw85,cw43,cw3,cw2,cw7])
def mc773 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw85,cw43,cw3,cw2,cw7])
def mc774 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw85,cw43,cw3,cw2,cw7])
def mc775 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw85,cw43,cw3,cw2,cw7])
def mc776 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw85,cw43,cw3,cw2,cw6])
def mc777 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw85,cw43,cw1,cw6,cw7])
def mc778 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw85,cw43,cw1,cw6,cw7])
def mc779 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw85,cw43,cw1,cw6,cw7])
def mc780 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw85,cw43,cw1,cw6,cw7])
def mc781 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw85,cw43,cw1,cw3,cw7])
def mc782 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw85,cw43,cw1,cw3,cw7])
def mc783 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw85,cw43,cw1,cw3,cw6])
def mc784 : SearchState := (1,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw43,cw5,cw1,cw3,cw2,cw6,cw7])
def mc785 : SearchState := (1,0xfc00000000000000000000000,[cw55,cw43,cw2,cw1,cw3,cw5,cw6,cw7])
def mc786 : SearchState := (1,0xf03fffffff03f03faaaaaaaaaaaaaaaa,[cw146,cw43,cw2,cw1,cw3,cw5,cw6,cw7])
def mc787 : SearchState := (1,0x3f0000000000000000000000000,[cw22,cw43,cw6,cw1,cw3,cw5,cw2,cw7])
def mc788 : SearchState := (1,0xfc0ffffff03f000db6db6db6db6db6d,[cw147,cw43,cw6,cw1,cw3,cw5,cw2,cw7])
def mc789 : SearchState := (1,0xfc00000000000000000000000000,[cw75,cw43,cw7,cw1,cw3,cw5,cw2,cw6])
def mc790 : SearchState := (1,0xfc003ffc00006186186186186186,[cw128,cw43,cw7,cw1,cw5,cw2,cw6])
def mc791 : SearchState := (0,0xfc003ffc00006186186186186186,[cw128,cw75,cw43,cw7,cw1,cw5,cw2,cw6])
def mc792 : SearchState := (0,0xfc003ffc00006186186186186186,[cw128,cw3,cw43,cw7,cw1,cw5,cw2,cw6])
def mc793 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw75,cw43,cw1,cw3,cw2,cw6])
def mc794 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw75,cw43,cw1,cw3,cw2,cw6])
def mc795 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw75,cw43,cw1,cw3,cw2,cw6])
def mc796 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw75,cw43,cw7,cw5,cw2,cw6])
def mc797 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw75,cw43,cw7,cw3,cw5,cw2])
def mc798 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw75,cw43,cw7,cw3,cw5,cw2])
def mc799 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw75,cw43,cw7,cw3,cw5,cw2])
def mc800 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw75,cw43,cw7,cw1,cw5,cw6])
def mc801 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw75,cw43,cw7,cw1,cw5,cw6])
def mc802 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw75,cw43,cw7,cw1,cw5,cw6])
def mc803 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw75,cw43,cw7,cw1,cw5,cw2])
def mc804 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw75,cw43,cw7,cw1,cw5,cw2])
def mc805 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw75,cw43,cw7,cw1,cw5,cw2])
def mc806 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw75,cw43,cw7,cw1,cw3,cw5])
def mc807 : SearchState := (1,0xffffffffffc08e38e38e38e38e38,[cw137,cw43,cw7,cw1,cw3,cw5,cw2,cw6])
def mc808 : SearchState := (2,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw43,cw5,cw2,cw6,cw7])
def mc809 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw43,cw5,cw2,cw6,cw7])
def mc810 : SearchState := (1,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw5,cw43,cw3,cw2,cw6,cw7])
def mc811 : SearchState := (1,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw43,cw3,cw5,cw6,cw7])
def mc812 : SearchState := (1,0xf000ffffff03f03f8a28a28a28a28a28,[cw148,cw1,cw2,cw3,cw5,cw6,cw7])
def mc813 : SearchState := (0,0xf000ffffff03f03f8a28a28a28a28a28,[cw148,cw0,cw1,cw2,cw3,cw5,cw6,cw7])
def mc814 : SearchState := (0,0xf000ffffff03f03f8a28a28a28a28a28,[cw148,cw43,cw1,cw2,cw3,cw5,cw6,cw7])
def mc815 : SearchState := (1,0xf00000003ffc003f6186186186186186,[cw9,cw1,cw2,cw43,cw5,cw6,cw7])
def mc816 : SearchState := (0,0xf00000003ffc003f6186186186186186,[cw9,cw0,cw1,cw2,cw43,cw5,cw6,cw7])
def mc817 : SearchState := (0,0xf00000003ffc003f6186186186186186,[cw9,cw3,cw1,cw2,cw43,cw5,cw6,cw7])
def mc818 : SearchState := (1,0xffff00000000003f0c30c30c30c30c30,[cw11,cw1,cw2,cw43,cw3,cw6,cw7])
def mc819 : SearchState := (0,0xffff00000000003f0c30c30c30c30c30,[cw11,cw0,cw1,cw2,cw43,cw3,cw6,cw7])
def mc820 : SearchState := (0,0xffff00000000003f0c30c30c30c30c30,[cw11,cw5,cw1,cw2,cw43,cw3,cw6,cw7])
def mc821 : SearchState := (1,0xffc003f00000003f5145145145145145,[cw12,cw1,cw2,cw43,cw3,cw5,cw7])
def mc822 : SearchState := (0,0xffc003f00000003f5145145145145145,[cw12,cw0,cw1,cw2,cw43,cw3,cw5,cw7])
def mc823 : SearchState := (0,0xffc003f00000003f5145145145145145,[cw12,cw6,cw1,cw2,cw43,cw3,cw5,cw7])
def mc824 : SearchState := (1,0xf000fc0000fc0fff0410410410410410,[cw13,cw1,cw2,cw43,cw3,cw5,cw6])
def mc825 : SearchState := (0,0xf000fc0000fc0fff0410410410410410,[cw13,cw0,cw1,cw2,cw43,cw3,cw5,cw6])
def mc826 : SearchState := (0,0xf000fc0000fc0fff0410410410410410,[cw13,cw7,cw1,cw2,cw43,cw3,cw5,cw6])
def mc827 : SearchState := (1,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw0,cw43,cw3,cw5,cw6,cw7])
def mc828 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw0,cw43,cw3,cw5,cw6,cw7])
def mc829 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw2,cw0,cw43,cw3,cw5,cw6,cw7])
def mc830 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw0,cw2,cw43,cw5,cw6,cw7])
def mc831 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw0,cw2,cw43,cw5,cw6,cw7])
def mc832 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw3,cw0,cw2,cw43,cw5,cw6,cw7])
def mc833 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw0,cw2,cw43,cw3,cw5,cw7])
def mc834 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw0,cw2,cw43,cw3,cw5,cw7])
def mc835 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw0,cw2,cw43,cw3,cw5,cw7])
def mc836 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw0,cw1,cw43,cw5,cw6,cw7])
def mc837 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw0,cw1,cw43,cw5,cw6,cw7])
def mc838 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw0,cw1,cw43,cw5,cw6,cw7])
def mc839 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw0,cw1,cw43,cw3,cw5,cw7])
def mc840 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw0,cw1,cw43,cw3,cw5,cw7])
def mc841 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw6,cw0,cw1,cw43,cw3,cw5,cw7])
def mc842 : SearchState := (1,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw43,cw3,cw5,cw6,cw7])
def mc843 : SearchState := (3,0xffc003f00003ffff5145145145145145,[cw17,cw43,cw3,cw5,cw2,cw7])
def mc844 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw43,cw3,cw5,cw2,cw7])
def mc845 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw43,cw3,cw5,cw2,cw7])
def mc846 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw43,cw3,cw5,cw2,cw7])
def mc847 : SearchState := (1,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw43,cw3,cw5,cw2,cw6])
def mc848 : SearchState := (1,0xfff00003ffc00006db6db6db6db6db6,[cw88,cw3,cw5,cw43,cw1,cw2,cw6,cw7])
def mc849 : SearchState := (3,0xf03f000ffffc003f6186186186186186,[cw18,cw43,cw1,cw5,cw6,cw7])
def mc850 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw43,cw1,cw5,cw6,cw7])
def mc851 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw43,cw1,cw5,cw6,cw7])
def mc852 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw43,cw1,cw5,cw6,cw7])
def mc853 : SearchState := (3,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw43,cw1,cw5,cw2,cw7])
def mc854 : SearchState := (1,0x3f03f0000000000000000000000,[cw149,cw41,cw43,cw1,cw5,cw2,cw7])
def mc855 : SearchState := (1,0xfc0fffffffff000fbefbefbefbefbef,[cw150,cw41,cw43,cw1,cw5,cw2,cw7])
def mc856 : SearchState := (1,0x1041041041041041,[cw66,cw41,cw1,cw43,cw5,cw2,cw7])
def mc857 : SearchState := (2,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw1,cw43,cw5,cw2,cw7])
def mc858 : SearchState := (1,0xffc003f03fffffff71c71c71c71c71c7,[cw21,cw41,cw1,cw43,cw5,cw2,cw7])
def mc859 : SearchState := (1,0xfc00000000000000000000000000000,[cw24,cw41,cw5,cw43,cw1,cw2,cw7])
def mc860 : SearchState := (1,0xfff03f03ffc00007df7df7df7df7df7,[cw68,cw41,cw5,cw43,cw1,cw2,cw7])
def mc861 : SearchState := (1,0x2082082082082082,[cw69,cw41,cw2,cw43,cw1,cw5,cw7])
def mc862 : SearchState := (2,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw2,cw43,cw1,cw5,cw7])
def mc863 : SearchState := (1,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw41,cw2,cw43,cw1,cw5,cw7])
def mc864 : SearchState := (1,0xfc00000000000000000000,[cw60,cw41,cw7,cw43,cw1,cw5,cw2])
def mc865 : SearchState := (1,0xfc0fff03ffc0fc075d75d75d75d75d7,[cw70,cw41,cw7,cw43,cw1,cw5,cw2])
def mc866 : SearchState := (1,0xf000ffffff03ffff9a69a69a69a69a69,[cw139,cw43,cw1,cw41,cw5,cw2,cw7])
def mc867 : SearchState := (2,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw43,cw41,cw1,cw2,cw7])
def mc868 : SearchState := (1,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw43,cw5,cw41,cw1,cw2,cw7])
def mc869 : SearchState := (1,0xf03fffffff03f03faaaaaaaaaaaaaaaa,[cw146,cw43,cw2,cw41,cw1,cw5,cw7])
def mc870 : SearchState := (1,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw5,cw41,cw43,cw2,cw7])
def mc871 : SearchState := (1,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw41,cw43,cw5,cw7])
def mc872 : SearchState := (1,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw41,cw43,cw5,cw7])
def mc873 : SearchState := (1,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw41,cw43,cw5,cw2])
def mc874 : SearchState := (1,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw2,cw41,cw43,cw1,cw7])
def mc875 : SearchState := (2,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw41,cw43,cw1,cw2])
def mc876 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw7,cw41,cw43,cw1,cw2])
def mc877 : SearchState := (1,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw41,cw43,cw1,cw5])
def mc878 : SearchState := (2,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw43,cw1,cw5,cw2,cw7])
def mc879 : SearchState := (2,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw43,cw1,cw5,cw2,cw7])
def mc880 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw6,cw43,cw1,cw5,cw2,cw7])
def mc881 : SearchState := (1,0x3f0000000000000000000000000000,[cw57,cw5,cw2,cw43,cw1,cw3,cw6,cw7])
def mc882 : SearchState := (1,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw2,cw43,cw1,cw3,cw6,cw7])
def mc883 : SearchState := (1,0xfc00000000000000000000000000000,[cw24,cw5,cw6,cw43,cw1,cw3,cw2,cw7])
def mc884 : SearchState := (1,0xfff03f0000000005d75d75d75d75d75,[cw90,cw5,cw6,cw43,cw1,cw3,cw2,cw7])
def mc885 : SearchState := (2,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw43,cw1,cw3,cw2,cw6])
def mc886 : SearchState := (0,0xfc00000000000820820820820820,[cw151,cw39,cw43,cw7,cw1,cw3,cw2,cw6])
def mc887 : SearchState := (1,0xfffffffffffffc08e38e38e38e38e38,[cw145,cw43,cw7,cw1,cw3,cw2,cw6])
def mc888 : SearchState := (0,0xfffffffffffffc08e38e38e38e38e38,[cw145,cw39,cw43,cw7,cw1,cw3,cw2,cw6])
def mc889 : SearchState := (0,0xfc00000000000000000,[cw27,cw39,cw1,cw7,cw43,cw3,cw2,cw6])
def mc890 : SearchState := (0,0xfffffc0000ffffff1c71c71c71c71c71,[cw74,cw39,cw1,cw7,cw43,cw3,cw2,cw6])
def mc891 : SearchState := (0,0xfc00000000000000000000,[cw60,cw39,cw3,cw7,cw43,cw1,cw2,cw6])
def mc892 : SearchState := (0,0xffffc003ffc0fc06db6db6db6db6db6,[cw152,cw39,cw3,cw7,cw43,cw1,cw2,cw6])
def mc893 : SearchState := (0,0x3f0000000000000000000000000000,[cw57,cw39,cw2,cw7,cw43,cw1,cw3,cw6])
def mc894 : SearchState := (0,0xfffffc0fc0fc0fff2cb2cb2cb2cb2cb2,[cw77,cw39,cw2,cw7,cw43,cw1,cw3,cw6])
def mc895 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw39,cw6,cw7,cw43,cw1,cw3,cw2])
def mc896 : SearchState := (0,0xffffff000fc0fc05d75d75d75d75d75,[cw153,cw39,cw6,cw7,cw43,cw1,cw3,cw2])
def mc897 : SearchState := (1,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw39,cw43,cw3,cw2,cw6])
def mc898 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw7,cw1,cw39,cw43,cw3,cw2,cw6])
def mc899 : SearchState := (1,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw39,cw43,cw1,cw3,cw6])
def mc900 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw7,cw2,cw39,cw43,cw1,cw3,cw6])
def mc901 : SearchState := (0,0xf000ffffff03ffff9a69a69a69a69a69,[cw139,cw43,cw1,cw39,cw7,cw3,cw2,cw6])
def mc902 : SearchState := (0,0xf03fffffff03f03faaaaaaaaaaaaaaaa,[cw146,cw43,cw2,cw39,cw7,cw1,cw3,cw6])
def mc903 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw39,cw7,cw43,cw2,cw6])
def mc904 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw39,cw7,cw43,cw2,cw6])
def mc905 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw39,cw7,cw43,cw3,cw6])
def mc906 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw39,cw7,cw43,cw3,cw6])
def mc907 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw39,cw7,cw43,cw3,cw2])
def mc908 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw39,cw7,cw43,cw3,cw2])
def mc909 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw39,cw7,cw43,cw3,cw2])
def mc910 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw39,cw7,cw43,cw3,cw2])
def mc911 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw39,cw7,cw43,cw1,cw6])
def mc912 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw39,cw7,cw43,cw1,cw6])
def mc913 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw39,cw7,cw43,cw1,cw6])
def mc914 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw39,cw7,cw43,cw1,cw6])
def mc915 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw39,cw7,cw43,cw1,cw3])
def mc916 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw39,cw7,cw43,cw1,cw3])
def mc917 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw7,cw43,cw1,cw3,cw2,cw6])
def mc918 : SearchState := (2,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw43,cw1,cw3,cw5,cw7])
def mc919 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw43,cw1,cw3,cw5,cw7])
def mc920 : SearchState := (1,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw43,cw1,cw3,cw5,cw6])
def mc921 : SearchState := (1,0xfc0fff000fc0fc05555555555555555,[cw91,cw6,cw7,cw43,cw1,cw3,cw5,cw2])
def mc922 : SearchState := (2,0xffffff03f0008a28a28a28a28a28,[cw43,cw4,cw1,cw3,cw5,cw2,cw6,cw7])
def mc923 : SearchState := (0,0x3f0000000000000000000,[cw29,cw43,cw1,cw4,cw3,cw5,cw2,cw6,cw7])
def mc924 : SearchState := (0,0xf000ffffff03ffff9a69a69a69a69a69,[cw139,cw43,cw1,cw4,cw3,cw5,cw2,cw6,cw7])
def mc925 : SearchState := (0,0x3f0000000000000000000000,[cw53,cw43,cw3,cw4,cw1,cw5,cw2,cw6,cw7])
def mc926 : SearchState := (0,0xfffffffff000ebaebaebaebaebae,[cw140,cw43,cw3,cw4,cw1,cw5,cw2,cw6,cw7])
def mc927 : SearchState := (0,0x820820820820820,[cw78,cw43,cw5,cw4,cw1,cw3,cw2,cw6,cw7])
def mc928 : SearchState := (1,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw43,cw4,cw1,cw3,cw2,cw6,cw7])
def mc929 : SearchState := (1,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw5,cw4,cw1,cw3,cw2,cw6,cw7])
def mc930 : SearchState := (0,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw43,cw5,cw4,cw1,cw3,cw2,cw6,cw7])
def mc931 : SearchState := (0,0xfc00000000000000000000000,[cw55,cw43,cw2,cw4,cw1,cw3,cw5,cw6,cw7])
def mc932 : SearchState := (0,0xf03fffffff03f03faaaaaaaaaaaaaaaa,[cw146,cw43,cw2,cw4,cw1,cw3,cw5,cw6,cw7])
def mc933 : SearchState := (0,0x3f0000000000000000000000000,[cw22,cw43,cw6,cw4,cw1,cw3,cw5,cw2,cw7])
def mc934 : SearchState := (0,0xfc0ffffff03f000db6db6db6db6db6d,[cw147,cw43,cw6,cw4,cw1,cw3,cw5,cw2,cw7])
def mc935 : SearchState := (0,0xfc00000000000000000000000000,[cw75,cw43,cw7,cw4,cw1,cw3,cw5,cw2,cw6])
def mc936 : SearchState := (1,0xffffffffffc08e38e38e38e38e38,[cw137,cw7,cw4,cw1,cw3,cw5,cw2,cw6])
def mc937 : SearchState := (0,0xffffffffffc08e38e38e38e38e38,[cw137,cw43,cw7,cw4,cw1,cw3,cw5,cw2,cw6])
def mc938 : SearchState := (1,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw43,cw3,cw5,cw2,cw6,cw7])
def mc939 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw4,cw1,cw43,cw3,cw5,cw2,cw6,cw7])
def mc940 : SearchState := (1,0xfffffffc0000e38e38e38e38e38e,[cw106,cw3,cw43,cw1,cw5,cw2,cw6,cw7])
def mc941 : SearchState := (0,0xfffffffc0000e38e38e38e38e38e,[cw106,cw4,cw3,cw43,cw1,cw5,cw2,cw6,cw7])
def mc942 : SearchState := (2,0xfffffffc00000008e38e38e38e38e38,[cw42,cw43,cw1,cw3,cw2,cw6,cw7])
def mc943 : SearchState := (1,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw43,cw1,cw3,cw2,cw6,cw7])
def mc944 : SearchState := (1,0xfffffffc00000008e38e38e38e38e38,[cw42,cw5,cw43,cw1,cw3,cw2,cw6,cw7])
def mc945 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw5,cw43,cw1,cw3,cw2,cw6,cw7])
def mc946 : SearchState := (1,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw2,cw43,cw1,cw3,cw5,cw6,cw7])
def mc947 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw43,cw1,cw3,cw5,cw6,cw7])
def mc948 : SearchState := (1,0xfc0ffffc0000000d34d34d34d34d34d,[cw89,cw6,cw43,cw1,cw3,cw5,cw2,cw7])
def mc949 : SearchState := (0,0xfc0ffffc0000000d34d34d34d34d34d,[cw89,cw4,cw6,cw43,cw1,cw3,cw5,cw2,cw7])
def mc950 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw43,cw4,cw5,cw2,cw6,cw7])
def mc951 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw43,cw4,cw5,cw2,cw6,cw7])
def mc952 : SearchState := (0,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw5,cw43,cw4,cw3,cw2,cw6,cw7])
def mc953 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw43,cw4,cw3,cw5,cw6,cw7])
def mc954 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw43,cw4,cw3,cw5,cw6,cw7])
def mc955 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw43,cw4,cw3,cw5,cw2,cw7])
def mc956 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw43,cw4,cw3,cw5,cw2,cw7])
def mc957 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw43,cw4,cw3,cw5,cw2,cw7])
def mc958 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw43,cw4,cw3,cw5,cw2,cw7])
def mc959 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw43,cw4,cw3,cw5,cw2,cw6])
def mc960 : SearchState := (0,0xfff00003ffc00006db6db6db6db6db6,[cw88,cw3,cw5,cw43,cw4,cw1,cw2,cw6,cw7])
def mc961 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw43,cw4,cw1,cw5,cw6,cw7])
def mc962 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw43,cw4,cw1,cw5,cw6,cw7])
def mc963 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw43,cw4,cw1,cw5,cw6,cw7])
def mc964 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw43,cw4,cw1,cw5,cw6,cw7])
def mc965 : SearchState := (2,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw43,cw4,cw1,cw5,cw2,cw7])
def mc966 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw43,cw4,cw1,cw5,cw2,cw7])
def mc967 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw43,cw4,cw1,cw5,cw2,cw7])
def mc968 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw6,cw43,cw4,cw1,cw5,cw2,cw7])
def mc969 : SearchState := (0,0x3f0000000000000000000000000000,[cw57,cw5,cw2,cw43,cw4,cw1,cw3,cw6,cw7])
def mc970 : SearchState := (0,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw2,cw43,cw4,cw1,cw3,cw6,cw7])
def mc971 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw5,cw6,cw43,cw4,cw1,cw3,cw2,cw7])
def mc972 : SearchState := (0,0xfff03f0000000005d75d75d75d75d75,[cw90,cw5,cw6,cw43,cw4,cw1,cw3,cw2,cw7])
def mc973 : SearchState := (2,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw43,cw4,cw1,cw3,cw2,cw6])
def mc974 : SearchState := (0,0xfc00000000000820820820820820,[cw151,cw39,cw43,cw4,cw1,cw3,cw2,cw6])
def mc975 : SearchState := (1,0xfffffffffffffc08e38e38e38e38e38,[cw145,cw39,cw4,cw1,cw3,cw2,cw6])
def mc976 : SearchState := (0,0xfffffffffffffc08e38e38e38e38e38,[cw145,cw39,cw43,cw4,cw1,cw3,cw2,cw6])
def mc977 : SearchState := (1,0xfc00000000000000000000000000,[cw75,cw39,cw43,cw1,cw3,cw2,cw6])
def mc978 : SearchState := (0,0xfc00000000000000000000000000,[cw75,cw39,cw4,cw43,cw1,cw3,cw2,cw6])
def mc979 : SearchState := (0,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw39,cw4,cw43,cw1,cw3,cw2,cw6])
def mc980 : SearchState := (0,0xfc00000000000000000,[cw27,cw39,cw1,cw43,cw4,cw3,cw2,cw6])
def mc981 : SearchState := (0,0xfffffc0000ffffff1c71c71c71c71c71,[cw74,cw39,cw1,cw43,cw4,cw3,cw2,cw6])
def mc982 : SearchState := (0,0xfc00000000000000000000,[cw60,cw39,cw3,cw43,cw4,cw1,cw2,cw6])
def mc983 : SearchState := (0,0xffffc003ffc0fc06db6db6db6db6db6,[cw152,cw39,cw3,cw43,cw4,cw1,cw2,cw6])
def mc984 : SearchState := (0,0x3f0000000000000000000000000000,[cw57,cw39,cw2,cw43,cw4,cw1,cw3,cw6])
def mc985 : SearchState := (0,0xfffffc0fc0fc0fff2cb2cb2cb2cb2cb2,[cw77,cw39,cw2,cw43,cw4,cw1,cw3,cw6])
def mc986 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw39,cw6,cw43,cw4,cw1,cw3,cw2])
def mc987 : SearchState := (0,0xffffff000fc0fc05d75d75d75d75d75,[cw153,cw39,cw6,cw43,cw4,cw1,cw3,cw2])
def mc988 : SearchState := (0,0xf000ffffff03ffff9a69a69a69a69a69,[cw139,cw43,cw1,cw39,cw4,cw3,cw2,cw6])
def mc989 : SearchState := (0,0xf03fffffff03f03faaaaaaaaaaaaaaaa,[cw146,cw43,cw2,cw39,cw4,cw1,cw3,cw6])
def mc990 : SearchState := (1,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw39,cw43,cw3,cw2,cw6])
def mc991 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw4,cw1,cw39,cw43,cw3,cw2,cw6])
def mc992 : SearchState := (1,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw2,cw39,cw43,cw1,cw3,cw6])
def mc993 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw39,cw43,cw1,cw3,cw6])
def mc994 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw39,cw43,cw4,cw2,cw6])
def mc995 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw39,cw43,cw4,cw2,cw6])
def mc996 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw39,cw43,cw4,cw3,cw6])
def mc997 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw39,cw43,cw4,cw3,cw6])
def mc998 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw39,cw43,cw4,cw3,cw2])
def mc999 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw39,cw43,cw4,cw3,cw2])
def mc1000 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw39,cw43,cw4,cw3,cw2])
def mc1001 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw39,cw43,cw4,cw3,cw2])
def mc1002 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw39,cw43,cw4,cw1,cw6])
def mc1003 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw39,cw43,cw4,cw1,cw6])
def mc1004 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw39,cw43,cw4,cw1,cw6])
def mc1005 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw39,cw43,cw4,cw1,cw6])
def mc1006 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw39,cw43,cw4,cw1,cw3])
def mc1007 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw39,cw43,cw4,cw1,cw3])
def mc1008 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw43,cw4,cw1,cw3,cw2,cw6])
def mc1009 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw43,cw4,cw1,cw3,cw2,cw6])
def mc1010 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw7,cw43,cw4,cw1,cw3,cw2,cw6])
def mc1011 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw43,cw4,cw1,cw3,cw5,cw7])
def mc1012 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw43,cw4,cw1,cw3,cw5,cw7])
def mc1013 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw43,cw4,cw1,cw3,cw5,cw6])
def mc1014 : SearchState := (0,0xfc0fff000fc0fc05555555555555555,[cw91,cw6,cw7,cw43,cw4,cw1,cw3,cw5,cw2])
def mc1015 : SearchState := (2,0xffffff03f0008a28a28a28a28a28,[cw43,cw8,cw1,cw3,cw5,cw2,cw6,cw7])
def mc1016 : SearchState := (0,0x3f0000000000000000000,[cw29,cw43,cw1,cw8,cw3,cw5,cw2,cw6,cw7])
def mc1017 : SearchState := (0,0xf000ffffff03ffff9a69a69a69a69a69,[cw139,cw43,cw1,cw8,cw3,cw5,cw2,cw6,cw7])
def mc1018 : SearchState := (0,0x3f0000000000000000000000,[cw53,cw43,cw3,cw8,cw1,cw5,cw2,cw6,cw7])
def mc1019 : SearchState := (0,0xfffffffff000ebaebaebaebaebae,[cw140,cw43,cw3,cw8,cw1,cw5,cw2,cw6,cw7])
def mc1020 : SearchState := (0,0x820820820820820,[cw78,cw43,cw5,cw8,cw1,cw3,cw2,cw6,cw7])
def mc1021 : SearchState := (1,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw43,cw8,cw1,cw3,cw2,cw6,cw7])
def mc1022 : SearchState := (0,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw43,cw5,cw8,cw1,cw3,cw2,cw6,cw7])
def mc1023 : SearchState := (0,0xfc00000000000000000000000,[cw55,cw43,cw2,cw8,cw1,cw3,cw5,cw6,cw7])
def mc1024 : SearchState := (0,0xf03fffffff03f03faaaaaaaaaaaaaaaa,[cw146,cw43,cw2,cw8,cw1,cw3,cw5,cw6,cw7])
def mc1025 : SearchState := (0,0x3f0000000000000000000000000,[cw22,cw43,cw6,cw8,cw1,cw3,cw5,cw2,cw7])
def mc1026 : SearchState := (0,0xfc0ffffff03f000db6db6db6db6db6d,[cw147,cw43,cw6,cw8,cw1,cw3,cw5,cw2,cw7])
def mc1027 : SearchState := (0,0xfc00000000000000000000000000,[cw75,cw43,cw7,cw8,cw1,cw3,cw5,cw2,cw6])
def mc1028 : SearchState := (0,0xffffffffffc08e38e38e38e38e38,[cw137,cw43,cw7,cw8,cw1,cw3,cw5,cw2,cw6])
def mc1029 : SearchState := (1,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw1,cw43,cw3,cw5,cw2,cw6,cw7])
def mc1030 : SearchState := (0,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw8,cw1,cw43,cw3,cw5,cw2,cw6,cw7])
def mc1031 : SearchState := (2,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw43,cw1,cw3,cw2,cw6,cw7])
def mc1032 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw43,cw1,cw3,cw2,cw6,cw7])
def mc1033 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw43,cw1,cw3,cw2,cw6,cw7])
def mc1034 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw5,cw43,cw1,cw3,cw2,cw6,cw7])
def mc1035 : SearchState := (1,0xf03f000fff03f03faaaaaaaaaaaaaaaa,[cw80,cw2,cw43,cw1,cw3,cw5,cw6,cw7])
def mc1036 : SearchState := (0,0xf03f000fff03f03faaaaaaaaaaaaaaaa,[cw80,cw8,cw2,cw43,cw1,cw3,cw5,cw6,cw7])
def mc1037 : SearchState := (1,0xfc003f03f03f000db6db6db6db6db6d,[cw154,cw6,cw43,cw1,cw3,cw5,cw2,cw7])
def mc1038 : SearchState := (0,0xfc003f03f03f000db6db6db6db6db6d,[cw154,cw8,cw6,cw43,cw1,cw3,cw5,cw2,cw7])
def mc1039 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw43,cw8,cw5,cw2,cw6,cw7])
def mc1040 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw43,cw8,cw5,cw2,cw6,cw7])
def mc1041 : SearchState := (0,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw5,cw43,cw8,cw3,cw2,cw6,cw7])
def mc1042 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw43,cw8,cw3,cw5,cw6,cw7])
def mc1043 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw43,cw8,cw3,cw5,cw6,cw7])
def mc1044 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw43,cw8,cw3,cw5,cw2,cw7])
def mc1045 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw43,cw8,cw3,cw5,cw2,cw7])
def mc1046 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw43,cw8,cw3,cw5,cw2,cw7])
def mc1047 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw43,cw8,cw3,cw5,cw2,cw7])
def mc1048 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw43,cw8,cw3,cw5,cw2,cw6])
def mc1049 : SearchState := (0,0xfff00003ffc00006db6db6db6db6db6,[cw88,cw3,cw5,cw43,cw8,cw1,cw2,cw6,cw7])
def mc1050 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw43,cw8,cw1,cw5,cw6,cw7])
def mc1051 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw43,cw8,cw1,cw5,cw6,cw7])
def mc1052 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw43,cw8,cw1,cw5,cw6,cw7])
def mc1053 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw43,cw8,cw1,cw5,cw6,cw7])
def mc1054 : SearchState := (2,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw43,cw8,cw1,cw5,cw2,cw7])
def mc1055 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw43,cw8,cw1,cw5,cw2,cw7])
def mc1056 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw43,cw8,cw1,cw5,cw2,cw7])
def mc1057 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw6,cw43,cw8,cw1,cw5,cw2,cw7])
def mc1058 : SearchState := (0,0x3f0000000000000000000000000000,[cw57,cw5,cw2,cw43,cw8,cw1,cw3,cw6,cw7])
def mc1059 : SearchState := (0,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw2,cw43,cw8,cw1,cw3,cw6,cw7])
def mc1060 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw5,cw6,cw43,cw8,cw1,cw3,cw2,cw7])
def mc1061 : SearchState := (0,0xfff03f0000000005d75d75d75d75d75,[cw90,cw5,cw6,cw43,cw8,cw1,cw3,cw2,cw7])
def mc1062 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw43,cw8,cw1,cw3,cw2,cw6])
def mc1063 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw7,cw43,cw8,cw1,cw3,cw2,cw6])
def mc1064 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw43,cw8,cw1,cw3,cw5,cw7])
def mc1065 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw43,cw8,cw1,cw3,cw5,cw7])
def mc1066 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw43,cw8,cw1,cw3,cw5,cw6])
def mc1067 : SearchState := (0,0xfc0fff000fc0fc05555555555555555,[cw91,cw6,cw7,cw43,cw8,cw1,cw3,cw5,cw2])
def mc1068 : SearchState := (1,0x3f0000000000000000000000000000,[cw57,cw5,cw2,cw1,cw3,cw4,cw6,cw7,cw8])
def mc1069 : SearchState := (1,0xf03f00000003ffff1041041041041041,[cw155,cw5,cw2,cw3,cw4,cw6,cw7,cw8])
def mc1070 : SearchState := (0,0xf03f00000003ffff1041041041041041,[cw155,cw57,cw5,cw2,cw3,cw4,cw6,cw7,cw8])
def mc1071 : SearchState := (0,0xf03f00000003ffff1041041041041041,[cw155,cw1,cw5,cw2,cw3,cw4,cw6,cw7,cw8])
def mc1072 : SearchState := (1,0x3f00003ffc00006186186186186186,[cw156,cw5,cw2,cw1,cw4,cw6,cw7,cw8])
def mc1073 : SearchState := (0,0x3f00003ffc00006186186186186186,[cw156,cw57,cw5,cw2,cw1,cw4,cw6,cw7,cw8])
def mc1074 : SearchState := (0,0x3f00003ffc00006186186186186186,[cw156,cw3,cw5,cw2,cw1,cw4,cw6,cw7,cw8])
def mc1075 : SearchState := (1,0x3fffffc00000008208208208208208,[cw157,cw5,cw2,cw1,cw3,cw6,cw7,cw8])
def mc1076 : SearchState := (0,0x3fffffc00000008208208208208208,[cw157,cw57,cw5,cw2,cw1,cw3,cw6,cw7,cw8])
def mc1077 : SearchState := (0,0x3fffffc00000008208208208208208,[cw157,cw4,cw5,cw2,cw1,cw3,cw6,cw7,cw8])
def mc1078 : SearchState := (1,0xfff03f0000000005145145145145145,[cw158,cw5,cw2,cw1,cw3,cw4,cw7,cw8])
def mc1079 : SearchState := (0,0xfff03f0000000005145145145145145,[cw158,cw57,cw5,cw2,cw1,cw3,cw4,cw7,cw8])
def mc1080 : SearchState := (0,0xfff03f0000000005145145145145145,[cw158,cw6,cw5,cw2,cw1,cw3,cw4,cw7,cw8])
def mc1081 : SearchState := (1,0x3ffc0000fc0fc00410410410410410,[cw159,cw5,cw2,cw1,cw3,cw4,cw6,cw8])
def mc1082 : SearchState := (0,0x3ffc0000fc0fc00410410410410410,[cw159,cw57,cw5,cw2,cw1,cw3,cw4,cw6,cw8])
def mc1083 : SearchState := (0,0x3ffc0000fc0fc00410410410410410,[cw159,cw7,cw5,cw2,cw1,cw3,cw4,cw6,cw8])
def mc1084 : SearchState := (1,0x3f00003f03f0008a28a28a28a28a28,[cw160,cw5,cw2,cw1,cw3,cw4,cw6,cw7])
def mc1085 : SearchState := (0,0x3f00003f03f0008a28a28a28a28a28,[cw160,cw57,cw5,cw2,cw1,cw3,cw4,cw6,cw7])
def mc1086 : SearchState := (0,0x3f00003f03f0008a28a28a28a28a28,[cw160,cw8,cw5,cw2,cw1,cw3,cw4,cw6,cw7])
def mc1087 : SearchState := (1,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw57,cw1,cw3,cw4,cw6,cw7,cw8])
def mc1088 : SearchState := (0,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw57,cw1,cw3,cw4,cw6,cw7,cw8])
def mc1089 : SearchState := (0,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw2,cw57,cw1,cw3,cw4,cw6,cw7,cw8])
def mc1090 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw57,cw2,cw1,cw3,cw6,cw7,cw8])
def mc1091 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw6,cw57,cw2,cw1,cw3,cw4,cw7,cw8])
def mc1092 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw57,cw2,cw1,cw3,cw4,cw6,cw8])
def mc1093 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw57,cw2,cw1,cw3,cw4,cw6,cw8])
def mc1094 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw57,cw2,cw1,cw3,cw4,cw6,cw8])
def mc1095 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw57,cw2,cw1,cw3,cw4,cw6,cw7])
def mc1096 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw57,cw2,cw1,cw3,cw4,cw6,cw7])
def mc1097 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw57,cw2,cw1,cw3,cw4,cw6,cw7])
def mc1098 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw57,cw5,cw1,cw4,cw6,cw7,cw8])
def mc1099 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw57,cw5,cw1,cw4,cw6,cw7,cw8])
def mc1100 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw57,cw5,cw1,cw4,cw6,cw7,cw8])
def mc1101 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw57,cw5,cw1,cw3,cw4,cw7,cw8])
def mc1102 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw7,cw57,cw5,cw1,cw3,cw4,cw6,cw8])
def mc1103 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw57,cw5,cw2,cw4,cw6,cw7,cw8])
def mc1104 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw57,cw5,cw2,cw3,cw4,cw7,cw8])
def mc1105 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw57,cw5,cw2,cw3,cw4,cw7,cw8])
def mc1106 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw57,cw5,cw2,cw3,cw4,cw7,cw8])
def mc1107 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw57,cw5,cw2,cw1,cw4,cw7,cw8])
def mc1108 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw57,cw5,cw2,cw1,cw4,cw7,cw8])
def mc1109 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw57,cw5,cw2,cw1,cw4,cw7,cw8])
def mc1110 : SearchState := (1,0xfc00000000000000000000000000000,[cw24,cw5,cw6,cw1,cw3,cw4,cw2,cw7,cw8])
def mc1111 : SearchState := (1,0xffc000000003ffff1041041041041041,[cw161,cw5,cw6,cw3,cw4,cw2,cw7,cw8])
def mc1112 : SearchState := (0,0xffc000000003ffff1041041041041041,[cw161,cw24,cw5,cw6,cw3,cw4,cw2,cw7,cw8])
def mc1113 : SearchState := (0,0xffc000000003ffff1041041041041041,[cw161,cw1,cw5,cw6,cw3,cw4,cw2,cw7,cw8])
def mc1114 : SearchState := (1,0xfc000003ffc00006186186186186186,[cw162,cw5,cw6,cw1,cw4,cw2,cw7,cw8])
def mc1115 : SearchState := (0,0xfc000003ffc00006186186186186186,[cw162,cw24,cw5,cw6,cw1,cw4,cw2,cw7,cw8])
def mc1116 : SearchState := (0,0xfc000003ffc00006186186186186186,[cw162,cw3,cw5,cw6,cw1,cw4,cw2,cw7,cw8])
def mc1117 : SearchState := (1,0xfc0ffffc00000008208208208208208,[cw163,cw5,cw6,cw1,cw3,cw2,cw7,cw8])
def mc1118 : SearchState := (0,0xfc0ffffc00000008208208208208208,[cw163,cw24,cw5,cw6,cw1,cw3,cw2,cw7,cw8])
def mc1119 : SearchState := (0,0xfc0ffffc00000008208208208208208,[cw163,cw4,cw5,cw6,cw1,cw3,cw2,cw7,cw8])
def mc1120 : SearchState := (1,0xffff000fc000003f2082082082082082,[cw164,cw5,cw6,cw1,cw3,cw4,cw7,cw8])
def mc1121 : SearchState := (0,0xffff000fc000003f2082082082082082,[cw164,cw24,cw5,cw6,cw1,cw3,cw4,cw7,cw8])
def mc1122 : SearchState := (0,0xffff000fc000003f2082082082082082,[cw164,cw2,cw5,cw6,cw1,cw3,cw4,cw7,cw8])
def mc1123 : SearchState := (1,0xfc0fc0000fc0fc00410410410410410,[cw165,cw5,cw6,cw1,cw3,cw4,cw2,cw8])
def mc1124 : SearchState := (0,0xfc0fc0000fc0fc00410410410410410,[cw165,cw24,cw5,cw6,cw1,cw3,cw4,cw2,cw8])
def mc1125 : SearchState := (0,0xfc0fc0000fc0fc00410410410410410,[cw165,cw7,cw5,cw6,cw1,cw3,cw4,cw2,cw8])
def mc1126 : SearchState := (1,0xfc000003f03f0008a28a28a28a28a28,[cw166,cw5,cw6,cw1,cw3,cw4,cw2,cw7])
def mc1127 : SearchState := (0,0xfc000003f03f0008a28a28a28a28a28,[cw166,cw24,cw5,cw6,cw1,cw3,cw4,cw2,cw7])
def mc1128 : SearchState := (0,0xfc000003f03f0008a28a28a28a28a28,[cw166,cw8,cw5,cw6,cw1,cw3,cw4,cw2,cw7])
def mc1129 : SearchState := (1,0xfff03f0000000005d75d75d75d75d75,[cw90,cw24,cw1,cw3,cw4,cw2,cw7,cw8])
def mc1130 : SearchState := (0,0xfff03f0000000005d75d75d75d75d75,[cw90,cw5,cw24,cw1,cw3,cw4,cw2,cw7,cw8])
def mc1131 : SearchState := (0,0xfff03f0000000005d75d75d75d75d75,[cw90,cw6,cw24,cw1,cw3,cw4,cw2,cw7,cw8])
def mc1132 : SearchState := (0,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw24,cw6,cw3,cw4,cw2,cw7,cw8])
def mc1133 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw24,cw6,cw1,cw3,cw2,cw7,cw8])
def mc1134 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw24,cw6,cw1,cw3,cw4,cw2,cw8])
def mc1135 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw24,cw6,cw1,cw3,cw4,cw2,cw8])
def mc1136 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw24,cw6,cw1,cw3,cw4,cw2,cw8])
def mc1137 : SearchState := (1,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw24,cw6,cw1,cw3,cw4,cw2,cw7])
def mc1138 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw24,cw6,cw1,cw3,cw4,cw2,cw7])
def mc1139 : SearchState := (0,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw8,cw24,cw6,cw1,cw3,cw4,cw2,cw7])
def mc1140 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw24,cw5,cw3,cw4,cw2,cw7,cw8])
def mc1141 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw24,cw5,cw3,cw4,cw2,cw7,cw8])
def mc1142 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw24,cw5,cw3,cw4,cw2,cw7,cw8])
def mc1143 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw24,cw5,cw1,cw4,cw2,cw7,cw8])
def mc1144 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw24,cw5,cw1,cw4,cw2,cw7,cw8])
def mc1145 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw24,cw5,cw1,cw4,cw2,cw7,cw8])
def mc1146 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw24,cw5,cw1,cw3,cw4,cw7,cw8])
def mc1147 : SearchState := (0,0xfc0fff000fc0fc05555555555555555,[cw91,cw7,cw24,cw5,cw1,cw3,cw4,cw2,cw8])
def mc1148 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw24,cw5,cw6,cw4,cw2,cw7,cw8])
def mc1149 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw24,cw5,cw6,cw1,cw4,cw7,cw8])
def mc1150 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw24,cw5,cw6,cw1,cw4,cw7,cw8])
def mc1151 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw24,cw5,cw6,cw1,cw4,cw7,cw8])
def mc1152 : SearchState := (3,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw1,cw3,cw4,cw2,cw6,cw8])
def mc1153 : SearchState := (1,0xfc00000000000000000,[cw27,cw39,cw1,cw3,cw4,cw2,cw6,cw8])
def mc1154 : SearchState := (1,0xfffffc0000ffffff1c71c71c71c71c71,[cw74,cw39,cw1,cw3,cw4,cw2,cw6,cw8])
def mc1155 : SearchState := (1,0xfc00000000000000000000,[cw60,cw39,cw3,cw1,cw4,cw2,cw6,cw8])
def mc1156 : SearchState := (1,0xffffc003ffc0fc06db6db6db6db6db6,[cw152,cw39,cw3,cw1,cw4,cw2,cw6,cw8])
def mc1157 : SearchState := (1,0xfc00000000000000000000000000,[cw75,cw39,cw4,cw1,cw3,cw2,cw6,cw8])
def mc1158 : SearchState := (1,0xf000fc000003ffff1041041041041041,[cw127,cw39,cw4,cw3,cw2,cw6,cw8])
def mc1159 : SearchState := (0,0xf000fc000003ffff1041041041041041,[cw127,cw75,cw39,cw4,cw3,cw2,cw6,cw8])
def mc1160 : SearchState := (0,0xf000fc000003ffff1041041041041041,[cw127,cw1,cw39,cw4,cw3,cw2,cw6,cw8])
def mc1161 : SearchState := (1,0xfc003ffc00006186186186186186,[cw128,cw39,cw4,cw1,cw2,cw6,cw8])
def mc1162 : SearchState := (0,0xfc003ffc00006186186186186186,[cw128,cw75,cw39,cw4,cw1,cw2,cw6,cw8])
def mc1163 : SearchState := (0,0xfc003ffc00006186186186186186,[cw128,cw3,cw39,cw4,cw1,cw2,cw6,cw8])
def mc1164 : SearchState := (1,0xf03ffc0fc000003f2082082082082082,[cw134,cw39,cw4,cw1,cw3,cw6,cw8])
def mc1165 : SearchState := (0,0xf03ffc0fc000003f2082082082082082,[cw134,cw75,cw39,cw4,cw1,cw3,cw6,cw8])
def mc1166 : SearchState := (0,0xf03ffc0fc000003f2082082082082082,[cw134,cw2,cw39,cw4,cw1,cw3,cw6,cw8])
def mc1167 : SearchState := (1,0xfc0fff0000000005145145145145145,[cw135,cw39,cw4,cw1,cw3,cw2,cw8])
def mc1168 : SearchState := (0,0xfc0fff0000000005145145145145145,[cw135,cw75,cw39,cw4,cw1,cw3,cw2,cw8])
def mc1169 : SearchState := (0,0xfc0fff0000000005145145145145145,[cw135,cw6,cw39,cw4,cw1,cw3,cw2,cw8])
def mc1170 : SearchState := (1,0xfc003f03f0008a28a28a28a28a28,[cw136,cw39,cw4,cw1,cw3,cw2,cw6])
def mc1171 : SearchState := (0,0xfc003f03f0008a28a28a28a28a28,[cw136,cw75,cw39,cw4,cw1,cw3,cw2,cw6])
def mc1172 : SearchState := (0,0xfc003f03f0008a28a28a28a28a28,[cw136,cw8,cw39,cw4,cw1,cw3,cw2,cw6])
def mc1173 : SearchState := (0,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw39,cw75,cw1,cw3,cw2,cw6,cw8])
def mc1174 : SearchState := (0,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw4,cw75,cw1,cw3,cw2,cw6,cw8])
def mc1175 : SearchState := (0,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw39,cw75,cw4,cw1,cw3,cw2,cw6])
def mc1176 : SearchState := (0,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw8,cw75,cw4,cw1,cw3,cw2,cw6])
def mc1177 : SearchState := (1,0xffffff03f0008a28a28a28a28a28,[cw43,cw75,cw39,cw1,cw3,cw2,cw6])
def mc1178 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw4,cw75,cw39,cw1,cw3,cw2,cw6])
def mc1179 : SearchState := (0,0xffffff03f0008a28a28a28a28a28,[cw43,cw8,cw75,cw39,cw1,cw3,cw2,cw6])
def mc1180 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw75,cw39,cw4,cw2,cw6,cw8])
def mc1181 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw75,cw39,cw4,cw3,cw2,cw8])
def mc1182 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw75,cw39,cw4,cw3,cw2,cw8])
def mc1183 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw75,cw39,cw4,cw3,cw2,cw8])
def mc1184 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw75,cw39,cw4,cw1,cw6,cw8])
def mc1185 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw75,cw39,cw4,cw1,cw6,cw8])
def mc1186 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw75,cw39,cw4,cw1,cw6,cw8])
def mc1187 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw75,cw39,cw4,cw1,cw2,cw8])
def mc1188 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw75,cw39,cw4,cw1,cw2,cw8])
def mc1189 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw75,cw39,cw4,cw1,cw2,cw8])
def mc1190 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw75,cw39,cw4,cw1,cw3,cw8])
def mc1191 : SearchState := (1,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw39,cw4,cw1,cw3,cw2,cw6,cw8])
def mc1192 : SearchState := (1,0x3f0000000000000000000000000000,[cw57,cw39,cw2,cw1,cw3,cw4,cw6,cw8])
def mc1193 : SearchState := (1,0xfffffc0fc0fc0fff2cb2cb2cb2cb2cb2,[cw77,cw39,cw2,cw1,cw3,cw4,cw6,cw8])
def mc1194 : SearchState := (1,0xfc00000000000000000000000000000,[cw24,cw39,cw6,cw1,cw3,cw4,cw2,cw8])
def mc1195 : SearchState := (1,0xffffff000fc0fc05d75d75d75d75d75,[cw153,cw39,cw6,cw1,cw3,cw4,cw2,cw8])
def mc1196 : SearchState := (1,0x820820820820820,[cw78,cw39,cw8,cw1,cw3,cw4,cw2,cw6])
def mc1197 : SearchState := (2,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw39,cw1,cw3,cw4,cw2,cw6])
def mc1198 : SearchState := (0,0x3ffc00000000000000000,[cw167,cw79,cw1,cw39,cw3,cw4,cw2,cw6])
def mc1199 : SearchState := (0,0xfffffc003fffffff9e79e79e79e79e79,[cw168,cw79,cw1,cw39,cw3,cw4,cw2,cw6])
def mc1200 : SearchState := (1,0x3ffc00000000000000000000,[cw138,cw79,cw39,cw1,cw4,cw2,cw6])
def mc1201 : SearchState := (0,0x3ffc00000000000000000000,[cw138,cw79,cw3,cw39,cw1,cw4,cw2,cw6])
def mc1202 : SearchState := (0,0xffffc003fffffc0efbefbefbefbefbe,[cw169,cw79,cw3,cw39,cw1,cw4,cw2,cw6])
def mc1203 : SearchState := (0,0xfc00000000008208208208208208,[cw170,cw79,cw4,cw39,cw1,cw3,cw2,cw6])
def mc1204 : SearchState := (1,0xfffffffffffffc08e38e38e38e38e38,[cw145,cw4,cw39,cw1,cw3,cw2,cw6])
def mc1205 : SearchState := (0,0xfffffffffffffc08e38e38e38e38e38,[cw145,cw79,cw4,cw39,cw1,cw3,cw2,cw6])
def mc1206 : SearchState := (0,0x3f0000000000000000000000000000,[cw57,cw79,cw2,cw39,cw1,cw3,cw4,cw6])
def mc1207 : SearchState := (0,0xfffffc0fffffffffaebaebaebaebaeba,[cw171,cw79,cw2,cw39,cw1,cw3,cw4,cw6])
def mc1208 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw79,cw6,cw39,cw1,cw3,cw4,cw2])
def mc1209 : SearchState := (0,0xffffff03fffffc0df7df7df7df7df7d,[cw172,cw79,cw6,cw39,cw1,cw3,cw4,cw2])
def mc1210 : SearchState := (1,0xfffffc0000ffffff1c71c71c71c71c71,[cw74,cw1,cw79,cw3,cw4,cw2,cw6])
def mc1211 : SearchState := (0,0xfffffc0000ffffff1c71c71c71c71c71,[cw74,cw39,cw1,cw79,cw3,cw4,cw2,cw6])
def mc1212 : SearchState := (0,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw39,cw4,cw79,cw1,cw3,cw2,cw6])
def mc1213 : SearchState := (1,0xfffffc0fc0fc0fff2cb2cb2cb2cb2cb2,[cw77,cw2,cw79,cw1,cw3,cw4,cw6])
def mc1214 : SearchState := (0,0xfffffc0fc0fc0fff2cb2cb2cb2cb2cb2,[cw77,cw39,cw2,cw79,cw1,cw3,cw4,cw6])
def mc1215 : SearchState := (1,0xffffff000fc0fc05d75d75d75d75d75,[cw153,cw6,cw79,cw1,cw3,cw4,cw2])
def mc1216 : SearchState := (0,0xffffff000fc0fc05d75d75d75d75d75,[cw153,cw39,cw6,cw79,cw1,cw3,cw4,cw2])
def mc1217 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw79,cw39,cw4,cw2,cw6])
def mc1218 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw79,cw39,cw4,cw2,cw6])
def mc1219 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw79,cw39,cw3,cw2,cw6])
def mc1220 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw79,cw39,cw3,cw4,cw6])
def mc1221 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw79,cw39,cw3,cw4,cw6])
def mc1222 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw79,cw39,cw3,cw4,cw2])
def mc1223 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw79,cw39,cw3,cw4,cw2])
def mc1224 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw79,cw39,cw3,cw4,cw2])
def mc1225 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw79,cw39,cw3,cw4,cw2])
def mc1226 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw79,cw39,cw1,cw4,cw6])
def mc1227 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw79,cw39,cw1,cw4,cw6])
def mc1228 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw79,cw39,cw1,cw4,cw6])
def mc1229 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw79,cw39,cw1,cw4,cw6])
def mc1230 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw79,cw39,cw1,cw3,cw6])
def mc1231 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw79,cw39,cw1,cw3,cw4])
def mc1232 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw79,cw39,cw1,cw3,cw4])
def mc1233 : SearchState := (1,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw39,cw8,cw1,cw3,cw4,cw2,cw6])
def mc1234 : SearchState := (2,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw39,cw4,cw2,cw6,cw8])
def mc1235 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw39,cw4,cw2,cw6,cw8])
def mc1236 : SearchState := (1,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw39,cw3,cw2,cw6,cw8])
def mc1237 : SearchState := (1,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw39,cw3,cw4,cw6,cw8])
def mc1238 : SearchState := (1,0xfffffc0000fc0fff0c30c30c30c30c30,[cw173,cw1,cw2,cw3,cw4,cw6,cw8])
def mc1239 : SearchState := (0,0xfffffc0000fc0fff0c30c30c30c30c30,[cw173,cw0,cw1,cw2,cw3,cw4,cw6,cw8])
def mc1240 : SearchState := (0,0xfffffc0000fc0fff0c30c30c30c30c30,[cw173,cw39,cw1,cw2,cw3,cw4,cw6,cw8])
def mc1241 : SearchState := (1,0xf00000003ffc003f6186186186186186,[cw9,cw1,cw2,cw39,cw4,cw6,cw8])
def mc1242 : SearchState := (0,0xf00000003ffc003f6186186186186186,[cw9,cw0,cw1,cw2,cw39,cw4,cw6,cw8])
def mc1243 : SearchState := (0,0xf00000003ffc003f6186186186186186,[cw9,cw3,cw1,cw2,cw39,cw4,cw6,cw8])
def mc1244 : SearchState := (1,0xf000ffffc000003f8208208208208208,[cw10,cw1,cw2,cw39,cw3,cw6,cw8])
def mc1245 : SearchState := (0,0xf000ffffc000003f8208208208208208,[cw10,cw0,cw1,cw2,cw39,cw3,cw6,cw8])
def mc1246 : SearchState := (0,0xf000ffffc000003f8208208208208208,[cw10,cw4,cw1,cw2,cw39,cw3,cw6,cw8])
def mc1247 : SearchState := (1,0xffc003f00000003f5145145145145145,[cw12,cw1,cw2,cw39,cw3,cw4,cw8])
def mc1248 : SearchState := (0,0xffc003f00000003f5145145145145145,[cw12,cw0,cw1,cw2,cw39,cw3,cw4,cw8])
def mc1249 : SearchState := (0,0xffc003f00000003f5145145145145145,[cw12,cw6,cw1,cw2,cw39,cw3,cw4,cw8])
def mc1250 : SearchState := (1,0xf00000003f03f03f8a28a28a28a28a28,[cw14,cw1,cw2,cw39,cw3,cw4,cw6])
def mc1251 : SearchState := (0,0xf00000003f03f03f8a28a28a28a28a28,[cw14,cw0,cw1,cw2,cw39,cw3,cw4,cw6])
def mc1252 : SearchState := (0,0xf00000003f03f03f8a28a28a28a28a28,[cw14,cw8,cw1,cw2,cw39,cw3,cw4,cw6])
def mc1253 : SearchState := (1,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw0,cw39,cw3,cw4,cw6,cw8])
def mc1254 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw0,cw39,cw3,cw4,cw6,cw8])
def mc1255 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw2,cw0,cw39,cw3,cw4,cw6,cw8])
def mc1256 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw0,cw2,cw39,cw4,cw6,cw8])
def mc1257 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw0,cw2,cw39,cw4,cw6,cw8])
def mc1258 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw3,cw0,cw2,cw39,cw4,cw6,cw8])
def mc1259 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw0,cw2,cw39,cw3,cw4,cw8])
def mc1260 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw0,cw2,cw39,cw3,cw4,cw8])
def mc1261 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw0,cw2,cw39,cw3,cw4,cw8])
def mc1262 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw0,cw1,cw39,cw4,cw6,cw8])
def mc1263 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw0,cw1,cw39,cw4,cw6,cw8])
def mc1264 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw0,cw1,cw39,cw4,cw6,cw8])
def mc1265 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw0,cw1,cw39,cw3,cw4,cw8])
def mc1266 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw0,cw1,cw39,cw3,cw4,cw8])
def mc1267 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw6,cw0,cw1,cw39,cw3,cw4,cw8])
def mc1268 : SearchState := (1,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw39,cw3,cw4,cw6,cw8])
def mc1269 : SearchState := (3,0xffc003f00003ffff5145145145145145,[cw17,cw39,cw3,cw4,cw2,cw8])
def mc1270 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw39,cw3,cw4,cw2,cw8])
def mc1271 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw39,cw3,cw4,cw2,cw8])
def mc1272 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw39,cw3,cw4,cw2,cw8])
def mc1273 : SearchState := (1,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw1,cw8,cw39,cw3,cw4,cw2,cw6])
def mc1274 : SearchState := (3,0xf03f000ffffc003f6186186186186186,[cw18,cw39,cw1,cw4,cw6,cw8])
def mc1275 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw39,cw1,cw4,cw6,cw8])
def mc1276 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw39,cw1,cw4,cw6,cw8])
def mc1277 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw39,cw1,cw4,cw6,cw8])
def mc1278 : SearchState := (1,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw39,cw1,cw3,cw6,cw8])
def mc1279 : SearchState := (2,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw39,cw1,cw3,cw4,cw8])
def mc1280 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw39,cw1,cw3,cw4,cw8])
def mc1281 : SearchState := (1,0xf03f000fff03f03faaaaaaaaaaaaaaaa,[cw80,cw2,cw8,cw39,cw1,cw3,cw4,cw6])
def mc1282 : SearchState := (2,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw1,cw3,cw4,cw2,cw6,cw8])
def mc1283 : SearchState := (0,0xfc00000000000000000,[cw27,cw39,cw1,cw5,cw3,cw4,cw2,cw6,cw8])
def mc1284 : SearchState := (0,0xfffffc0000ffffff1c71c71c71c71c71,[cw74,cw39,cw1,cw5,cw3,cw4,cw2,cw6,cw8])
def mc1285 : SearchState := (0,0xfc00000000000000000000,[cw60,cw39,cw3,cw5,cw1,cw4,cw2,cw6,cw8])
def mc1286 : SearchState := (0,0xffffc003ffc0fc06db6db6db6db6db6,[cw152,cw39,cw3,cw5,cw1,cw4,cw2,cw6,cw8])
def mc1287 : SearchState := (0,0xfc00000000000000000000000000,[cw75,cw39,cw4,cw5,cw1,cw3,cw2,cw6,cw8])
def mc1288 : SearchState := (0,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw39,cw4,cw5,cw1,cw3,cw2,cw6,cw8])
def mc1289 : SearchState := (0,0x3f0000000000000000000000000000,[cw57,cw39,cw2,cw5,cw1,cw3,cw4,cw6,cw8])
def mc1290 : SearchState := (0,0xfffffc0fc0fc0fff2cb2cb2cb2cb2cb2,[cw77,cw39,cw2,cw5,cw1,cw3,cw4,cw6,cw8])
def mc1291 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw39,cw6,cw5,cw1,cw3,cw4,cw2,cw8])
def mc1292 : SearchState := (0,0xffffff000fc0fc05d75d75d75d75d75,[cw153,cw39,cw6,cw5,cw1,cw3,cw4,cw2,cw8])
def mc1293 : SearchState := (0,0x820820820820820,[cw78,cw39,cw8,cw5,cw1,cw3,cw4,cw2,cw6])
def mc1294 : SearchState := (1,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw39,cw5,cw1,cw3,cw4,cw2,cw6])
def mc1295 : SearchState := (0,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw39,cw8,cw5,cw1,cw3,cw4,cw2,cw6])
def mc1296 : SearchState := (1,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw39,cw3,cw4,cw2,cw6,cw8])
def mc1297 : SearchState := (0,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw5,cw1,cw39,cw3,cw4,cw2,cw6,cw8])
def mc1298 : SearchState := (1,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw39,cw1,cw3,cw2,cw6,cw8])
def mc1299 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw5,cw4,cw39,cw1,cw3,cw2,cw6,cw8])
def mc1300 : SearchState := (1,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw2,cw39,cw1,cw3,cw4,cw6,cw8])
def mc1301 : SearchState := (0,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw2,cw39,cw1,cw3,cw4,cw6,cw8])
def mc1302 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw39,cw5,cw4,cw2,cw6,cw8])
def mc1303 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw39,cw5,cw4,cw2,cw6,cw8])
def mc1304 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw39,cw5,cw3,cw2,cw6,cw8])
def mc1305 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw39,cw5,cw3,cw4,cw6,cw8])
def mc1306 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw39,cw5,cw3,cw4,cw6,cw8])
def mc1307 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw39,cw5,cw3,cw4,cw2,cw8])
def mc1308 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw39,cw5,cw3,cw4,cw2,cw8])
def mc1309 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw39,cw5,cw3,cw4,cw2,cw8])
def mc1310 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw39,cw5,cw3,cw4,cw2,cw8])
def mc1311 : SearchState := (0,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw1,cw8,cw39,cw5,cw3,cw4,cw2,cw6])
def mc1312 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw39,cw5,cw1,cw4,cw6,cw8])
def mc1313 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw39,cw5,cw1,cw4,cw6,cw8])
def mc1314 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw39,cw5,cw1,cw4,cw6,cw8])
def mc1315 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw39,cw5,cw1,cw4,cw6,cw8])
def mc1316 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw39,cw5,cw1,cw3,cw6,cw8])
def mc1317 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw39,cw5,cw1,cw3,cw4,cw8])
def mc1318 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw39,cw5,cw1,cw3,cw4,cw8])
def mc1319 : SearchState := (0,0xf03f000fff03f03faaaaaaaaaaaaaaaa,[cw80,cw2,cw8,cw39,cw5,cw1,cw3,cw4,cw6])
def mc1320 : SearchState := (2,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw1,cw3,cw4,cw2,cw6,cw8])
def mc1321 : SearchState := (0,0xfc00000000000000000,[cw27,cw39,cw1,cw7,cw3,cw4,cw2,cw6,cw8])
def mc1322 : SearchState := (0,0xfffffc0000ffffff1c71c71c71c71c71,[cw74,cw39,cw1,cw7,cw3,cw4,cw2,cw6,cw8])
def mc1323 : SearchState := (0,0xfc00000000000000000000,[cw60,cw39,cw3,cw7,cw1,cw4,cw2,cw6,cw8])
def mc1324 : SearchState := (0,0xffffc003ffc0fc06db6db6db6db6db6,[cw152,cw39,cw3,cw7,cw1,cw4,cw2,cw6,cw8])
def mc1325 : SearchState := (0,0xfc00000000000000000000000000,[cw75,cw39,cw4,cw7,cw1,cw3,cw2,cw6,cw8])
def mc1326 : SearchState := (1,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw4,cw7,cw1,cw3,cw2,cw6,cw8])
def mc1327 : SearchState := (0,0xfffffffc0fc0fc08e38e38e38e38e38,[cw76,cw39,cw4,cw7,cw1,cw3,cw2,cw6,cw8])
def mc1328 : SearchState := (0,0x3f0000000000000000000000000000,[cw57,cw39,cw2,cw7,cw1,cw3,cw4,cw6,cw8])
def mc1329 : SearchState := (0,0xfffffc0fc0fc0fff2cb2cb2cb2cb2cb2,[cw77,cw39,cw2,cw7,cw1,cw3,cw4,cw6,cw8])
def mc1330 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw39,cw6,cw7,cw1,cw3,cw4,cw2,cw8])
def mc1331 : SearchState := (0,0xffffff000fc0fc05d75d75d75d75d75,[cw153,cw39,cw6,cw7,cw1,cw3,cw4,cw2,cw8])
def mc1332 : SearchState := (0,0x820820820820820,[cw78,cw39,cw8,cw7,cw1,cw3,cw4,cw2,cw6])
def mc1333 : SearchState := (2,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw7,cw1,cw3,cw4,cw2,cw6])
def mc1334 : SearchState := (1,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw39,cw7,cw1,cw3,cw4,cw2,cw6])
def mc1335 : SearchState := (1,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw8,cw7,cw1,cw3,cw4,cw2,cw6])
def mc1336 : SearchState := (0,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw39,cw8,cw7,cw1,cw3,cw4,cw2,cw6])
def mc1337 : SearchState := (1,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw39,cw3,cw4,cw2,cw6,cw8])
def mc1338 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw7,cw1,cw39,cw3,cw4,cw2,cw6,cw8])
def mc1339 : SearchState := (1,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw39,cw1,cw3,cw4,cw6,cw8])
def mc1340 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw7,cw2,cw39,cw1,cw3,cw4,cw6,cw8])
def mc1341 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw39,cw7,cw4,cw2,cw6,cw8])
def mc1342 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw39,cw7,cw4,cw2,cw6,cw8])
def mc1343 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw39,cw7,cw3,cw2,cw6,cw8])
def mc1344 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw39,cw7,cw3,cw4,cw6,cw8])
def mc1345 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw39,cw7,cw3,cw4,cw6,cw8])
def mc1346 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw39,cw7,cw3,cw4,cw2,cw8])
def mc1347 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw39,cw7,cw3,cw4,cw2,cw8])
def mc1348 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw39,cw7,cw3,cw4,cw2,cw8])
def mc1349 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw39,cw7,cw3,cw4,cw2,cw8])
def mc1350 : SearchState := (0,0xf00000003f03ffff9a69a69a69a69a69,[cw51,cw1,cw8,cw39,cw7,cw3,cw4,cw2,cw6])
def mc1351 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw39,cw7,cw1,cw4,cw6,cw8])
def mc1352 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw39,cw7,cw1,cw4,cw6,cw8])
def mc1353 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw39,cw7,cw1,cw4,cw6,cw8])
def mc1354 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw39,cw7,cw1,cw4,cw6,cw8])
def mc1355 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw39,cw7,cw1,cw3,cw6,cw8])
def mc1356 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw39,cw7,cw1,cw3,cw4,cw8])
def mc1357 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw39,cw7,cw1,cw3,cw4,cw8])
def mc1358 : SearchState := (0,0xf03f000fff03f03faaaaaaaaaaaaaaaa,[cw80,cw2,cw8,cw39,cw7,cw1,cw3,cw4,cw6])
def mc1359 : SearchState := (3,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw1,cw3,cw4,cw2,cw6,cw7])
def mc1360 : SearchState := (1,0x3f0000000000000000000,[cw29,cw44,cw1,cw3,cw4,cw2,cw6,cw7])
def mc1361 : SearchState := (1,0xffff00003f03ffff9e79e79e79e79e79,[cw83,cw44,cw1,cw3,cw4,cw2,cw6,cw7])
def mc1362 : SearchState := (1,0x3f0000000000000000000000,[cw53,cw44,cw3,cw1,cw4,cw2,cw6,cw7])
def mc1363 : SearchState := (1,0xfff00003ffff000efbefbefbefbefbe,[cw174,cw44,cw3,cw1,cw4,cw2,cw6,cw7])
def mc1364 : SearchState := (1,0x8208208208208208,[cw84,cw44,cw4,cw1,cw3,cw2,cw6,cw7])
def mc1365 : SearchState := (1,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw44,cw4,cw1,cw3,cw2,cw6,cw7])
def mc1366 : SearchState := (1,0x3f0000000000000000000000000000,[cw57,cw44,cw2,cw1,cw3,cw4,cw6,cw7])
def mc1367 : SearchState := (1,0xffff000fff03f03faebaebaebaebaeba,[cw86,cw44,cw2,cw1,cw3,cw4,cw6,cw7])
def mc1368 : SearchState := (1,0xfc00000000000000000000000000000,[cw24,cw44,cw6,cw1,cw3,cw4,cw2,cw7])
def mc1369 : SearchState := (1,0xfff03f03f03f000df7df7df7df7df7d,[cw175,cw44,cw6,cw1,cw3,cw4,cw2,cw7])
def mc1370 : SearchState := (1,0x410410410410410,[cw87,cw44,cw7,cw1,cw3,cw4,cw2,cw6])
def mc1371 : SearchState := (1,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw44,cw7,cw1,cw3,cw4,cw2,cw6])
def mc1372 : SearchState := (2,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw44,cw4,cw2,cw6,cw7])
def mc1373 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw44,cw4,cw2,cw6,cw7])
def mc1374 : SearchState := (1,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw44,cw3,cw2,cw6,cw7])
def mc1375 : SearchState := (1,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw44,cw3,cw4,cw6,cw7])
def mc1376 : SearchState := (1,0xffff00003f03f03f8e38e38e38e38e38,[cw176,cw1,cw2,cw3,cw4,cw6,cw7])
def mc1377 : SearchState := (0,0xffff00003f03f03f8e38e38e38e38e38,[cw176,cw0,cw1,cw2,cw3,cw4,cw6,cw7])
def mc1378 : SearchState := (0,0xffff00003f03f03f8e38e38e38e38e38,[cw176,cw44,cw1,cw2,cw3,cw4,cw6,cw7])
def mc1379 : SearchState := (1,0xf00000003ffc003f6186186186186186,[cw9,cw1,cw2,cw44,cw4,cw6,cw7])
def mc1380 : SearchState := (0,0xf00000003ffc003f6186186186186186,[cw9,cw0,cw1,cw2,cw44,cw4,cw6,cw7])
def mc1381 : SearchState := (0,0xf00000003ffc003f6186186186186186,[cw9,cw3,cw1,cw2,cw44,cw4,cw6,cw7])
def mc1382 : SearchState := (1,0xf000ffffc000003f8208208208208208,[cw10,cw1,cw2,cw44,cw3,cw6,cw7])
def mc1383 : SearchState := (0,0xf000ffffc000003f8208208208208208,[cw10,cw0,cw1,cw2,cw44,cw3,cw6,cw7])
def mc1384 : SearchState := (0,0xf000ffffc000003f8208208208208208,[cw10,cw4,cw1,cw2,cw44,cw3,cw6,cw7])
def mc1385 : SearchState := (1,0xffc003f00000003f5145145145145145,[cw12,cw1,cw2,cw44,cw3,cw4,cw7])
def mc1386 : SearchState := (0,0xffc003f00000003f5145145145145145,[cw12,cw0,cw1,cw2,cw44,cw3,cw4,cw7])
def mc1387 : SearchState := (0,0xffc003f00000003f5145145145145145,[cw12,cw6,cw1,cw2,cw44,cw3,cw4,cw7])
def mc1388 : SearchState := (1,0xf000fc0000fc0fff0410410410410410,[cw13,cw1,cw2,cw44,cw3,cw4,cw6])
def mc1389 : SearchState := (0,0xf000fc0000fc0fff0410410410410410,[cw13,cw0,cw1,cw2,cw44,cw3,cw4,cw6])
def mc1390 : SearchState := (0,0xf000fc0000fc0fff0410410410410410,[cw13,cw7,cw1,cw2,cw44,cw3,cw4,cw6])
def mc1391 : SearchState := (1,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw0,cw44,cw3,cw4,cw6,cw7])
def mc1392 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw0,cw44,cw3,cw4,cw6,cw7])
def mc1393 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw2,cw0,cw44,cw3,cw4,cw6,cw7])
def mc1394 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw0,cw2,cw44,cw4,cw6,cw7])
def mc1395 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw0,cw2,cw44,cw4,cw6,cw7])
def mc1396 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw3,cw0,cw2,cw44,cw4,cw6,cw7])
def mc1397 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw0,cw2,cw44,cw3,cw4,cw7])
def mc1398 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw0,cw2,cw44,cw3,cw4,cw7])
def mc1399 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw0,cw2,cw44,cw3,cw4,cw7])
def mc1400 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw0,cw1,cw44,cw4,cw6,cw7])
def mc1401 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw0,cw1,cw44,cw4,cw6,cw7])
def mc1402 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw0,cw1,cw44,cw4,cw6,cw7])
def mc1403 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw0,cw1,cw44,cw3,cw4,cw7])
def mc1404 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw0,cw1,cw44,cw3,cw4,cw7])
def mc1405 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw6,cw0,cw1,cw44,cw3,cw4,cw7])
def mc1406 : SearchState := (1,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw44,cw3,cw4,cw6,cw7])
def mc1407 : SearchState := (3,0xffc003f00003ffff5145145145145145,[cw17,cw44,cw3,cw4,cw2,cw7])
def mc1408 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw44,cw3,cw4,cw2,cw7])
def mc1409 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw44,cw3,cw4,cw2,cw7])
def mc1410 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw44,cw3,cw4,cw2,cw7])
def mc1411 : SearchState := (1,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw44,cw3,cw4,cw2,cw6])
def mc1412 : SearchState := (3,0xf03f000ffffc003f6186186186186186,[cw18,cw44,cw1,cw4,cw6,cw7])
def mc1413 : SearchState := (1,0x3f00003f0000000000000000000000,[cw177,cw18,cw44,cw1,cw4,cw6,cw7])
def mc1414 : SearchState := (1,0xffff000ffffff03fefbefbefbefbefbe,[cw178,cw18,cw44,cw1,cw4,cw6,cw7])
def mc1415 : SearchState := (1,0xf00000000000003f0000000000000000,[cw0,cw18,cw1,cw44,cw4,cw6,cw7])
def mc1416 : SearchState := (1,0xf03f000fffffffff71c71c71c71c71c7,[cw54,cw18,cw1,cw44,cw4,cw6,cw7])
def mc1417 : SearchState := (1,0xfc00000000000000000000000,[cw55,cw18,cw4,cw44,cw1,cw6,cw7])
def mc1418 : SearchState := (1,0xf03ffffffffc003fe38e38e38e38e38e,[cw56,cw18,cw4,cw44,cw1,cw6,cw7])
def mc1419 : SearchState := (1,0x4104104104104104,[cw20,cw18,cw6,cw44,cw1,cw4,cw7])
def mc1420 : SearchState := (2,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw18,cw44,cw1,cw4,cw7])
def mc1421 : SearchState := (1,0xffff03fffffc003f71c71c71c71c71c7,[cw59,cw18,cw6,cw44,cw1,cw4,cw7])
def mc1422 : SearchState := (1,0xfc00000000000000000000,[cw60,cw18,cw7,cw44,cw1,cw4,cw6])
def mc1423 : SearchState := (1,0xf03ffc0ffffc0fff6596596596596596,[cw61,cw18,cw7,cw44,cw1,cw4,cw6])
def mc1424 : SearchState := (1,0xffff00003f03ffff9e79e79e79e79e79,[cw83,cw44,cw1,cw18,cw4,cw6,cw7])
def mc1425 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw18,cw44,cw4,cw7])
def mc1426 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw18,cw44,cw4,cw7])
def mc1427 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw44,cw1,cw4,cw6,cw7])
def mc1428 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw44,cw1,cw4,cw6,cw7])
def mc1429 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw44,cw1,cw4,cw6,cw7])
def mc1430 : SearchState := (1,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw44,cw1,cw3,cw6,cw7])
def mc1431 : SearchState := (2,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw44,cw1,cw3,cw4,cw7])
def mc1432 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw44,cw1,cw3,cw4,cw7])
def mc1433 : SearchState := (1,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw44,cw1,cw3,cw4,cw6])
def mc1434 : SearchState := (2,0xfff00003f03f0008e38e38e38e38e38,[cw44,cw5,cw1,cw3,cw4,cw2,cw6,cw7])
def mc1435 : SearchState := (0,0x3f0000000000000000000,[cw29,cw44,cw1,cw5,cw3,cw4,cw2,cw6,cw7])
def mc1436 : SearchState := (0,0xffff00003f03ffff9e79e79e79e79e79,[cw83,cw44,cw1,cw5,cw3,cw4,cw2,cw6,cw7])
def mc1437 : SearchState := (0,0x3f0000000000000000000000,[cw53,cw44,cw3,cw5,cw1,cw4,cw2,cw6,cw7])
def mc1438 : SearchState := (0,0xfff00003ffff000efbefbefbefbefbe,[cw174,cw44,cw3,cw5,cw1,cw4,cw2,cw6,cw7])
def mc1439 : SearchState := (0,0x8208208208208208,[cw84,cw44,cw4,cw5,cw1,cw3,cw2,cw6,cw7])
def mc1440 : SearchState := (1,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw4,cw5,cw1,cw3,cw2,cw6,cw7])
def mc1441 : SearchState := (0,0xfffffffff03f0008e38e38e38e38e38,[cw85,cw44,cw4,cw5,cw1,cw3,cw2,cw6,cw7])
def mc1442 : SearchState := (0,0x3f0000000000000000000000000000,[cw57,cw44,cw2,cw5,cw1,cw3,cw4,cw6,cw7])
def mc1443 : SearchState := (0,0xffff000fff03f03faebaebaebaebaeba,[cw86,cw44,cw2,cw5,cw1,cw3,cw4,cw6,cw7])
def mc1444 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw44,cw6,cw5,cw1,cw3,cw4,cw2,cw7])
def mc1445 : SearchState := (0,0xfff03f03f03f000df7df7df7df7df7d,[cw175,cw44,cw6,cw5,cw1,cw3,cw4,cw2,cw7])
def mc1446 : SearchState := (0,0x410410410410410,[cw87,cw44,cw7,cw5,cw1,cw3,cw4,cw2,cw6])
def mc1447 : SearchState := (1,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw7,cw5,cw1,cw3,cw4,cw2,cw6])
def mc1448 : SearchState := (0,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw44,cw7,cw5,cw1,cw3,cw4,cw2,cw6])
def mc1449 : SearchState := (1,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw44,cw3,cw4,cw2,cw6,cw7])
def mc1450 : SearchState := (0,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw5,cw1,cw44,cw3,cw4,cw2,cw6,cw7])
def mc1451 : SearchState := (1,0xfff00003ffc00006db6db6db6db6db6,[cw88,cw3,cw44,cw1,cw4,cw2,cw6,cw7])
def mc1452 : SearchState := (0,0xfff00003ffc00006db6db6db6db6db6,[cw88,cw5,cw3,cw44,cw1,cw4,cw2,cw6,cw7])
def mc1453 : SearchState := (1,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw44,cw1,cw3,cw2,cw6,cw7])
def mc1454 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw5,cw4,cw44,cw1,cw3,cw2,cw6,cw7])
def mc1455 : SearchState := (1,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw2,cw44,cw1,cw3,cw4,cw6,cw7])
def mc1456 : SearchState := (0,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw2,cw44,cw1,cw3,cw4,cw6,cw7])
def mc1457 : SearchState := (1,0xfff03f0000000005d75d75d75d75d75,[cw90,cw6,cw44,cw1,cw3,cw4,cw2,cw7])
def mc1458 : SearchState := (0,0xfff03f0000000005d75d75d75d75d75,[cw90,cw5,cw6,cw44,cw1,cw3,cw4,cw2,cw7])
def mc1459 : SearchState := (2,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw44,cw1,cw3,cw4,cw2,cw6])
def mc1460 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw44,cw1,cw3,cw4,cw2,cw6])
def mc1461 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw44,cw1,cw3,cw4,cw2,cw6])
def mc1462 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw7,cw44,cw1,cw3,cw4,cw2,cw6])
def mc1463 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw44,cw5,cw4,cw2,cw6,cw7])
def mc1464 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw44,cw5,cw4,cw2,cw6,cw7])
def mc1465 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw44,cw5,cw3,cw2,cw6,cw7])
def mc1466 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw44,cw5,cw3,cw4,cw6,cw7])
def mc1467 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw44,cw5,cw3,cw4,cw6,cw7])
def mc1468 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw44,cw5,cw3,cw4,cw2,cw7])
def mc1469 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw44,cw5,cw3,cw4,cw2,cw7])
def mc1470 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw44,cw5,cw3,cw4,cw2,cw7])
def mc1471 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw44,cw5,cw3,cw4,cw2,cw7])
def mc1472 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw7,cw44,cw5,cw3,cw4,cw2,cw6])
def mc1473 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw44,cw5,cw1,cw4,cw6,cw7])
def mc1474 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw44,cw5,cw1,cw4,cw6,cw7])
def mc1475 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw44,cw5,cw1,cw4,cw6,cw7])
def mc1476 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw44,cw5,cw1,cw4,cw6,cw7])
def mc1477 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw44,cw5,cw1,cw3,cw6,cw7])
def mc1478 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw44,cw5,cw1,cw3,cw4,cw7])
def mc1479 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw44,cw5,cw1,cw3,cw4,cw7])
def mc1480 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw7,cw44,cw5,cw1,cw3,cw4,cw6])
def mc1481 : SearchState := (2,0xfc003fffffc08e38e38e38e38e38,[cw40,cw7,cw1,cw3,cw4,cw5,cw2,cw6])
def mc1482 : SearchState := (0,0x3ffc00000000000000000,[cw167,cw40,cw1,cw7,cw3,cw4,cw5,cw2,cw6])
def mc1483 : SearchState := (0,0xf000fc003fffffff9e79e79e79e79e79,[cw179,cw40,cw1,cw7,cw3,cw4,cw5,cw2,cw6])
def mc1484 : SearchState := (1,0x3ffc00000000000000000000,[cw138,cw40,cw7,cw1,cw4,cw5,cw2,cw6])
def mc1485 : SearchState := (0,0x3ffc00000000000000000000,[cw138,cw40,cw3,cw7,cw1,cw4,cw5,cw2,cw6])
def mc1486 : SearchState := (0,0xfc003fffffc0efbefbefbefbefbe,[cw180,cw40,cw3,cw7,cw1,cw4,cw5,cw2,cw6])
def mc1487 : SearchState := (0,0xfc00000000008208208208208208,[cw170,cw40,cw4,cw7,cw1,cw3,cw5,cw2,cw6])
def mc1488 : SearchState := (1,0xffffffffffc08e38e38e38e38e38,[cw137,cw4,cw7,cw1,cw3,cw5,cw2,cw6])
def mc1489 : SearchState := (0,0xffffffffffc08e38e38e38e38e38,[cw137,cw40,cw4,cw7,cw1,cw3,cw5,cw2,cw6])
def mc1490 : SearchState := (0,0xc30c30c30c30c30,[cw181,cw40,cw5,cw7,cw1,cw3,cw4,cw2,cw6])
def mc1491 : SearchState := (1,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw40,cw7,cw1,cw3,cw4,cw2,cw6])
def mc1492 : SearchState := (1,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw5,cw7,cw1,cw3,cw4,cw2,cw6])
def mc1493 : SearchState := (0,0xffffc003fffffc08e38e38e38e38e38,[cw79,cw40,cw5,cw7,cw1,cw3,cw4,cw2,cw6])
def mc1494 : SearchState := (0,0xf03ffc0fffffffffaebaebaebaebaeba,[cw182,cw40,cw2,cw7,cw1,cw3,cw4,cw5,cw6])
def mc1495 : SearchState := (0,0xfc0fff03fffffc0df7df7df7df7df7d,[cw183,cw40,cw6,cw7,cw1,cw3,cw4,cw5,cw2])
def mc1496 : SearchState := (1,0xf000fc0000ffffff1451451451451451,[cw38,cw1,cw40,cw3,cw4,cw5,cw2,cw6])
def mc1497 : SearchState := (0,0xf000fc0000ffffff1451451451451451,[cw38,cw7,cw1,cw40,cw3,cw4,cw5,cw2,cw6])
def mc1498 : SearchState := (0,0xffffc0fc0fc08618618618618618,[cw132,cw7,cw4,cw40,cw1,cw3,cw5,cw2,cw6])
def mc1499 : SearchState := (2,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw40,cw1,cw3,cw4,cw2,cw6])
def mc1500 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw40,cw1,cw3,cw4,cw2,cw6])
def mc1501 : SearchState := (1,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw5,cw40,cw1,cw3,cw4,cw2,cw6])
def mc1502 : SearchState := (0,0xffffc0000fc0fc00c30c30c30c30c30,[cw39,cw7,cw5,cw40,cw1,cw3,cw4,cw2,cw6])
def mc1503 : SearchState := (1,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw2,cw40,cw1,cw3,cw4,cw5,cw6])
def mc1504 : SearchState := (0,0xf03ffc0fc0fc0fff2492492492492492,[cw65,cw7,cw2,cw40,cw1,cw3,cw4,cw5,cw6])
def mc1505 : SearchState := (1,0xfc0fff000fc0fc05555555555555555,[cw91,cw6,cw40,cw1,cw3,cw4,cw5,cw2])
def mc1506 : SearchState := (0,0xfc0fff000fc0fc05555555555555555,[cw91,cw7,cw6,cw40,cw1,cw3,cw4,cw5,cw2])
def mc1507 : SearchState := (1,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw40,cw7,cw4,cw5,cw2,cw6])
def mc1508 : SearchState := (0,0xf00000003fffffff71c71c71c71c71c7,[cw16,cw1,cw3,cw40,cw7,cw4,cw5,cw2,cw6])
def mc1509 : SearchState := (0,0xf000ffffc003ffff9249249249249249,[cw52,cw1,cw4,cw40,cw7,cw3,cw5,cw2,cw6])
def mc1510 : SearchState := (0,0xffff00000003ffff1c71c71c71c71c71,[cw63,cw1,cw5,cw40,cw7,cw3,cw4,cw2,cw6])
def mc1511 : SearchState := (0,0xf00000000000003f0000000000000000,[cw0,cw1,cw2,cw40,cw7,cw3,cw4,cw5,cw6])
def mc1512 : SearchState := (0,0xf03f000fc003ffff30c30c30c30c30c3,[cw15,cw1,cw2,cw40,cw7,cw3,cw4,cw5,cw6])
def mc1513 : SearchState := (2,0xffc003f00003ffff5145145145145145,[cw17,cw40,cw7,cw3,cw4,cw5,cw2])
def mc1514 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw40,cw7,cw3,cw4,cw5,cw2])
def mc1515 : SearchState := (1,0xffc003f00003ffff5145145145145145,[cw17,cw6,cw40,cw7,cw3,cw4,cw5,cw2])
def mc1516 : SearchState := (0,0xffc003f00003ffff5145145145145145,[cw17,cw1,cw6,cw40,cw7,cw3,cw4,cw5,cw2])
def mc1517 : SearchState := (0,0xfffffffc0000e38e38e38e38e38e,[cw106,cw3,cw4,cw40,cw7,cw1,cw5,cw2,cw6])
def mc1518 : SearchState := (0,0xfff00003ffc00006db6db6db6db6db6,[cw88,cw3,cw5,cw40,cw7,cw1,cw4,cw2,cw6])
def mc1519 : SearchState := (2,0xf03f000ffffc003f6186186186186186,[cw18,cw40,cw7,cw1,cw4,cw5,cw6])
def mc1520 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw40,cw7,cw1,cw4,cw5,cw6])
def mc1521 : SearchState := (1,0xf03f000ffffc003f6186186186186186,[cw18,cw2,cw40,cw7,cw1,cw4,cw5,cw6])
def mc1522 : SearchState := (0,0xf03f000ffffc003f6186186186186186,[cw18,cw3,cw2,cw40,cw7,cw1,cw4,cw5,cw6])
def mc1523 : SearchState := (2,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw40,cw7,cw1,cw4,cw5,cw2])
def mc1524 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw40,cw7,cw1,cw4,cw5,cw2])
def mc1525 : SearchState := (1,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw6,cw40,cw7,cw1,cw4,cw5,cw2])
def mc1526 : SearchState := (0,0xfc003f03ffc000071c71c71c71c71c7,[cw41,cw3,cw6,cw40,cw7,cw1,cw4,cw5,cw2])
def mc1527 : SearchState := (1,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw40,cw7,cw1,cw3,cw2,cw6])
def mc1528 : SearchState := (0,0xfffffffc00000008e38e38e38e38e38,[cw42,cw4,cw5,cw40,cw7,cw1,cw3,cw2,cw6])
def mc1529 : SearchState := (0,0xf03fffffc000003fa28a28a28a28a28a,[cw64,cw4,cw2,cw40,cw7,cw1,cw3,cw5,cw6])
def mc1530 : SearchState := (0,0xfc0ffffc0000000d34d34d34d34d34d,[cw89,cw4,cw6,cw40,cw7,cw1,cw3,cw5,cw2])
def mc1531 : SearchState := (0,0x3f0000000000000000000000000000,[cw57,cw5,cw2,cw40,cw7,cw1,cw3,cw4,cw6])
def mc1532 : SearchState := (0,0xffff000fc000003f2cb2cb2cb2cb2cb2,[cw31,cw5,cw2,cw40,cw7,cw1,cw3,cw4,cw6])
def mc1533 : SearchState := (0,0xfc00000000000000000000000000000,[cw24,cw5,cw6,cw40,cw7,cw1,cw3,cw4,cw2])
def mc1534 : SearchState := (0,0xfff03f0000000005d75d75d75d75d75,[cw90,cw5,cw6,cw40,cw7,cw1,cw3,cw4,cw2])
def mc1535 : SearchState := (1,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw40,cw7,cw1,cw3,cw4,cw5])
def mc1536 : SearchState := (0,0xffff03ffc000003f71c71c71c71c71c7,[cw19,cw2,cw6,cw40,cw7,cw1,cw3,cw4,cw5])

def tab0 : List (ℕ × ℕ × List W) :=
  [(2, 0xf00000003fffffff71c71c71c71c71c7, [0xf00000003fffffff71c71c71c71c71c7, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab1 : List (ℕ × ℕ × List W) :=
  [(1, 0xf00000003fffffff71c71c71c71c71c7, [0xf00000003fffffff71c71c71c71c71c7, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab2 : List (ℕ × ℕ × List W) :=
  [(1, 0xf000ffffc003ffff9249249249249249, [0xf000ffffc003ffff9249249249249249, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab3 : List (ℕ × ℕ × List W) :=
  [(1, 0xffff00000003ffff1c71c71c71c71c71, [0xffff00000003ffff1c71c71c71c71c71, 0xf00000000003ffff1041041041041041, 0xfff0000000000000c30c30c30c30c30, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab4 : List (ℕ × ℕ × List W) :=
  [(1, 0xf00000000000003f0000000000000000, [0xf00000000000003f0000000000000000, 0xf00000000003ffff1041041041041041, 0xf03f000fc000003f2082082082082082, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab5 : List (ℕ × ℕ × List W) :=
  [(1, 0xf03f000fc003ffff30c30c30c30c30c3, [0xf03f000fc003ffff30c30c30c30c30c3, 0xf00000000003ffff1041041041041041, 0xf03f000fc000003f2082082082082082, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab6 : List (ℕ × ℕ × List W) :=
  [(1, 0x1041041041041041, [0x1041041041041041, 0xf00000000003ffff1041041041041041, 0xfc003f0000000005145145145145145, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab7 : List (ℕ × ℕ × List W) :=
  [(3, 0xffc003f00003ffff5145145145145145, [0xffc003f00003ffff5145145145145145, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab8 : List (ℕ × ℕ × List W) :=
  [(2, 0xffc003f00003ffff5145145145145145, [0xffc003f00003ffff5145145145145145, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab9 : List (ℕ × ℕ × List W) :=
  [(2, 0xffc003f00003ffff5145145145145145, [0xffc003f00003ffff5145145145145145, 0xfc003f0000000005145145145145145, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab10 : List (ℕ × ℕ × List W) :=
  [(1, 0xffc003f00003ffff5145145145145145, [0xffc003f00003ffff5145145145145145, 0xf00000000003ffff1041041041041041, 0xfc003f0000000005145145145145145, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab11 : List (ℕ × ℕ × List W) :=
  [(1, 0xfc00000000000000000, [0xfc00000000000000000, 0xf00000000003ffff1041041041041041, 0xfc0000fc0fc00410410410410410, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab12 : List (ℕ × ℕ × List W) :=
  [(1, 0xf000fc0000ffffff1451451451451451, [0xf000fc0000ffffff1451451451451451, 0xf00000000003ffff1041041041041041, 0xfc0000fc0fc00410410410410410, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab13 : List (ℕ × ℕ × List W) :=
  [(1, 0x3f0000000000000000000, [0x3f0000000000000000000, 0xf00000000003ffff1041041041041041, 0x3f03f0008a28a28a28a28a28, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab14 : List (ℕ × ℕ × List W) :=
  [(1, 0xf00000003f03ffff9a69a69a69a69a69, [0xf00000003f03ffff9a69a69a69a69a69, 0xf00000000003ffff1041041041041041, 0x3f03f0008a28a28a28a28a28, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab15 : List (ℕ × ℕ × List W) :=
  [(1, 0xfffffffc0000e38e38e38e38e38e, [0xfffffffc0000e38e38e38e38e38e, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf00000000003ffff1041041041041041, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab16 : List (ℕ × ℕ × List W) :=
  [(1, 0xfff00003ffc00006db6db6db6db6db6, [0xfff00003ffc00006db6db6db6db6db6, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab17 : List (ℕ × ℕ × List W) :=
  [(1, 0x2082082082082082, [0x2082082082082082, 0x3ffc00006186186186186186, 0xf03f000fc000003f2082082082082082, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab18 : List (ℕ × ℕ × List W) :=
  [(3, 0xf03f000ffffc003f6186186186186186, [0xf03f000ffffc003f6186186186186186, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab19 : List (ℕ × ℕ × List W) :=
  [(2, 0xf03f000ffffc003f6186186186186186, [0xf03f000ffffc003f6186186186186186, 0x3ffc00006186186186186186, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab20 : List (ℕ × ℕ × List W) :=
  [(2, 0xf03f000ffffc003f6186186186186186, [0xf03f000ffffc003f6186186186186186, 0xf03f000fc000003f2082082082082082, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab21 : List (ℕ × ℕ × List W) :=
  [(1, 0xf03f000ffffc003f6186186186186186, [0xf03f000ffffc003f6186186186186186, 0x3ffc00006186186186186186, 0xf03f000fc000003f2082082082082082, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab22 : List (ℕ × ℕ × List W) :=
  [(1, 0x4104104104104104, [0x4104104104104104, 0x3ffc00006186186186186186, 0xfc003f0000000005145145145145145, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab23 : List (ℕ × ℕ × List W) :=
  [(3, 0xfc003f03ffc000071c71c71c71c71c7, [0xfc003f03ffc000071c71c71c71c71c7, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab24 : List (ℕ × ℕ × List W) :=
  [(2, 0xfc003f03ffc000071c71c71c71c71c7, [0xfc003f03ffc000071c71c71c71c71c7, 0x3ffc00006186186186186186, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab25 : List (ℕ × ℕ × List W) :=
  [(2, 0xfc003f03ffc000071c71c71c71c71c7, [0xfc003f03ffc000071c71c71c71c71c7, 0xfc003f0000000005145145145145145, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab26 : List (ℕ × ℕ × List W) :=
  [(1, 0xfc003f03ffc000071c71c71c71c71c7, [0xfc003f03ffc000071c71c71c71c71c7, 0x3ffc00006186186186186186, 0xfc003f0000000005145145145145145, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab27 : List (ℕ × ℕ × List W) :=
  [(1, 0xfc00000000000000000000, [0xfc00000000000000000000, 0x3ffc00006186186186186186, 0xfc0000fc0fc00410410410410410, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab28 : List (ℕ × ℕ × List W) :=
  [(1, 0xfc003ffc0fc06596596596596596, [0xfc003ffc0fc06596596596596596, 0x3ffc00006186186186186186, 0xfc0000fc0fc00410410410410410, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab29 : List (ℕ × ℕ × List W) :=
  [(1, 0x3f0000000000000000000000, [0x3f0000000000000000000000, 0x3ffc00006186186186186186, 0x3f03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab30 : List (ℕ × ℕ × List W) :=
  [(1, 0x3ffff000ebaebaebaebaebae, [0x3ffff000ebaebaebaebaebae, 0x3ffc00006186186186186186, 0x3f03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab31 : List (ℕ × ℕ × List W) :=
  [(2, 0xfffffffc00000008e38e38e38e38e38, [0xfffffffc00000008e38e38e38e38e38, 0xffffc00000008208208208208208, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab32 : List (ℕ × ℕ × List W) :=
  [(1, 0xfffffffc00000008e38e38e38e38e38, [0xfffffffc00000008e38e38e38e38e38, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab33 : List (ℕ × ℕ × List W) :=
  [(1, 0xfc00000000000000000000000, [0xfc00000000000000000000000, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab34 : List (ℕ × ℕ × List W) :=
  [(1, 0xf03fffffc000003fa28a28a28a28a28a, [0xf03fffffc000003fa28a28a28a28a28a, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab35 : List (ℕ × ℕ × List W) :=
  [(1, 0x3f0000000000000000000000000, [0x3f0000000000000000000000000, 0xffffc00000008208208208208208, 0xfc003f0000000005145145145145145, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab36 : List (ℕ × ℕ × List W) :=
  [(1, 0xfc0ffffc0000000d34d34d34d34d34d, [0xfc0ffffc0000000d34d34d34d34d34d, 0xffffc00000008208208208208208, 0xfc003f0000000005145145145145145, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab37 : List (ℕ × ℕ × List W) :=
  [(1, 0xfc00000000000000000000000000, [0xfc00000000000000000000000000, 0xffffc00000008208208208208208, 0xfc0000fc0fc00410410410410410, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab38 : List (ℕ × ℕ × List W) :=
  [(1, 0xffffc0fc0fc08618618618618618, [0xffffc0fc0fc08618618618618618, 0xffffc00000008208208208208208, 0xfc0000fc0fc00410410410410410, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab39 : List (ℕ × ℕ × List W) :=
  [(1, 0x8208208208208208, [0x8208208208208208, 0xffffc00000008208208208208208, 0x3f03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab40 : List (ℕ × ℕ × List W) :=
  [(3, 0xffffff03f0008a28a28a28a28a28, [0xffffff03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab41 : List (ℕ × ℕ × List W) :=
  [(2, 0xffffff03f0008a28a28a28a28a28, [0xffffff03f0008a28a28a28a28a28, 0xffffc00000008208208208208208, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab42 : List (ℕ × ℕ × List W) :=
  [(2, 0xffffff03f0008a28a28a28a28a28, [0xffffff03f0008a28a28a28a28a28, 0x3f03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab43 : List (ℕ × ℕ × List W) :=
  [(1, 0xffffff03f0008a28a28a28a28a28, [0xffffff03f0008a28a28a28a28a28, 0xffffc00000008208208208208208, 0x3f03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab44 : List (ℕ × ℕ × List W) :=
  [(1, 0x3f0000000000000000000000000000, [0x3f0000000000000000000000000000, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab45 : List (ℕ × ℕ × List W) :=
  [(1, 0xffff000fc000003f2cb2cb2cb2cb2cb2, [0xffff000fc000003f2cb2cb2cb2cb2cb2, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab46 : List (ℕ × ℕ × List W) :=
  [(1, 0xfc00000000000000000000000000000, [0xfc00000000000000000000000000000, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab47 : List (ℕ × ℕ × List W) :=
  [(1, 0xfff03f0000000005d75d75d75d75d75, [0xfff03f0000000005d75d75d75d75d75, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab48 : List (ℕ × ℕ × List W) :=
  [(1, 0x410410410410410, [0x410410410410410, 0xfff0000000000000c30c30c30c30c30, 0xfc0000fc0fc00410410410410410, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab49 : List (ℕ × ℕ × List W) :=
  [(3, 0xffffc0000fc0fc00c30c30c30c30c30, [0xffffc0000fc0fc00c30c30c30c30c30, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab50 : List (ℕ × ℕ × List W) :=
  [(2, 0xffffc0000fc0fc00c30c30c30c30c30, [0xffffc0000fc0fc00c30c30c30c30c30, 0xfff0000000000000c30c30c30c30c30, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab51 : List (ℕ × ℕ × List W) :=
  [(2, 0xffffc0000fc0fc00c30c30c30c30c30, [0xffffc0000fc0fc00c30c30c30c30c30, 0xfc0000fc0fc00410410410410410, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab52 : List (ℕ × ℕ × List W) :=
  [(1, 0xffffc0000fc0fc00c30c30c30c30c30, [0xffffc0000fc0fc00c30c30c30c30c30, 0xfff0000000000000c30c30c30c30c30, 0xfc0000fc0fc00410410410410410, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab53 : List (ℕ × ℕ × List W) :=
  [(1, 0x820820820820820, [0x820820820820820, 0xfff0000000000000c30c30c30c30c30, 0x3f03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab54 : List (ℕ × ℕ × List W) :=
  [(3, 0xfff00003f03f0008e38e38e38e38e38, [0xfff00003f03f0008e38e38e38e38e38, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab55 : List (ℕ × ℕ × List W) :=
  [(2, 0xfff00003f03f0008e38e38e38e38e38, [0xfff00003f03f0008e38e38e38e38e38, 0xfff0000000000000c30c30c30c30c30, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab56 : List (ℕ × ℕ × List W) :=
  [(2, 0xfff00003f03f0008e38e38e38e38e38, [0xfff00003f03f0008e38e38e38e38e38, 0x3f03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab57 : List (ℕ × ℕ × List W) :=
  [(1, 0xfff00003f03f0008e38e38e38e38e38, [0xfff00003f03f0008e38e38e38e38e38, 0xfff0000000000000c30c30c30c30c30, 0x3f03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab58 : List (ℕ × ℕ × List W) :=
  [(2, 0xffff03ffc000003f71c71c71c71c71c7, [0xffff03ffc000003f71c71c71c71c71c7, 0xf03f000fc000003f2082082082082082, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab59 : List (ℕ × ℕ × List W) :=
  [(1, 0xffff03ffc000003f71c71c71c71c71c7, [0xffff03ffc000003f71c71c71c71c71c7, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28])]

def tab60 : List (ℕ × ℕ × List W) :=
  [(1, 0xf03ffc0fc0fc0fff2492492492492492, [0xf03ffc0fc0fc0fff2492492492492492, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28])]

def tab61 : List (ℕ × ℕ × List W) :=
  [(1, 0xf03f000fff03f03faaaaaaaaaaaaaaaa, [0xf03f000fff03f03faaaaaaaaaaaaaaaa, 0xf03f000fc000003f2082082082082082, 0x3f03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410])]

def tab62 : List (ℕ × ℕ × List W) :=
  [(1, 0xfc0fff000fc0fc05555555555555555, [0xfc0fff000fc0fc05555555555555555, 0xfc003f0000000005145145145145145, 0xfc0000fc0fc00410410410410410, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0x3f03f0008a28a28a28a28a28])]

def tab63 : List (ℕ × ℕ × List W) :=
  [(1, 0xfc003f03f03f000db6db6db6db6db6d, [0xfc003f03f03f000db6db6db6db6db6d, 0xfc003f0000000005145145145145145, 0x3f03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc0000fc0fc00410410410410410])]

def tab64 : List (ℕ × ℕ × List W) :=
  [(2, 0xfc003fffffc08e38e38e38e38e38, [0xfc003fffffc08e38e38e38e38e38, 0xfc0000fc0fc00410410410410410, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145])]

def tab65 : List (ℕ × ℕ × List W) :=
  [(1, 0xfc003fffffc08e38e38e38e38e38, [0xfc003fffffc08e38e38e38e38e38, 0xfc0000fc0fc00410410410410410, 0x3f03f0008a28a28a28a28a28, 0xf00000000003ffff1041041041041041, 0x3ffc00006186186186186186, 0xffffc00000008208208208208208, 0xfff0000000000000c30c30c30c30c30, 0xf03f000fc000003f2082082082082082, 0xfc003f0000000005145145145145145])]

def table : List (ℕ × ℕ × List W) := tab0 ++ tab1 ++ tab2 ++ tab3 ++ tab4 ++ tab5 ++ tab6 ++ tab7 ++ tab8 ++ tab9 ++ tab10 ++ tab11 ++ tab12 ++ tab13 ++ tab14 ++ tab15 ++ tab16 ++ tab17 ++ tab18 ++ tab19 ++ tab20 ++ tab21 ++ tab22 ++ tab23 ++ tab24 ++ tab25 ++ tab26 ++ tab27 ++ tab28 ++ tab29 ++ tab30 ++ tab31 ++ tab32 ++ tab33 ++ tab34 ++ tab35 ++ tab36 ++ tab37 ++ tab38 ++ tab39 ++ tab40 ++ tab41 ++ tab42 ++ tab43 ++ tab44 ++ tab45 ++ tab46 ++ tab47 ++ tab48 ++ tab49 ++ tab50 ++ tab51 ++ tab52 ++ tab53 ++ tab54 ++ tab55 ++ tab56 ++ tab57 ++ tab58 ++ tab59 ++ tab60 ++ tab61 ++ tab62 ++ tab63 ++ tab64 ++ tab65

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1False : stateResult 8 mc1 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc2False : stateResult 8 mc2 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc3False : stateResult 8 mc3 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc4False : stateResult 8 mc4 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc5False : stateResult 8 mc5 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc6False : stateResult 8 mc6 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc7False : stateResult 8 mc7 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc8False : stateResult 8 mc8 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc9False : stateResult 8 mc9 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc10False : stateResult 8 mc10 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc11False : stateResult 8 mc11 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc12False : stateResult 8 mc12 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc13False : stateResult 8 mc13 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc14False : stateResult 8 mc14 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc15False : stateResult 8 mc15 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc16False : stateResult 8 mc16 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc17False : stateResult 8 mc17 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc18False : stateResult 8 mc18 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc19False : stateResult 8 mc19 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc20False : stateResult 8 mc20 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc21False : stateResult 8 mc21 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc22False : stateResult 8 mc22 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc23False : stateResult 8 mc23 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc24False : stateResult 8 mc24 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc25False : stateResult 8 mc25 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc26False : stateResult 8 mc26 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc27False : stateResult 8 mc27 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc28False : stateResult 8 mc28 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc29False : stateResult 8 mc29 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc30False : stateResult 8 mc30 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc31False : stateResult 8 mc31 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc32False : stateResult 8 mc32 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc33False : stateResult 8 mc33 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc0Children : List SearchState := [mc1,mc2,mc3,mc4,mc5,mc6,mc7,mc8,mc9,mc10,mc11,mc12,mc13,mc14,mc15,mc16,mc17,mc18,mc19,mc20,mc21,mc22,mc23,mc24,mc25,mc26,mc27,mc28,mc29,mc30,mc31,mc32,mc33]
theorem mc0False : stateResult 9 mc0 = false := by
  apply coverResult (k := 6) (states := mc0Children)
  · change mc0Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc0Children, List.all_cons, List.all_nil, mc1False, mc2False, mc3False, mc4False, mc5False, mc6False, mc7False, mc8False, mc9False, mc10False, mc11False, mc12False, mc13False, mc14False, mc15False, mc16False, mc17False, mc18False, mc19False, mc20False, mc21False, mc22False, mc23False, mc24False, mc25False, mc26False, mc27False, mc28False, mc29False, mc30False, mc31False, mc32False, mc33False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc35False : stateResult 8 mc35 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc36False : stateResult 8 mc36 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc37False : stateResult 8 mc37 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc38False : stateResult 8 mc38 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc39False : stateResult 8 mc39 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc40False : stateResult 8 mc40 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc41False : stateResult 8 mc41 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc42False : stateResult 8 mc42 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc43False : stateResult 8 mc43 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc44False : stateResult 8 mc44 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc45False : stateResult 8 mc45 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc46False : stateResult 8 mc46 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc47False : stateResult 8 mc47 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc48False : stateResult 8 mc48 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc34Children : List SearchState := [mc35,mc36,mc37,mc38,mc39,mc40,mc41,mc42,mc43,mc44,mc45,mc46,mc47,mc48]
theorem mc34False : stateResult 9 mc34 = false := by
  apply coverResult (k := 6) (states := mc34Children)
  · change mc34Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc34Children, List.all_cons, List.all_nil, mc35False, mc36False, mc37False, mc38False, mc39False, mc40False, mc41False, mc42False, mc43False, mc44False, mc45False, mc46False, mc47False, mc48False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc50False : stateResult 8 mc50 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc51False : stateResult 8 mc51 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc52False : stateResult 8 mc52 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc53False : stateResult 8 mc53 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc54False : stateResult 8 mc54 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc55False : stateResult 8 mc55 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc56False : stateResult 8 mc56 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc57False : stateResult 8 mc57 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc58False : stateResult 8 mc58 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc59False : stateResult 8 mc59 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc60False : stateResult 8 mc60 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc61False : stateResult 8 mc61 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc62False : stateResult 8 mc62 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc63False : stateResult 8 mc63 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc64False : stateResult 8 mc64 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc65False : stateResult 8 mc65 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc66False : stateResult 8 mc66 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc67False : stateResult 8 mc67 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc68False : stateResult 8 mc68 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc69False : stateResult 8 mc69 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc70False : stateResult 8 mc70 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc71False : stateResult 8 mc71 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc72False : stateResult 8 mc72 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc73False : stateResult 8 mc73 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc74False : stateResult 8 mc74 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc75False : stateResult 8 mc75 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc76False : stateResult 8 mc76 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc77False : stateResult 8 mc77 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc78False : stateResult 8 mc78 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc79False : stateResult 8 mc79 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc80False : stateResult 8 mc80 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc81False : stateResult 8 mc81 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc82False : stateResult 8 mc82 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc83False : stateResult 8 mc83 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc84False : stateResult 8 mc84 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc85False : stateResult 8 mc85 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc86False : stateResult 8 mc86 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc87False : stateResult 8 mc87 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc88False : stateResult 8 mc88 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc89False : stateResult 8 mc89 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc90False : stateResult 8 mc90 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc91False : stateResult 8 mc91 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc92False : stateResult 8 mc92 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc49Children : List SearchState := [mc50,mc51,mc52,mc53,mc54,mc55,mc56,mc57,mc58,mc59,mc60,mc61,mc62,mc63,mc64,mc65,mc66,mc67,mc68,mc69,mc70,mc71,mc72,mc73,mc74,mc75,mc76,mc77,mc78,mc79,mc80,mc81,mc82,mc83,mc84,mc85,mc86,mc87,mc88,mc89,mc90,mc91,mc92]
theorem mc49False : stateResult 9 mc49 = false := by
  apply coverResult (k := 6) (states := mc49Children)
  · change mc49Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc49Children, List.all_cons, List.all_nil, mc50False, mc51False, mc52False, mc53False, mc54False, mc55False, mc56False, mc57False, mc58False, mc59False, mc60False, mc61False, mc62False, mc63False, mc64False, mc65False, mc66False, mc67False, mc68False, mc69False, mc70False, mc71False, mc72False, mc73False, mc74False, mc75False, mc76False, mc77False, mc78False, mc79False, mc80False, mc81False, mc82False, mc83False, mc84False, mc85False, mc86False, mc87False, mc88False, mc89False, mc90False, mc91False, mc92False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc94False : stateResult 8 mc94 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc95False : stateResult 8 mc95 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc96False : stateResult 8 mc96 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc97False : stateResult 8 mc97 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc98False : stateResult 8 mc98 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc99False : stateResult 8 mc99 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc100False : stateResult 8 mc100 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc101False : stateResult 8 mc101 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc102False : stateResult 8 mc102 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc103False : stateResult 8 mc103 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc104False : stateResult 8 mc104 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc105False : stateResult 8 mc105 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc106False : stateResult 8 mc106 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc107False : stateResult 8 mc107 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc108False : stateResult 8 mc108 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc109False : stateResult 8 mc109 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc110False : stateResult 8 mc110 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc111False : stateResult 8 mc111 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc112False : stateResult 8 mc112 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc113False : stateResult 8 mc113 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc114False : stateResult 8 mc114 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc115False : stateResult 8 mc115 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc116False : stateResult 8 mc116 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc117False : stateResult 8 mc117 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc118False : stateResult 8 mc118 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc119False : stateResult 8 mc119 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc120False : stateResult 8 mc120 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc121False : stateResult 8 mc121 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc122False : stateResult 8 mc122 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc123False : stateResult 8 mc123 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc124False : stateResult 8 mc124 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc125False : stateResult 8 mc125 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc126False : stateResult 8 mc126 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc127False : stateResult 8 mc127 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc128False : stateResult 8 mc128 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc129False : stateResult 8 mc129 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc130False : stateResult 8 mc130 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc131False : stateResult 8 mc131 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc132False : stateResult 8 mc132 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc133False : stateResult 8 mc133 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc134False : stateResult 8 mc134 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc135False : stateResult 8 mc135 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc136False : stateResult 8 mc136 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc137False : stateResult 8 mc137 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc138False : stateResult 8 mc138 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc93Children : List SearchState := [mc94,mc95,mc96,mc97,mc98,mc99,mc100,mc101,mc102,mc103,mc104,mc105,mc106,mc107,mc108,mc109,mc110,mc111,mc112,mc113,mc114,mc115,mc116,mc117,mc118,mc119,mc120,mc121,mc122,mc123,mc124,mc125,mc126,mc127,mc128,mc129,mc130,mc131,mc132,mc133,mc134,mc135,mc136,mc137,mc138]
theorem mc93False : stateResult 9 mc93 = false := by
  apply coverResult (k := 6) (states := mc93Children)
  · change mc93Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc93Children, List.all_cons, List.all_nil, mc94False, mc95False, mc96False, mc97False, mc98False, mc99False, mc100False, mc101False, mc102False, mc103False, mc104False, mc105False, mc106False, mc107False, mc108False, mc109False, mc110False, mc111False, mc112False, mc113False, mc114False, mc115False, mc116False, mc117False, mc118False, mc119False, mc120False, mc121False, mc122False, mc123False, mc124False, mc125False, mc126False, mc127False, mc128False, mc129False, mc130False, mc131False, mc132False, mc133False, mc134False, mc135False, mc136False, mc137False, mc138False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc140False : stateResult 8 mc140 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc141False : stateResult 8 mc141 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc142False : stateResult 8 mc142 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc143False : stateResult 8 mc143 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc144False : stateResult 8 mc144 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc145False : stateResult 8 mc145 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc146False : stateResult 8 mc146 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc147False : stateResult 8 mc147 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc148False : stateResult 8 mc148 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc149False : stateResult 8 mc149 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc150False : stateResult 8 mc150 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc151False : stateResult 8 mc151 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc152False : stateResult 8 mc152 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc153False : stateResult 8 mc153 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc154False : stateResult 8 mc154 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc155False : stateResult 8 mc155 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc139Children : List SearchState := [mc140,mc141,mc142,mc143,mc144,mc145,mc146,mc147,mc148,mc149,mc150,mc151,mc152,mc153,mc154,mc155]
theorem mc139False : stateResult 9 mc139 = false := by
  apply coverResult (k := 6) (states := mc139Children)
  · change mc139Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc139Children, List.all_cons, List.all_nil, mc140False, mc141False, mc142False, mc143False, mc144False, mc145False, mc146False, mc147False, mc148False, mc149False, mc150False, mc151False, mc152False, mc153False, mc154False, mc155False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc157False : stateResult 8 mc157 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc158False : stateResult 8 mc158 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc159False : stateResult 8 mc159 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc160False : stateResult 8 mc160 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc161False : stateResult 8 mc161 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc162False : stateResult 8 mc162 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc163False : stateResult 8 mc163 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc164False : stateResult 8 mc164 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc165False : stateResult 8 mc165 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc166False : stateResult 8 mc166 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc167False : stateResult 8 mc167 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc168False : stateResult 8 mc168 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc169False : stateResult 8 mc169 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc170False : stateResult 8 mc170 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc171False : stateResult 8 mc171 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc172False : stateResult 8 mc172 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc173False : stateResult 8 mc173 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc174False : stateResult 8 mc174 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc175False : stateResult 8 mc175 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc176False : stateResult 8 mc176 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc177False : stateResult 8 mc177 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc178False : stateResult 8 mc178 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc179False : stateResult 8 mc179 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc180False : stateResult 8 mc180 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc181False : stateResult 8 mc181 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc182False : stateResult 8 mc182 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc183False : stateResult 8 mc183 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc184False : stateResult 8 mc184 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc185False : stateResult 8 mc185 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc186False : stateResult 8 mc186 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc187False : stateResult 8 mc187 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc156Children : List SearchState := [mc157,mc158,mc159,mc160,mc161,mc162,mc163,mc164,mc165,mc166,mc167,mc168,mc169,mc170,mc171,mc172,mc173,mc174,mc175,mc176,mc177,mc178,mc179,mc180,mc181,mc182,mc183,mc184,mc185,mc186,mc187]
theorem mc156False : stateResult 9 mc156 = false := by
  apply coverResult (k := 6) (states := mc156Children)
  · change mc156Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc156Children, List.all_cons, List.all_nil, mc157False, mc158False, mc159False, mc160False, mc161False, mc162False, mc163False, mc164False, mc165False, mc166False, mc167False, mc168False, mc169False, mc170False, mc171False, mc172False, mc173False, mc174False, mc175False, mc176False, mc177False, mc178False, mc179False, mc180False, mc181False, mc182False, mc183False, mc184False, mc185False, mc186False, mc187False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc189False : stateResult 8 mc189 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc190False : stateResult 8 mc190 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc191False : stateResult 8 mc191 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc192False : stateResult 8 mc192 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc193False : stateResult 8 mc193 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc194False : stateResult 8 mc194 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc195False : stateResult 8 mc195 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc196False : stateResult 8 mc196 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc197False : stateResult 8 mc197 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc198False : stateResult 8 mc198 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc199False : stateResult 8 mc199 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc200False : stateResult 8 mc200 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc201False : stateResult 8 mc201 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc202False : stateResult 8 mc202 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc203False : stateResult 8 mc203 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc204False : stateResult 8 mc204 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc205False : stateResult 8 mc205 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc206False : stateResult 8 mc206 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc207False : stateResult 8 mc207 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc208False : stateResult 8 mc208 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc209False : stateResult 8 mc209 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc210False : stateResult 8 mc210 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc211False : stateResult 8 mc211 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc213False : stateResult 7 mc213 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc214False : stateResult 7 mc214 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc215False : stateResult 7 mc215 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc216False : stateResult 7 mc216 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc217False : stateResult 7 mc217 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc218False : stateResult 7 mc218 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc219False : stateResult 7 mc219 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc220False : stateResult 7 mc220 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc221False : stateResult 7 mc221 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc222False : stateResult 7 mc222 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc223False : stateResult 7 mc223 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc224False : stateResult 7 mc224 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc225False : stateResult 7 mc225 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc226False : stateResult 7 mc226 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc227False : stateResult 7 mc227 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc228False : stateResult 7 mc228 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc229False : stateResult 7 mc229 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc230False : stateResult 7 mc230 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc231False : stateResult 7 mc231 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc232False : stateResult 7 mc232 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc233False : stateResult 7 mc233 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc212Children : List SearchState := [mc213,mc214,mc215,mc216,mc217,mc218,mc219,mc220,mc221,mc222,mc223,mc224,mc225,mc226,mc227,mc228,mc229,mc230,mc231,mc232,mc233]
theorem mc212False : stateResult 8 mc212 = false := by
  apply coverResult (k := 5) (states := mc212Children)
  · change mc212Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc212Children, List.all_cons, List.all_nil, mc213False, mc214False, mc215False, mc216False, mc217False, mc218False, mc219False, mc220False, mc221False, mc222False, mc223False, mc224False, mc225False, mc226False, mc227False, mc228False, mc229False, mc230False, mc231False, mc232False, mc233False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc234False : stateResult 8 mc234 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc235False : stateResult 8 mc235 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc236False : stateResult 8 mc236 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc238False : stateResult 7 mc238 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc239False : stateResult 7 mc239 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc240False : stateResult 7 mc240 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc241False : stateResult 7 mc241 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc242False : stateResult 7 mc242 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc243False : stateResult 7 mc243 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc244False : stateResult 7 mc244 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc245False : stateResult 7 mc245 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc246False : stateResult 7 mc246 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc247False : stateResult 7 mc247 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc248False : stateResult 7 mc248 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc249False : stateResult 7 mc249 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc250False : stateResult 7 mc250 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc251False : stateResult 7 mc251 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc252False : stateResult 7 mc252 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc253False : stateResult 7 mc253 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc254False : stateResult 7 mc254 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc255False : stateResult 7 mc255 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc256False : stateResult 7 mc256 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc257False : stateResult 7 mc257 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc258False : stateResult 7 mc258 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc259False : stateResult 7 mc259 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc237Children : List SearchState := [mc238,mc239,mc240,mc241,mc242,mc243,mc244,mc245,mc246,mc247,mc248,mc249,mc250,mc251,mc252,mc253,mc254,mc255,mc256,mc257,mc258,mc259]
theorem mc237False : stateResult 8 mc237 = false := by
  apply coverResult (k := 5) (states := mc237Children)
  · change mc237Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc237Children, List.all_cons, List.all_nil, mc238False, mc239False, mc240False, mc241False, mc242False, mc243False, mc244False, mc245False, mc246False, mc247False, mc248False, mc249False, mc250False, mc251False, mc252False, mc253False, mc254False, mc255False, mc256False, mc257False, mc258False, mc259False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc260False : stateResult 8 mc260 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc261False : stateResult 8 mc261 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc262False : stateResult 8 mc262 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc263False : stateResult 8 mc263 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc264False : stateResult 8 mc264 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc188Children : List SearchState := [mc189,mc190,mc191,mc192,mc193,mc194,mc195,mc196,mc165,mc197,mc198,mc199,mc200,mc201,mc202,mc203,mc204,mc205,mc206,mc207,mc208,mc209,mc210,mc211,mc212,mc234,mc235,mc236,mc237,mc260,mc261,mc262,mc263,mc264]
theorem mc188False : stateResult 9 mc188 = false := by
  apply coverResult (k := 6) (states := mc188Children)
  · change mc188Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc188Children, List.all_cons, List.all_nil, mc189False, mc190False, mc191False, mc192False, mc193False, mc194False, mc195False, mc196False, mc165False, mc197False, mc198False, mc199False, mc200False, mc201False, mc202False, mc203False, mc204False, mc205False, mc206False, mc207False, mc208False, mc209False, mc210False, mc211False, mc212False, mc234False, mc235False, mc236False, mc237False, mc260False, mc261False, mc262False, mc263False, mc264False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc266False : stateResult 8 mc266 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc267False : stateResult 8 mc267 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc268False : stateResult 8 mc268 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc269False : stateResult 8 mc269 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc270False : stateResult 8 mc270 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc271False : stateResult 8 mc271 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc272False : stateResult 8 mc272 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc273False : stateResult 8 mc273 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc274False : stateResult 8 mc274 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc275False : stateResult 8 mc275 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc276False : stateResult 8 mc276 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc277False : stateResult 8 mc277 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc278False : stateResult 8 mc278 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc279False : stateResult 8 mc279 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc280False : stateResult 8 mc280 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc281False : stateResult 8 mc281 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc282False : stateResult 8 mc282 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc283False : stateResult 8 mc283 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc284False : stateResult 8 mc284 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc285False : stateResult 8 mc285 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc286False : stateResult 8 mc286 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc287False : stateResult 8 mc287 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc288False : stateResult 8 mc288 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc289False : stateResult 8 mc289 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc290False : stateResult 8 mc290 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc291False : stateResult 8 mc291 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc292False : stateResult 8 mc292 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc293False : stateResult 8 mc293 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc294False : stateResult 8 mc294 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc295False : stateResult 8 mc295 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc296False : stateResult 8 mc296 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc297False : stateResult 8 mc297 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc298False : stateResult 8 mc298 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc299False : stateResult 8 mc299 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc300False : stateResult 8 mc300 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc301False : stateResult 8 mc301 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc302False : stateResult 8 mc302 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc303False : stateResult 8 mc303 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc304False : stateResult 8 mc304 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc305False : stateResult 8 mc305 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc306False : stateResult 8 mc306 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc307False : stateResult 8 mc307 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc265Children : List SearchState := [mc266,mc267,mc268,mc269,mc270,mc271,mc272,mc273,mc274,mc275,mc276,mc277,mc278,mc279,mc280,mc281,mc282,mc283,mc284,mc285,mc286,mc287,mc288,mc289,mc290,mc291,mc292,mc293,mc294,mc295,mc296,mc297,mc298,mc299,mc300,mc301,mc302,mc303,mc304,mc305,mc306,mc307]
theorem mc265False : stateResult 9 mc265 = false := by
  apply coverResult (k := 6) (states := mc265Children)
  · change mc265Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc265Children, List.all_cons, List.all_nil, mc266False, mc267False, mc268False, mc269False, mc270False, mc271False, mc272False, mc273False, mc274False, mc275False, mc276False, mc277False, mc278False, mc279False, mc280False, mc281False, mc282False, mc283False, mc284False, mc285False, mc286False, mc287False, mc288False, mc289False, mc290False, mc291False, mc292False, mc293False, mc294False, mc295False, mc296False, mc297False, mc298False, mc299False, mc300False, mc301False, mc302False, mc303False, mc304False, mc305False, mc306False, mc307False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc309False : stateResult 8 mc309 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc310False : stateResult 8 mc310 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc311False : stateResult 8 mc311 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc312False : stateResult 8 mc312 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc313False : stateResult 8 mc313 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc314False : stateResult 8 mc314 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc315False : stateResult 8 mc315 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc316False : stateResult 8 mc316 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc317False : stateResult 8 mc317 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc318False : stateResult 8 mc318 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc319False : stateResult 8 mc319 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc320False : stateResult 8 mc320 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc321False : stateResult 8 mc321 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc322False : stateResult 8 mc322 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc323False : stateResult 8 mc323 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc324False : stateResult 8 mc324 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc325False : stateResult 8 mc325 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc326False : stateResult 8 mc326 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc327False : stateResult 8 mc327 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc328False : stateResult 8 mc328 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc329False : stateResult 8 mc329 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc330False : stateResult 8 mc330 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc331False : stateResult 8 mc331 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc332False : stateResult 8 mc332 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc333False : stateResult 8 mc333 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc334False : stateResult 8 mc334 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc335False : stateResult 8 mc335 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc336False : stateResult 8 mc336 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc337False : stateResult 8 mc337 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc338False : stateResult 8 mc338 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc339False : stateResult 8 mc339 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc340False : stateResult 8 mc340 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc341False : stateResult 8 mc341 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc342False : stateResult 8 mc342 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc343False : stateResult 8 mc343 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc344False : stateResult 8 mc344 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc345False : stateResult 8 mc345 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc346False : stateResult 8 mc346 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc347False : stateResult 8 mc347 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc348False : stateResult 8 mc348 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc349False : stateResult 8 mc349 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc350False : stateResult 8 mc350 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc351False : stateResult 8 mc351 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc352False : stateResult 8 mc352 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc353False : stateResult 8 mc353 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc354False : stateResult 8 mc354 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc308Children : List SearchState := [mc309,mc310,mc311,mc312,mc313,mc314,mc315,mc316,mc317,mc318,mc319,mc320,mc321,mc322,mc323,mc324,mc325,mc326,mc327,mc328,mc329,mc330,mc331,mc332,mc333,mc334,mc335,mc336,mc337,mc338,mc339,mc340,mc341,mc342,mc343,mc344,mc345,mc346,mc347,mc348,mc349,mc350,mc351,mc352,mc353,mc354]
theorem mc308False : stateResult 9 mc308 = false := by
  apply coverResult (k := 6) (states := mc308Children)
  · change mc308Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc308Children, List.all_cons, List.all_nil, mc309False, mc310False, mc311False, mc312False, mc313False, mc314False, mc315False, mc316False, mc317False, mc318False, mc319False, mc320False, mc321False, mc322False, mc323False, mc324False, mc325False, mc326False, mc327False, mc328False, mc329False, mc330False, mc331False, mc332False, mc333False, mc334False, mc335False, mc336False, mc337False, mc338False, mc339False, mc340False, mc341False, mc342False, mc343False, mc344False, mc345False, mc346False, mc347False, mc348False, mc349False, mc350False, mc351False, mc352False, mc353False, mc354False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc356False : stateResult 8 mc356 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc357False : stateResult 8 mc357 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc358False : stateResult 8 mc358 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc359False : stateResult 8 mc359 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc360False : stateResult 8 mc360 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc361False : stateResult 8 mc361 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc362False : stateResult 8 mc362 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc363False : stateResult 8 mc363 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc364False : stateResult 8 mc364 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc365False : stateResult 8 mc365 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc366False : stateResult 8 mc366 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc367False : stateResult 8 mc367 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc368False : stateResult 8 mc368 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc369False : stateResult 8 mc369 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc370False : stateResult 8 mc370 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc371False : stateResult 8 mc371 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc372False : stateResult 8 mc372 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc373False : stateResult 8 mc373 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc374False : stateResult 8 mc374 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc375False : stateResult 8 mc375 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc376False : stateResult 8 mc376 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc377False : stateResult 8 mc377 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc378False : stateResult 8 mc378 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc379False : stateResult 8 mc379 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc380False : stateResult 8 mc380 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc381False : stateResult 8 mc381 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc382False : stateResult 8 mc382 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc383False : stateResult 8 mc383 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc384False : stateResult 8 mc384 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc385False : stateResult 8 mc385 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc386False : stateResult 8 mc386 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc387False : stateResult 8 mc387 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc388False : stateResult 8 mc388 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc389False : stateResult 8 mc389 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc390False : stateResult 8 mc390 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc391False : stateResult 8 mc391 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc392False : stateResult 8 mc392 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc393False : stateResult 8 mc393 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc394False : stateResult 8 mc394 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc395False : stateResult 8 mc395 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc396False : stateResult 8 mc396 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc397False : stateResult 8 mc397 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc398False : stateResult 8 mc398 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc399False : stateResult 8 mc399 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc400False : stateResult 8 mc400 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc355Children : List SearchState := [mc356,mc357,mc358,mc359,mc360,mc361,mc362,mc363,mc364,mc365,mc366,mc367,mc368,mc369,mc370,mc371,mc372,mc373,mc374,mc375,mc376,mc377,mc378,mc379,mc380,mc381,mc382,mc383,mc384,mc385,mc386,mc387,mc388,mc389,mc390,mc391,mc392,mc393,mc394,mc395,mc396,mc397,mc398,mc399,mc400]
theorem mc355False : stateResult 9 mc355 = false := by
  apply coverResult (k := 6) (states := mc355Children)
  · change mc355Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc355Children, List.all_cons, List.all_nil, mc356False, mc357False, mc358False, mc359False, mc360False, mc361False, mc362False, mc363False, mc364False, mc365False, mc366False, mc367False, mc368False, mc369False, mc370False, mc371False, mc372False, mc373False, mc374False, mc375False, mc376False, mc377False, mc378False, mc379False, mc380False, mc381False, mc382False, mc383False, mc384False, mc385False, mc386False, mc387False, mc388False, mc389False, mc390False, mc391False, mc392False, mc393False, mc394False, mc395False, mc396False, mc397False, mc398False, mc399False, mc400False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc402False : stateResult 8 mc402 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc403False : stateResult 8 mc403 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc404False : stateResult 8 mc404 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc405False : stateResult 8 mc405 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc406False : stateResult 8 mc406 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc407False : stateResult 8 mc407 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc408False : stateResult 8 mc408 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc409False : stateResult 8 mc409 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc410False : stateResult 8 mc410 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc411False : stateResult 8 mc411 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc412False : stateResult 8 mc412 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc413False : stateResult 8 mc413 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc414False : stateResult 8 mc414 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc415False : stateResult 8 mc415 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc416False : stateResult 8 mc416 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc417False : stateResult 8 mc417 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc418False : stateResult 8 mc418 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc419False : stateResult 8 mc419 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc420False : stateResult 8 mc420 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc421False : stateResult 8 mc421 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc422False : stateResult 8 mc422 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc423False : stateResult 8 mc423 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc424False : stateResult 8 mc424 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc425False : stateResult 8 mc425 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc426False : stateResult 8 mc426 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc427False : stateResult 8 mc427 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc428False : stateResult 8 mc428 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc429False : stateResult 8 mc429 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc430False : stateResult 8 mc430 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc431False : stateResult 8 mc431 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc432False : stateResult 8 mc432 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc433False : stateResult 8 mc433 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc434False : stateResult 8 mc434 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc435False : stateResult 8 mc435 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc436False : stateResult 8 mc436 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc437False : stateResult 8 mc437 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc438False : stateResult 8 mc438 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc439False : stateResult 8 mc439 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc440False : stateResult 8 mc440 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc441False : stateResult 8 mc441 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc442False : stateResult 8 mc442 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc443False : stateResult 8 mc443 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc444False : stateResult 8 mc444 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc445False : stateResult 8 mc445 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc446False : stateResult 8 mc446 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc401Children : List SearchState := [mc402,mc403,mc404,mc405,mc406,mc407,mc408,mc409,mc410,mc411,mc412,mc413,mc414,mc415,mc416,mc417,mc418,mc419,mc420,mc421,mc422,mc423,mc424,mc425,mc426,mc427,mc428,mc429,mc430,mc431,mc432,mc433,mc434,mc435,mc436,mc437,mc438,mc439,mc440,mc441,mc442,mc443,mc444,mc445,mc446]
theorem mc401False : stateResult 9 mc401 = false := by
  apply coverResult (k := 6) (states := mc401Children)
  · change mc401Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc401Children, List.all_cons, List.all_nil, mc402False, mc403False, mc404False, mc405False, mc406False, mc407False, mc408False, mc409False, mc410False, mc411False, mc412False, mc413False, mc414False, mc415False, mc416False, mc417False, mc418False, mc419False, mc420False, mc421False, mc422False, mc423False, mc424False, mc425False, mc426False, mc427False, mc428False, mc429False, mc430False, mc431False, mc432False, mc433False, mc434False, mc435False, mc436False, mc437False, mc438False, mc439False, mc440False, mc441False, mc442False, mc443False, mc444False, mc445False, mc446False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc448False : stateResult 8 mc448 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc449False : stateResult 8 mc449 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc450False : stateResult 8 mc450 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc451False : stateResult 8 mc451 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc452False : stateResult 8 mc452 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc453False : stateResult 8 mc453 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc454False : stateResult 8 mc454 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc455False : stateResult 8 mc455 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc456False : stateResult 8 mc456 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc457False : stateResult 8 mc457 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc458False : stateResult 8 mc458 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc459False : stateResult 8 mc459 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc460False : stateResult 8 mc460 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc461False : stateResult 8 mc461 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc462False : stateResult 8 mc462 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc463False : stateResult 8 mc463 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc464False : stateResult 8 mc464 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc465False : stateResult 8 mc465 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc466False : stateResult 8 mc466 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc467False : stateResult 8 mc467 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc468False : stateResult 8 mc468 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc469False : stateResult 8 mc469 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc470False : stateResult 8 mc470 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc471False : stateResult 8 mc471 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc472False : stateResult 8 mc472 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc473False : stateResult 8 mc473 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc474False : stateResult 8 mc474 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc475False : stateResult 8 mc475 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc476False : stateResult 8 mc476 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc477False : stateResult 8 mc477 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc478False : stateResult 8 mc478 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc479False : stateResult 8 mc479 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc480False : stateResult 8 mc480 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc481False : stateResult 8 mc481 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc482False : stateResult 8 mc482 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc483False : stateResult 8 mc483 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc484False : stateResult 8 mc484 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc447Children : List SearchState := [mc448,mc449,mc450,mc451,mc452,mc453,mc454,mc455,mc456,mc457,mc458,mc459,mc460,mc461,mc462,mc463,mc464,mc465,mc466,mc467,mc468,mc469,mc470,mc471,mc472,mc473,mc474,mc475,mc476,mc477,mc478,mc479,mc480,mc481,mc482,mc483,mc484]
theorem mc447False : stateResult 9 mc447 = false := by
  apply coverResult (k := 6) (states := mc447Children)
  · change mc447Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc447Children, List.all_cons, List.all_nil, mc448False, mc449False, mc450False, mc451False, mc452False, mc453False, mc454False, mc455False, mc456False, mc457False, mc458False, mc459False, mc460False, mc461False, mc462False, mc463False, mc464False, mc465False, mc466False, mc467False, mc468False, mc469False, mc470False, mc471False, mc472False, mc473False, mc474False, mc475False, mc476False, mc477False, mc478False, mc479False, mc480False, mc481False, mc482False, mc483False, mc484False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc486False : stateResult 8 mc486 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc487False : stateResult 8 mc487 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc488False : stateResult 8 mc488 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc489False : stateResult 8 mc489 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc490False : stateResult 8 mc490 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc491False : stateResult 8 mc491 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc492False : stateResult 8 mc492 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc493False : stateResult 8 mc493 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc494False : stateResult 8 mc494 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc495False : stateResult 8 mc495 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc496False : stateResult 8 mc496 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc497False : stateResult 8 mc497 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc498False : stateResult 8 mc498 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc499False : stateResult 8 mc499 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc500False : stateResult 8 mc500 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc501False : stateResult 8 mc501 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc502False : stateResult 8 mc502 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc503False : stateResult 8 mc503 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc504False : stateResult 8 mc504 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc505False : stateResult 8 mc505 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc506False : stateResult 8 mc506 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc507False : stateResult 8 mc507 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc508False : stateResult 8 mc508 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc509False : stateResult 8 mc509 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc510False : stateResult 8 mc510 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc511False : stateResult 8 mc511 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc512False : stateResult 8 mc512 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc513False : stateResult 8 mc513 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc514False : stateResult 8 mc514 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc515False : stateResult 8 mc515 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc516False : stateResult 8 mc516 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc517False : stateResult 8 mc517 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc518False : stateResult 8 mc518 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc519False : stateResult 8 mc519 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc520False : stateResult 8 mc520 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc521False : stateResult 8 mc521 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc522False : stateResult 8 mc522 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc523False : stateResult 8 mc523 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc524False : stateResult 8 mc524 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc525False : stateResult 8 mc525 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc526False : stateResult 8 mc526 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc527False : stateResult 8 mc527 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc528False : stateResult 8 mc528 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc485Children : List SearchState := [mc486,mc487,mc488,mc489,mc490,mc491,mc492,mc493,mc494,mc495,mc496,mc497,mc498,mc499,mc500,mc501,mc502,mc503,mc504,mc505,mc506,mc507,mc508,mc509,mc510,mc511,mc512,mc513,mc514,mc515,mc516,mc517,mc518,mc519,mc520,mc521,mc522,mc523,mc524,mc525,mc526,mc527,mc528]
theorem mc485False : stateResult 9 mc485 = false := by
  apply coverResult (k := 6) (states := mc485Children)
  · change mc485Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc485Children, List.all_cons, List.all_nil, mc486False, mc487False, mc488False, mc489False, mc490False, mc491False, mc492False, mc493False, mc494False, mc495False, mc496False, mc497False, mc498False, mc499False, mc500False, mc501False, mc502False, mc503False, mc504False, mc505False, mc506False, mc507False, mc508False, mc509False, mc510False, mc511False, mc512False, mc513False, mc514False, mc515False, mc516False, mc517False, mc518False, mc519False, mc520False, mc521False, mc522False, mc523False, mc524False, mc525False, mc526False, mc527False, mc528False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc530False : stateResult 8 mc530 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc531False : stateResult 8 mc531 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc532False : stateResult 8 mc532 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc533False : stateResult 8 mc533 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc534False : stateResult 8 mc534 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc535False : stateResult 8 mc535 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc536False : stateResult 8 mc536 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc537False : stateResult 8 mc537 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc538False : stateResult 8 mc538 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc539False : stateResult 8 mc539 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc540False : stateResult 8 mc540 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc541False : stateResult 8 mc541 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc542False : stateResult 8 mc542 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc543False : stateResult 8 mc543 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc544False : stateResult 8 mc544 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc545False : stateResult 8 mc545 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc546False : stateResult 8 mc546 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc547False : stateResult 8 mc547 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc548False : stateResult 8 mc548 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc549False : stateResult 8 mc549 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc550False : stateResult 8 mc550 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc551False : stateResult 8 mc551 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc552False : stateResult 8 mc552 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc553False : stateResult 8 mc553 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc554False : stateResult 8 mc554 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc555False : stateResult 8 mc555 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc556False : stateResult 8 mc556 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc557False : stateResult 8 mc557 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc558False : stateResult 8 mc558 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc559False : stateResult 8 mc559 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc560False : stateResult 8 mc560 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc561False : stateResult 8 mc561 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc562False : stateResult 8 mc562 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc563False : stateResult 8 mc563 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc564False : stateResult 8 mc564 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc565False : stateResult 8 mc565 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc566False : stateResult 8 mc566 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc567False : stateResult 8 mc567 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc568False : stateResult 8 mc568 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc569False : stateResult 8 mc569 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc570False : stateResult 8 mc570 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc571False : stateResult 8 mc571 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc572False : stateResult 8 mc572 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc573False : stateResult 8 mc573 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc574False : stateResult 8 mc574 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc529Children : List SearchState := [mc530,mc531,mc532,mc533,mc534,mc535,mc536,mc537,mc538,mc539,mc540,mc541,mc542,mc543,mc544,mc545,mc546,mc547,mc548,mc549,mc550,mc551,mc552,mc553,mc554,mc555,mc556,mc557,mc558,mc559,mc560,mc561,mc562,mc563,mc564,mc565,mc566,mc567,mc568,mc569,mc570,mc571,mc572,mc573,mc574]
theorem mc529False : stateResult 9 mc529 = false := by
  apply coverResult (k := 6) (states := mc529Children)
  · change mc529Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc529Children, List.all_cons, List.all_nil, mc530False, mc531False, mc532False, mc533False, mc534False, mc535False, mc536False, mc537False, mc538False, mc539False, mc540False, mc541False, mc542False, mc543False, mc544False, mc545False, mc546False, mc547False, mc548False, mc549False, mc550False, mc551False, mc552False, mc553False, mc554False, mc555False, mc556False, mc557False, mc558False, mc559False, mc560False, mc561False, mc562False, mc563False, mc564False, mc565False, mc566False, mc567False, mc568False, mc569False, mc570False, mc571False, mc572False, mc573False, mc574False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc576False : stateResult 8 mc576 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc577False : stateResult 8 mc577 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc578False : stateResult 8 mc578 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc580False : stateResult 7 mc580 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc581False : stateResult 7 mc581 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc582False : stateResult 7 mc582 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc583False : stateResult 7 mc583 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc584False : stateResult 7 mc584 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc585False : stateResult 7 mc585 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc586False : stateResult 7 mc586 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc587False : stateResult 7 mc587 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc588False : stateResult 7 mc588 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc589False : stateResult 7 mc589 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc590False : stateResult 7 mc590 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc591False : stateResult 7 mc591 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc592False : stateResult 7 mc592 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc593False : stateResult 7 mc593 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc594False : stateResult 7 mc594 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc595False : stateResult 7 mc595 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc596False : stateResult 7 mc596 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc597False : stateResult 7 mc597 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc598False : stateResult 7 mc598 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc599False : stateResult 7 mc599 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc600False : stateResult 7 mc600 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc601False : stateResult 7 mc601 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc602False : stateResult 7 mc602 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc603False : stateResult 7 mc603 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc604False : stateResult 7 mc604 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc605False : stateResult 7 mc605 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc606False : stateResult 7 mc606 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc607False : stateResult 7 mc607 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc608False : stateResult 7 mc608 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc579Children : List SearchState := [mc580,mc581,mc582,mc583,mc584,mc585,mc586,mc587,mc588,mc589,mc590,mc591,mc592,mc593,mc594,mc595,mc596,mc597,mc598,mc599,mc600,mc601,mc602,mc603,mc604,mc605,mc606,mc607,mc608]
theorem mc579False : stateResult 8 mc579 = false := by
  apply coverResult (k := 5) (states := mc579Children)
  · change mc579Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc579Children, List.all_cons, List.all_nil, mc580False, mc581False, mc582False, mc583False, mc584False, mc585False, mc586False, mc587False, mc588False, mc589False, mc590False, mc591False, mc592False, mc593False, mc594False, mc595False, mc596False, mc597False, mc598False, mc599False, mc600False, mc601False, mc602False, mc603False, mc604False, mc605False, mc606False, mc607False, mc608False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc609False : stateResult 8 mc609 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc610False : stateResult 8 mc610 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc611False : stateResult 8 mc611 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc612False : stateResult 8 mc612 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc613False : stateResult 8 mc613 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc614False : stateResult 8 mc614 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc615False : stateResult 8 mc615 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc616False : stateResult 8 mc616 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc617False : stateResult 8 mc617 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc618False : stateResult 8 mc618 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc619False : stateResult 8 mc619 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc620False : stateResult 8 mc620 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc621False : stateResult 8 mc621 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc622False : stateResult 8 mc622 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc624False : stateResult 7 mc624 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc625False : stateResult 7 mc625 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc626False : stateResult 7 mc626 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc627False : stateResult 7 mc627 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc628False : stateResult 7 mc628 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc629False : stateResult 7 mc629 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc630False : stateResult 7 mc630 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc631False : stateResult 7 mc631 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc632False : stateResult 7 mc632 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc633False : stateResult 7 mc633 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc634False : stateResult 7 mc634 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc635False : stateResult 7 mc635 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc636False : stateResult 7 mc636 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc637False : stateResult 7 mc637 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc638False : stateResult 7 mc638 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc639False : stateResult 7 mc639 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc640False : stateResult 7 mc640 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc641False : stateResult 7 mc641 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc642False : stateResult 7 mc642 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc643False : stateResult 7 mc643 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc644False : stateResult 7 mc644 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc645False : stateResult 7 mc645 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc646False : stateResult 7 mc646 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc647False : stateResult 7 mc647 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc648False : stateResult 7 mc648 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc649False : stateResult 7 mc649 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc650False : stateResult 7 mc650 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc651False : stateResult 7 mc651 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc652False : stateResult 7 mc652 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc653False : stateResult 7 mc653 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc623Children : List SearchState := [mc624,mc625,mc626,mc627,mc628,mc629,mc630,mc631,mc632,mc633,mc634,mc635,mc636,mc637,mc638,mc639,mc640,mc641,mc642,mc643,mc644,mc645,mc646,mc647,mc648,mc649,mc650,mc651,mc652,mc653]
theorem mc623False : stateResult 8 mc623 = false := by
  apply coverResult (k := 5) (states := mc623Children)
  · change mc623Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc623Children, List.all_cons, List.all_nil, mc624False, mc625False, mc626False, mc627False, mc628False, mc629False, mc630False, mc631False, mc632False, mc633False, mc634False, mc635False, mc636False, mc637False, mc638False, mc639False, mc640False, mc641False, mc642False, mc643False, mc644False, mc645False, mc646False, mc647False, mc648False, mc649False, mc650False, mc651False, mc652False, mc653False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc654False : stateResult 8 mc654 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc655False : stateResult 8 mc655 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc656False : stateResult 8 mc656 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc657False : stateResult 8 mc657 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc658False : stateResult 8 mc658 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc660False : stateResult 7 mc660 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc661False : stateResult 7 mc661 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc662False : stateResult 7 mc662 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc663False : stateResult 7 mc663 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc664False : stateResult 7 mc664 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc665False : stateResult 7 mc665 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc666False : stateResult 7 mc666 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc667False : stateResult 7 mc667 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc668False : stateResult 7 mc668 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc669False : stateResult 7 mc669 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc670False : stateResult 7 mc670 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc671False : stateResult 7 mc671 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc672False : stateResult 7 mc672 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc673False : stateResult 7 mc673 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc674False : stateResult 7 mc674 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc675False : stateResult 7 mc675 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc676False : stateResult 7 mc676 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc677False : stateResult 7 mc677 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc678False : stateResult 7 mc678 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc679False : stateResult 7 mc679 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc680False : stateResult 7 mc680 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc681False : stateResult 7 mc681 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc682False : stateResult 7 mc682 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc683False : stateResult 7 mc683 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc684False : stateResult 7 mc684 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc685False : stateResult 7 mc685 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc686False : stateResult 7 mc686 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc687False : stateResult 7 mc687 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc688False : stateResult 7 mc688 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc689False : stateResult 7 mc689 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc690False : stateResult 7 mc690 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc659Children : List SearchState := [mc627,mc660,mc661,mc662,mc663,mc664,mc665,mc666,mc667,mc668,mc669,mc670,mc671,mc672,mc673,mc674,mc675,mc676,mc677,mc678,mc679,mc680,mc681,mc682,mc683,mc684,mc685,mc686,mc687,mc688,mc689,mc690]
theorem mc659False : stateResult 8 mc659 = false := by
  apply coverResult (k := 5) (states := mc659Children)
  · change mc659Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc659Children, List.all_cons, List.all_nil, mc627False, mc660False, mc661False, mc662False, mc663False, mc664False, mc665False, mc666False, mc667False, mc668False, mc669False, mc670False, mc671False, mc672False, mc673False, mc674False, mc675False, mc676False, mc677False, mc678False, mc679False, mc680False, mc681False, mc682False, mc683False, mc684False, mc685False, mc686False, mc687False, mc688False, mc689False, mc690False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc691False : stateResult 8 mc691 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc692False : stateResult 8 mc692 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc693False : stateResult 8 mc693 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc694False : stateResult 8 mc694 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc695False : stateResult 8 mc695 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc697False : stateResult 7 mc697 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc698False : stateResult 7 mc698 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc699False : stateResult 7 mc699 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc700False : stateResult 7 mc700 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc701False : stateResult 7 mc701 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc702False : stateResult 7 mc702 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc703False : stateResult 7 mc703 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc704False : stateResult 7 mc704 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc705False : stateResult 7 mc705 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc706False : stateResult 7 mc706 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc707False : stateResult 7 mc707 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc708False : stateResult 7 mc708 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc709False : stateResult 7 mc709 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc710False : stateResult 7 mc710 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc711False : stateResult 7 mc711 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc712False : stateResult 7 mc712 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc713False : stateResult 7 mc713 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc714False : stateResult 7 mc714 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc715False : stateResult 7 mc715 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc716False : stateResult 7 mc716 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc717False : stateResult 7 mc717 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc718False : stateResult 7 mc718 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc719False : stateResult 7 mc719 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc720False : stateResult 7 mc720 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc721False : stateResult 7 mc721 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc722False : stateResult 7 mc722 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc723False : stateResult 7 mc723 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc724False : stateResult 7 mc724 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc725False : stateResult 7 mc725 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc726False : stateResult 7 mc726 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc727False : stateResult 7 mc727 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc728False : stateResult 7 mc728 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc696Children : List SearchState := [mc627,mc697,mc698,mc699,mc700,mc701,mc702,mc703,mc704,mc705,mc706,mc707,mc708,mc709,mc710,mc711,mc712,mc713,mc714,mc715,mc716,mc717,mc718,mc719,mc720,mc721,mc722,mc723,mc724,mc725,mc726,mc727,mc728]
theorem mc696False : stateResult 8 mc696 = false := by
  apply coverResult (k := 5) (states := mc696Children)
  · change mc696Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc696Children, List.all_cons, List.all_nil, mc627False, mc697False, mc698False, mc699False, mc700False, mc701False, mc702False, mc703False, mc704False, mc705False, mc706False, mc707False, mc708False, mc709False, mc710False, mc711False, mc712False, mc713False, mc714False, mc715False, mc716False, mc717False, mc718False, mc719False, mc720False, mc721False, mc722False, mc723False, mc724False, mc725False, mc726False, mc727False, mc728False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc729False : stateResult 8 mc729 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc730False : stateResult 8 mc730 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc731False : stateResult 8 mc731 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc732False : stateResult 8 mc732 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc733False : stateResult 8 mc733 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc734False : stateResult 8 mc734 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc735False : stateResult 8 mc735 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc736False : stateResult 8 mc736 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc737False : stateResult 8 mc737 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc738False : stateResult 8 mc738 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc739False : stateResult 8 mc739 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc740False : stateResult 8 mc740 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc741False : stateResult 8 mc741 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc742False : stateResult 8 mc742 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc743False : stateResult 8 mc743 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc744False : stateResult 8 mc744 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc575Children : List SearchState := [mc576,mc577,mc578,mc579,mc609,mc610,mc611,mc612,mc613,mc614,mc615,mc616,mc617,mc618,mc619,mc620,mc621,mc622,mc623,mc654,mc655,mc656,mc657,mc658,mc659,mc691,mc692,mc693,mc694,mc695,mc696,mc729,mc730,mc731,mc732,mc733,mc734,mc735,mc736,mc737,mc738,mc739,mc740,mc741,mc742,mc743,mc744]
theorem mc575False : stateResult 9 mc575 = false := by
  apply coverResult (k := 6) (states := mc575Children)
  · change mc575Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc575Children, List.all_cons, List.all_nil, mc576False, mc577False, mc578False, mc579False, mc609False, mc610False, mc611False, mc612False, mc613False, mc614False, mc615False, mc616False, mc617False, mc618False, mc619False, mc620False, mc621False, mc622False, mc623False, mc654False, mc655False, mc656False, mc657False, mc658False, mc659False, mc691False, mc692False, mc693False, mc694False, mc695False, mc696False, mc729False, mc730False, mc731False, mc732False, mc733False, mc734False, mc735False, mc736False, mc737False, mc738False, mc739False, mc740False, mc741False, mc742False, mc743False, mc744False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc746False : stateResult 8 mc746 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc747False : stateResult 8 mc747 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc748False : stateResult 8 mc748 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc749False : stateResult 8 mc749 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc750False : stateResult 8 mc750 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc752False : stateResult 7 mc752 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc753False : stateResult 7 mc753 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc754False : stateResult 7 mc754 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc755False : stateResult 7 mc755 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc756False : stateResult 7 mc756 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc757False : stateResult 7 mc757 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc758False : stateResult 7 mc758 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc759False : stateResult 7 mc759 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc760False : stateResult 7 mc760 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc761False : stateResult 7 mc761 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc762False : stateResult 7 mc762 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc763False : stateResult 7 mc763 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc764False : stateResult 7 mc764 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc765False : stateResult 7 mc765 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc766False : stateResult 7 mc766 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc767False : stateResult 7 mc767 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc768False : stateResult 7 mc768 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc769False : stateResult 7 mc769 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc770False : stateResult 7 mc770 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc771False : stateResult 7 mc771 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc772False : stateResult 7 mc772 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc773False : stateResult 7 mc773 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc774False : stateResult 7 mc774 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc775False : stateResult 7 mc775 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc776False : stateResult 7 mc776 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc777False : stateResult 7 mc777 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc778False : stateResult 7 mc778 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc779False : stateResult 7 mc779 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc780False : stateResult 7 mc780 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc781False : stateResult 7 mc781 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc782False : stateResult 7 mc782 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc783False : stateResult 7 mc783 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc751Children : List SearchState := [mc752,mc753,mc754,mc755,mc756,mc757,mc758,mc759,mc760,mc761,mc762,mc763,mc764,mc765,mc766,mc767,mc768,mc769,mc770,mc771,mc772,mc773,mc774,mc775,mc776,mc777,mc778,mc779,mc780,mc781,mc782,mc783]
theorem mc751False : stateResult 8 mc751 = false := by
  apply coverResult (k := 5) (states := mc751Children)
  · change mc751Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc751Children, List.all_cons, List.all_nil, mc752False, mc753False, mc754False, mc755False, mc756False, mc757False, mc758False, mc759False, mc760False, mc761False, mc762False, mc763False, mc764False, mc765False, mc766False, mc767False, mc768False, mc769False, mc770False, mc771False, mc772False, mc773False, mc774False, mc775False, mc776False, mc777False, mc778False, mc779False, mc780False, mc781False, mc782False, mc783False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc784False : stateResult 8 mc784 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc785False : stateResult 8 mc785 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc786False : stateResult 8 mc786 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc787False : stateResult 8 mc787 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc788False : stateResult 8 mc788 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc790False : stateResult 7 mc790 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc791False : stateResult 7 mc791 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc792False : stateResult 7 mc792 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc793False : stateResult 7 mc793 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc794False : stateResult 7 mc794 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc795False : stateResult 7 mc795 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc796False : stateResult 7 mc796 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc797False : stateResult 7 mc797 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc798False : stateResult 7 mc798 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc799False : stateResult 7 mc799 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc800False : stateResult 7 mc800 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc801False : stateResult 7 mc801 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc802False : stateResult 7 mc802 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc803False : stateResult 7 mc803 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc804False : stateResult 7 mc804 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc805False : stateResult 7 mc805 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc806False : stateResult 7 mc806 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc789Children : List SearchState := [mc665,mc666,mc667,mc790,mc791,mc792,mc668,mc669,mc670,mc671,mc672,mc673,mc674,mc675,mc676,mc627,mc660,mc661,mc662,mc663,mc664,mc793,mc794,mc795,mc796,mc797,mc798,mc799,mc800,mc801,mc802,mc803,mc804,mc805,mc806]
theorem mc789False : stateResult 8 mc789 = false := by
  apply coverResult (k := 5) (states := mc789Children)
  · change mc789Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc789Children, List.all_cons, List.all_nil, mc665False, mc666False, mc667False, mc790False, mc791False, mc792False, mc668False, mc669False, mc670False, mc671False, mc672False, mc673False, mc674False, mc675False, mc676False, mc627False, mc660False, mc661False, mc662False, mc663False, mc664False, mc793False, mc794False, mc795False, mc796False, mc797False, mc798False, mc799False, mc800False, mc801False, mc802False, mc803False, mc804False, mc805False, mc806False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc807False : stateResult 8 mc807 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc808False : stateResult 8 mc808 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc809False : stateResult 8 mc809 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc810False : stateResult 8 mc810 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc812False : stateResult 7 mc812 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc813False : stateResult 7 mc813 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc814False : stateResult 7 mc814 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc815False : stateResult 7 mc815 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc816False : stateResult 7 mc816 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc817False : stateResult 7 mc817 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc818False : stateResult 7 mc818 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc819False : stateResult 7 mc819 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc820False : stateResult 7 mc820 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc821False : stateResult 7 mc821 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc822False : stateResult 7 mc822 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc823False : stateResult 7 mc823 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc824False : stateResult 7 mc824 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc825False : stateResult 7 mc825 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc826False : stateResult 7 mc826 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc827False : stateResult 7 mc827 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc828False : stateResult 7 mc828 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc829False : stateResult 7 mc829 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc830False : stateResult 7 mc830 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc831False : stateResult 7 mc831 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc832False : stateResult 7 mc832 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc833False : stateResult 7 mc833 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc834False : stateResult 7 mc834 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc835False : stateResult 7 mc835 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc836False : stateResult 7 mc836 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc837False : stateResult 7 mc837 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc838False : stateResult 7 mc838 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc839False : stateResult 7 mc839 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc840False : stateResult 7 mc840 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc841False : stateResult 7 mc841 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc811Children : List SearchState := [mc812,mc813,mc814,mc815,mc816,mc817,mc818,mc819,mc820,mc821,mc822,mc823,mc824,mc825,mc826,mc827,mc828,mc829,mc830,mc831,mc832,mc833,mc834,mc835,mc836,mc837,mc838,mc839,mc840,mc841]
theorem mc811False : stateResult 8 mc811 = false := by
  apply coverResult (k := 5) (states := mc811Children)
  · change mc811Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc811Children, List.all_cons, List.all_nil, mc812False, mc813False, mc814False, mc815False, mc816False, mc817False, mc818False, mc819False, mc820False, mc821False, mc822False, mc823False, mc824False, mc825False, mc826False, mc827False, mc828False, mc829False, mc830False, mc831False, mc832False, mc833False, mc834False, mc835False, mc836False, mc837False, mc838False, mc839False, mc840False, mc841False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc842False : stateResult 8 mc842 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc843False : stateResult 8 mc843 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc844False : stateResult 8 mc844 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc845False : stateResult 8 mc845 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc846False : stateResult 8 mc846 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc847False : stateResult 8 mc847 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc848False : stateResult 8 mc848 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc849False : stateResult 8 mc849 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc850False : stateResult 8 mc850 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc851False : stateResult 8 mc851 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc852False : stateResult 8 mc852 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc854False : stateResult 7 mc854 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc855False : stateResult 7 mc855 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc856False : stateResult 7 mc856 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc857False : stateResult 7 mc857 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc858False : stateResult 7 mc858 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc859False : stateResult 7 mc859 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc860False : stateResult 7 mc860 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc861False : stateResult 7 mc861 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc862False : stateResult 7 mc862 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc863False : stateResult 7 mc863 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc864False : stateResult 7 mc864 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc865False : stateResult 7 mc865 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc866False : stateResult 7 mc866 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc867False : stateResult 7 mc867 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc868False : stateResult 7 mc868 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc869False : stateResult 7 mc869 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc870False : stateResult 7 mc870 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc871False : stateResult 7 mc871 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc872False : stateResult 7 mc872 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc873False : stateResult 7 mc873 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc874False : stateResult 7 mc874 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc875False : stateResult 7 mc875 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc876False : stateResult 7 mc876 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc877False : stateResult 7 mc877 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc853Children : List SearchState := [mc854,mc855,mc856,mc857,mc858,mc859,mc860,mc861,mc862,mc863,mc864,mc865,mc866,mc867,mc868,mc869,mc870,mc871,mc872,mc873,mc874,mc875,mc876,mc877]
theorem mc853False : stateResult 8 mc853 = false := by
  apply coverResult (k := 5) (states := mc853Children)
  · change mc853Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc853Children, List.all_cons, List.all_nil, mc854False, mc855False, mc856False, mc857False, mc858False, mc859False, mc860False, mc861False, mc862False, mc863False, mc864False, mc865False, mc866False, mc867False, mc868False, mc869False, mc870False, mc871False, mc872False, mc873False, mc874False, mc875False, mc876False, mc877False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc878False : stateResult 8 mc878 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc879False : stateResult 8 mc879 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc880False : stateResult 8 mc880 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc881False : stateResult 8 mc881 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc882False : stateResult 8 mc882 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc883False : stateResult 8 mc883 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc884False : stateResult 8 mc884 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc886False : stateResult 7 mc886 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc887False : stateResult 7 mc887 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc888False : stateResult 7 mc888 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc889False : stateResult 7 mc889 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc890False : stateResult 7 mc890 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc891False : stateResult 7 mc891 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc892False : stateResult 7 mc892 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc893False : stateResult 7 mc893 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc894False : stateResult 7 mc894 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc895False : stateResult 7 mc895 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc896False : stateResult 7 mc896 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc897False : stateResult 7 mc897 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc898False : stateResult 7 mc898 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc899False : stateResult 7 mc899 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc900False : stateResult 7 mc900 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc901False : stateResult 7 mc901 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc902False : stateResult 7 mc902 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc903False : stateResult 7 mc903 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc904False : stateResult 7 mc904 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc905False : stateResult 7 mc905 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc906False : stateResult 7 mc906 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc907False : stateResult 7 mc907 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc908False : stateResult 7 mc908 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc909False : stateResult 7 mc909 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc910False : stateResult 7 mc910 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc911False : stateResult 7 mc911 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc912False : stateResult 7 mc912 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc913False : stateResult 7 mc913 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc914False : stateResult 7 mc914 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc915False : stateResult 7 mc915 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc916False : stateResult 7 mc916 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc885Children : List SearchState := [mc886,mc887,mc888,mc889,mc890,mc891,mc892,mc893,mc894,mc895,mc896,mc897,mc898,mc899,mc900,mc901,mc902,mc903,mc904,mc905,mc906,mc907,mc908,mc909,mc910,mc911,mc912,mc913,mc914,mc915,mc916]
theorem mc885False : stateResult 8 mc885 = false := by
  apply coverResult (k := 5) (states := mc885Children)
  · change mc885Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc885Children, List.all_cons, List.all_nil, mc886False, mc887False, mc888False, mc889False, mc890False, mc891False, mc892False, mc893False, mc894False, mc895False, mc896False, mc897False, mc898False, mc899False, mc900False, mc901False, mc902False, mc903False, mc904False, mc905False, mc906False, mc907False, mc908False, mc909False, mc910False, mc911False, mc912False, mc913False, mc914False, mc915False, mc916False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc917False : stateResult 8 mc917 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc918False : stateResult 8 mc918 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc919False : stateResult 8 mc919 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc920False : stateResult 8 mc920 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc921False : stateResult 8 mc921 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc745Children : List SearchState := [mc746,mc747,mc748,mc749,mc750,mc751,mc784,mc785,mc786,mc787,mc788,mc789,mc807,mc808,mc809,mc810,mc811,mc842,mc843,mc844,mc845,mc846,mc847,mc848,mc849,mc850,mc851,mc852,mc853,mc878,mc879,mc880,mc881,mc882,mc883,mc884,mc885,mc917,mc918,mc919,mc920,mc921]
theorem mc745False : stateResult 9 mc745 = false := by
  apply coverResult (k := 6) (states := mc745Children)
  · change mc745Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc745Children, List.all_cons, List.all_nil, mc746False, mc747False, mc748False, mc749False, mc750False, mc751False, mc784False, mc785False, mc786False, mc787False, mc788False, mc789False, mc807False, mc808False, mc809False, mc810False, mc811False, mc842False, mc843False, mc844False, mc845False, mc846False, mc847False, mc848False, mc849False, mc850False, mc851False, mc852False, mc853False, mc878False, mc879False, mc880False, mc881False, mc882False, mc883False, mc884False, mc885False, mc917False, mc918False, mc919False, mc920False, mc921False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc923False : stateResult 8 mc923 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc924False : stateResult 8 mc924 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc925False : stateResult 8 mc925 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc926False : stateResult 8 mc926 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc927False : stateResult 8 mc927 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc928False : stateResult 8 mc928 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc929False : stateResult 8 mc929 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc930False : stateResult 8 mc930 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc931False : stateResult 8 mc931 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc932False : stateResult 8 mc932 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc933False : stateResult 8 mc933 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc934False : stateResult 8 mc934 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc935False : stateResult 8 mc935 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc936False : stateResult 8 mc936 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc937False : stateResult 8 mc937 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc938False : stateResult 8 mc938 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc939False : stateResult 8 mc939 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc940False : stateResult 8 mc940 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc941False : stateResult 8 mc941 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc942False : stateResult 8 mc942 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc943False : stateResult 8 mc943 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc944False : stateResult 8 mc944 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc945False : stateResult 8 mc945 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc946False : stateResult 8 mc946 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc947False : stateResult 8 mc947 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc948False : stateResult 8 mc948 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc949False : stateResult 8 mc949 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc950False : stateResult 8 mc950 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc951False : stateResult 8 mc951 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc952False : stateResult 8 mc952 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc953False : stateResult 8 mc953 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc954False : stateResult 8 mc954 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc955False : stateResult 8 mc955 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc956False : stateResult 8 mc956 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc957False : stateResult 8 mc957 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc958False : stateResult 8 mc958 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc959False : stateResult 8 mc959 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc960False : stateResult 8 mc960 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc961False : stateResult 8 mc961 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc962False : stateResult 8 mc962 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc963False : stateResult 8 mc963 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc964False : stateResult 8 mc964 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc965False : stateResult 8 mc965 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc966False : stateResult 8 mc966 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc967False : stateResult 8 mc967 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc968False : stateResult 8 mc968 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc969False : stateResult 8 mc969 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc970False : stateResult 8 mc970 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc971False : stateResult 8 mc971 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc972False : stateResult 8 mc972 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc974False : stateResult 7 mc974 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc975False : stateResult 7 mc975 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc976False : stateResult 7 mc976 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc977False : stateResult 7 mc977 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc978False : stateResult 7 mc978 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc979False : stateResult 7 mc979 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc980False : stateResult 7 mc980 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc981False : stateResult 7 mc981 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc982False : stateResult 7 mc982 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc983False : stateResult 7 mc983 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc984False : stateResult 7 mc984 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc985False : stateResult 7 mc985 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc986False : stateResult 7 mc986 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc987False : stateResult 7 mc987 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc988False : stateResult 7 mc988 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc989False : stateResult 7 mc989 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc990False : stateResult 7 mc990 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc991False : stateResult 7 mc991 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc992False : stateResult 7 mc992 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc993False : stateResult 7 mc993 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc994False : stateResult 7 mc994 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc995False : stateResult 7 mc995 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc996False : stateResult 7 mc996 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc997False : stateResult 7 mc997 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc998False : stateResult 7 mc998 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc999False : stateResult 7 mc999 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1000False : stateResult 7 mc1000 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1001False : stateResult 7 mc1001 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1002False : stateResult 7 mc1002 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1003False : stateResult 7 mc1003 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1004False : stateResult 7 mc1004 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1005False : stateResult 7 mc1005 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1006False : stateResult 7 mc1006 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1007False : stateResult 7 mc1007 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc973Children : List SearchState := [mc974,mc975,mc976,mc977,mc978,mc979,mc980,mc981,mc982,mc983,mc984,mc985,mc986,mc987,mc988,mc989,mc990,mc991,mc992,mc993,mc994,mc995,mc996,mc997,mc998,mc999,mc1000,mc1001,mc1002,mc1003,mc1004,mc1005,mc1006,mc1007]
theorem mc973False : stateResult 8 mc973 = false := by
  apply coverResult (k := 5) (states := mc973Children)
  · change mc973Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc973Children, List.all_cons, List.all_nil, mc974False, mc975False, mc976False, mc977False, mc978False, mc979False, mc980False, mc981False, mc982False, mc983False, mc984False, mc985False, mc986False, mc987False, mc988False, mc989False, mc990False, mc991False, mc992False, mc993False, mc994False, mc995False, mc996False, mc997False, mc998False, mc999False, mc1000False, mc1001False, mc1002False, mc1003False, mc1004False, mc1005False, mc1006False, mc1007False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1008False : stateResult 8 mc1008 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1009False : stateResult 8 mc1009 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1010False : stateResult 8 mc1010 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1011False : stateResult 8 mc1011 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1012False : stateResult 8 mc1012 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1013False : stateResult 8 mc1013 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1014False : stateResult 8 mc1014 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc922Children : List SearchState := [mc923,mc924,mc925,mc926,mc927,mc459,mc928,mc929,mc930,mc931,mc932,mc933,mc934,mc935,mc936,mc937,mc938,mc939,mc940,mc941,mc942,mc943,mc944,mc945,mc946,mc947,mc948,mc949,mc950,mc951,mc952,mc953,mc954,mc955,mc956,mc957,mc958,mc959,mc960,mc961,mc962,mc963,mc964,mc965,mc966,mc967,mc968,mc969,mc970,mc971,mc972,mc973,mc1008,mc1009,mc1010,mc1011,mc1012,mc1013,mc1014]
theorem mc922False : stateResult 9 mc922 = false := by
  apply coverResult (k := 6) (states := mc922Children)
  · change mc922Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc922Children, List.all_cons, List.all_nil, mc923False, mc924False, mc925False, mc926False, mc927False, mc459False, mc928False, mc929False, mc930False, mc931False, mc932False, mc933False, mc934False, mc935False, mc936False, mc937False, mc938False, mc939False, mc940False, mc941False, mc942False, mc943False, mc944False, mc945False, mc946False, mc947False, mc948False, mc949False, mc950False, mc951False, mc952False, mc953False, mc954False, mc955False, mc956False, mc957False, mc958False, mc959False, mc960False, mc961False, mc962False, mc963False, mc964False, mc965False, mc966False, mc967False, mc968False, mc969False, mc970False, mc971False, mc972False, mc973False, mc1008False, mc1009False, mc1010False, mc1011False, mc1012False, mc1013False, mc1014False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1016False : stateResult 8 mc1016 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1017False : stateResult 8 mc1017 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1018False : stateResult 8 mc1018 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1019False : stateResult 8 mc1019 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1020False : stateResult 8 mc1020 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1021False : stateResult 8 mc1021 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1022False : stateResult 8 mc1022 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1023False : stateResult 8 mc1023 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1024False : stateResult 8 mc1024 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1025False : stateResult 8 mc1025 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1026False : stateResult 8 mc1026 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1027False : stateResult 8 mc1027 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1028False : stateResult 8 mc1028 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1029False : stateResult 8 mc1029 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1030False : stateResult 8 mc1030 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1031False : stateResult 8 mc1031 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1032False : stateResult 8 mc1032 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1033False : stateResult 8 mc1033 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1034False : stateResult 8 mc1034 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1035False : stateResult 8 mc1035 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1036False : stateResult 8 mc1036 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1037False : stateResult 8 mc1037 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1038False : stateResult 8 mc1038 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1039False : stateResult 8 mc1039 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1040False : stateResult 8 mc1040 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1041False : stateResult 8 mc1041 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1042False : stateResult 8 mc1042 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1043False : stateResult 8 mc1043 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1044False : stateResult 8 mc1044 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1045False : stateResult 8 mc1045 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1046False : stateResult 8 mc1046 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1047False : stateResult 8 mc1047 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1048False : stateResult 8 mc1048 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1049False : stateResult 8 mc1049 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1050False : stateResult 8 mc1050 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1051False : stateResult 8 mc1051 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1052False : stateResult 8 mc1052 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1053False : stateResult 8 mc1053 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1054False : stateResult 8 mc1054 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1055False : stateResult 8 mc1055 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1056False : stateResult 8 mc1056 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1057False : stateResult 8 mc1057 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1058False : stateResult 8 mc1058 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1059False : stateResult 8 mc1059 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1060False : stateResult 8 mc1060 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1061False : stateResult 8 mc1061 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1062False : stateResult 8 mc1062 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1063False : stateResult 8 mc1063 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1064False : stateResult 8 mc1064 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1065False : stateResult 8 mc1065 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1066False : stateResult 8 mc1066 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1067False : stateResult 8 mc1067 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1015Children : List SearchState := [mc1016,mc1017,mc1018,mc1019,mc1020,mc1021,mc1022,mc1023,mc1024,mc1025,mc1026,mc1027,mc1028,mc1029,mc1030,mc1031,mc1032,mc1033,mc1034,mc1035,mc1036,mc1037,mc1038,mc1039,mc1040,mc1041,mc1042,mc1043,mc1044,mc1045,mc1046,mc1047,mc1048,mc1049,mc1050,mc1051,mc1052,mc1053,mc1054,mc1055,mc1056,mc1057,mc1058,mc1059,mc1060,mc1061,mc1062,mc1063,mc1064,mc1065,mc1066,mc1067]
theorem mc1015False : stateResult 9 mc1015 = false := by
  apply coverResult (k := 6) (states := mc1015Children)
  · change mc1015Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc1015Children, List.all_cons, List.all_nil, mc1016False, mc1017False, mc1018False, mc1019False, mc1020False, mc1021False, mc1022False, mc1023False, mc1024False, mc1025False, mc1026False, mc1027False, mc1028False, mc1029False, mc1030False, mc1031False, mc1032False, mc1033False, mc1034False, mc1035False, mc1036False, mc1037False, mc1038False, mc1039False, mc1040False, mc1041False, mc1042False, mc1043False, mc1044False, mc1045False, mc1046False, mc1047False, mc1048False, mc1049False, mc1050False, mc1051False, mc1052False, mc1053False, mc1054False, mc1055False, mc1056False, mc1057False, mc1058False, mc1059False, mc1060False, mc1061False, mc1062False, mc1063False, mc1064False, mc1065False, mc1066False, mc1067False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1069False : stateResult 8 mc1069 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1070False : stateResult 8 mc1070 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1071False : stateResult 8 mc1071 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1072False : stateResult 8 mc1072 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1073False : stateResult 8 mc1073 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1074False : stateResult 8 mc1074 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1075False : stateResult 8 mc1075 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1076False : stateResult 8 mc1076 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1077False : stateResult 8 mc1077 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1078False : stateResult 8 mc1078 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1079False : stateResult 8 mc1079 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1080False : stateResult 8 mc1080 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1081False : stateResult 8 mc1081 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1082False : stateResult 8 mc1082 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1083False : stateResult 8 mc1083 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1084False : stateResult 8 mc1084 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1085False : stateResult 8 mc1085 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1086False : stateResult 8 mc1086 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1087False : stateResult 8 mc1087 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1088False : stateResult 8 mc1088 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1089False : stateResult 8 mc1089 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1090False : stateResult 8 mc1090 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1091False : stateResult 8 mc1091 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1092False : stateResult 8 mc1092 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1093False : stateResult 8 mc1093 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1094False : stateResult 8 mc1094 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1095False : stateResult 8 mc1095 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1096False : stateResult 8 mc1096 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1097False : stateResult 8 mc1097 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1098False : stateResult 8 mc1098 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1099False : stateResult 8 mc1099 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1100False : stateResult 8 mc1100 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1101False : stateResult 8 mc1101 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1102False : stateResult 8 mc1102 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1103False : stateResult 8 mc1103 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1104False : stateResult 8 mc1104 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1105False : stateResult 8 mc1105 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1106False : stateResult 8 mc1106 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1107False : stateResult 8 mc1107 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1108False : stateResult 8 mc1108 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1109False : stateResult 8 mc1109 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1068Children : List SearchState := [mc1069,mc1070,mc1071,mc1072,mc1073,mc1074,mc1075,mc1076,mc1077,mc1078,mc1079,mc1080,mc1081,mc1082,mc1083,mc1084,mc1085,mc1086,mc1087,mc1088,mc1089,mc1090,mc1091,mc1092,mc1093,mc1094,mc1095,mc1096,mc1097,mc1098,mc1099,mc1100,mc1101,mc1102,mc1103,mc1104,mc1105,mc1106,mc1107,mc1108,mc1109]
theorem mc1068False : stateResult 9 mc1068 = false := by
  apply coverResult (k := 6) (states := mc1068Children)
  · change mc1068Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc1068Children, List.all_cons, List.all_nil, mc1069False, mc1070False, mc1071False, mc1072False, mc1073False, mc1074False, mc1075False, mc1076False, mc1077False, mc1078False, mc1079False, mc1080False, mc1081False, mc1082False, mc1083False, mc1084False, mc1085False, mc1086False, mc1087False, mc1088False, mc1089False, mc1090False, mc1091False, mc1092False, mc1093False, mc1094False, mc1095False, mc1096False, mc1097False, mc1098False, mc1099False, mc1100False, mc1101False, mc1102False, mc1103False, mc1104False, mc1105False, mc1106False, mc1107False, mc1108False, mc1109False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1111False : stateResult 8 mc1111 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1112False : stateResult 8 mc1112 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1113False : stateResult 8 mc1113 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1114False : stateResult 8 mc1114 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1115False : stateResult 8 mc1115 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1116False : stateResult 8 mc1116 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1117False : stateResult 8 mc1117 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1118False : stateResult 8 mc1118 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1119False : stateResult 8 mc1119 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1120False : stateResult 8 mc1120 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1121False : stateResult 8 mc1121 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1122False : stateResult 8 mc1122 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1123False : stateResult 8 mc1123 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1124False : stateResult 8 mc1124 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1125False : stateResult 8 mc1125 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1126False : stateResult 8 mc1126 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1127False : stateResult 8 mc1127 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1128False : stateResult 8 mc1128 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1129False : stateResult 8 mc1129 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1130False : stateResult 8 mc1130 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1131False : stateResult 8 mc1131 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1132False : stateResult 8 mc1132 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1133False : stateResult 8 mc1133 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1134False : stateResult 8 mc1134 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1135False : stateResult 8 mc1135 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1136False : stateResult 8 mc1136 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1137False : stateResult 8 mc1137 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1138False : stateResult 8 mc1138 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1139False : stateResult 8 mc1139 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1140False : stateResult 8 mc1140 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1141False : stateResult 8 mc1141 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1142False : stateResult 8 mc1142 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1143False : stateResult 8 mc1143 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1144False : stateResult 8 mc1144 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1145False : stateResult 8 mc1145 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1146False : stateResult 8 mc1146 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1147False : stateResult 8 mc1147 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1148False : stateResult 8 mc1148 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1149False : stateResult 8 mc1149 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1150False : stateResult 8 mc1150 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1151False : stateResult 8 mc1151 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1110Children : List SearchState := [mc1111,mc1112,mc1113,mc1114,mc1115,mc1116,mc1117,mc1118,mc1119,mc1120,mc1121,mc1122,mc1123,mc1124,mc1125,mc1126,mc1127,mc1128,mc1129,mc1130,mc1131,mc1132,mc1133,mc1134,mc1135,mc1136,mc1137,mc1138,mc1139,mc1140,mc1141,mc1142,mc1143,mc1144,mc1145,mc1146,mc1147,mc1148,mc1149,mc1150,mc1151]
theorem mc1110False : stateResult 9 mc1110 = false := by
  apply coverResult (k := 6) (states := mc1110Children)
  · change mc1110Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc1110Children, List.all_cons, List.all_nil, mc1111False, mc1112False, mc1113False, mc1114False, mc1115False, mc1116False, mc1117False, mc1118False, mc1119False, mc1120False, mc1121False, mc1122False, mc1123False, mc1124False, mc1125False, mc1126False, mc1127False, mc1128False, mc1129False, mc1130False, mc1131False, mc1132False, mc1133False, mc1134False, mc1135False, mc1136False, mc1137False, mc1138False, mc1139False, mc1140False, mc1141False, mc1142False, mc1143False, mc1144False, mc1145False, mc1146False, mc1147False, mc1148False, mc1149False, mc1150False, mc1151False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1153False : stateResult 8 mc1153 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1154False : stateResult 8 mc1154 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1155False : stateResult 8 mc1155 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1156False : stateResult 8 mc1156 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1158False : stateResult 7 mc1158 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1159False : stateResult 7 mc1159 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1160False : stateResult 7 mc1160 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1161False : stateResult 7 mc1161 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1162False : stateResult 7 mc1162 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1163False : stateResult 7 mc1163 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1164False : stateResult 7 mc1164 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1165False : stateResult 7 mc1165 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1166False : stateResult 7 mc1166 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1167False : stateResult 7 mc1167 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1168False : stateResult 7 mc1168 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1169False : stateResult 7 mc1169 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1170False : stateResult 7 mc1170 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1171False : stateResult 7 mc1171 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1172False : stateResult 7 mc1172 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1173False : stateResult 7 mc1173 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1174False : stateResult 7 mc1174 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1175False : stateResult 7 mc1175 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1176False : stateResult 7 mc1176 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1177False : stateResult 7 mc1177 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1178False : stateResult 7 mc1178 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1179False : stateResult 7 mc1179 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1180False : stateResult 7 mc1180 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1181False : stateResult 7 mc1181 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1182False : stateResult 7 mc1182 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1183False : stateResult 7 mc1183 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1184False : stateResult 7 mc1184 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1185False : stateResult 7 mc1185 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1186False : stateResult 7 mc1186 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1187False : stateResult 7 mc1187 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1188False : stateResult 7 mc1188 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1189False : stateResult 7 mc1189 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1190False : stateResult 7 mc1190 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1157Children : List SearchState := [mc1158,mc1159,mc1160,mc1161,mc1162,mc1163,mc1164,mc1165,mc1166,mc1167,mc1168,mc1169,mc1170,mc1171,mc1172,mc624,mc1173,mc1174,mc700,mc1175,mc1176,mc1177,mc1178,mc1179,mc1180,mc1181,mc1182,mc1183,mc1184,mc1185,mc1186,mc1187,mc1188,mc1189,mc1190]
theorem mc1157False : stateResult 8 mc1157 = false := by
  apply coverResult (k := 5) (states := mc1157Children)
  · change mc1157Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc1157Children, List.all_cons, List.all_nil, mc1158False, mc1159False, mc1160False, mc1161False, mc1162False, mc1163False, mc1164False, mc1165False, mc1166False, mc1167False, mc1168False, mc1169False, mc1170False, mc1171False, mc1172False, mc624False, mc1173False, mc1174False, mc700False, mc1175False, mc1176False, mc1177False, mc1178False, mc1179False, mc1180False, mc1181False, mc1182False, mc1183False, mc1184False, mc1185False, mc1186False, mc1187False, mc1188False, mc1189False, mc1190False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1191False : stateResult 8 mc1191 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1192False : stateResult 8 mc1192 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1193False : stateResult 8 mc1193 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1194False : stateResult 8 mc1194 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1195False : stateResult 8 mc1195 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1196False : stateResult 8 mc1196 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1198False : stateResult 7 mc1198 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1199False : stateResult 7 mc1199 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1200False : stateResult 7 mc1200 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1201False : stateResult 7 mc1201 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1202False : stateResult 7 mc1202 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1203False : stateResult 7 mc1203 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1204False : stateResult 7 mc1204 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1205False : stateResult 7 mc1205 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1206False : stateResult 7 mc1206 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1207False : stateResult 7 mc1207 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1208False : stateResult 7 mc1208 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1209False : stateResult 7 mc1209 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1210False : stateResult 7 mc1210 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1211False : stateResult 7 mc1211 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1212False : stateResult 7 mc1212 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1213False : stateResult 7 mc1213 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1214False : stateResult 7 mc1214 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1215False : stateResult 7 mc1215 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1216False : stateResult 7 mc1216 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1217False : stateResult 7 mc1217 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1218False : stateResult 7 mc1218 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1219False : stateResult 7 mc1219 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1220False : stateResult 7 mc1220 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1221False : stateResult 7 mc1221 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1222False : stateResult 7 mc1222 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1223False : stateResult 7 mc1223 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1224False : stateResult 7 mc1224 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1225False : stateResult 7 mc1225 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1226False : stateResult 7 mc1226 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1227False : stateResult 7 mc1227 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1228False : stateResult 7 mc1228 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1229False : stateResult 7 mc1229 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1230False : stateResult 7 mc1230 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1231False : stateResult 7 mc1231 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1232False : stateResult 7 mc1232 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1197Children : List SearchState := [mc1198,mc1199,mc1200,mc1201,mc1202,mc1203,mc1204,mc1205,mc1206,mc1207,mc1208,mc1209,mc1210,mc1211,mc1212,mc1213,mc1214,mc1215,mc1216,mc1217,mc1218,mc1219,mc1220,mc1221,mc1222,mc1223,mc1224,mc1225,mc1226,mc1227,mc1228,mc1229,mc1230,mc1231,mc1232]
theorem mc1197False : stateResult 8 mc1197 = false := by
  apply coverResult (k := 5) (states := mc1197Children)
  · change mc1197Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc1197Children, List.all_cons, List.all_nil, mc1198False, mc1199False, mc1200False, mc1201False, mc1202False, mc1203False, mc1204False, mc1205False, mc1206False, mc1207False, mc1208False, mc1209False, mc1210False, mc1211False, mc1212False, mc1213False, mc1214False, mc1215False, mc1216False, mc1217False, mc1218False, mc1219False, mc1220False, mc1221False, mc1222False, mc1223False, mc1224False, mc1225False, mc1226False, mc1227False, mc1228False, mc1229False, mc1230False, mc1231False, mc1232False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1233False : stateResult 8 mc1233 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1234False : stateResult 8 mc1234 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1235False : stateResult 8 mc1235 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1236False : stateResult 8 mc1236 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1238False : stateResult 7 mc1238 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1239False : stateResult 7 mc1239 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1240False : stateResult 7 mc1240 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1241False : stateResult 7 mc1241 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1242False : stateResult 7 mc1242 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1243False : stateResult 7 mc1243 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1244False : stateResult 7 mc1244 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1245False : stateResult 7 mc1245 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1246False : stateResult 7 mc1246 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1247False : stateResult 7 mc1247 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1248False : stateResult 7 mc1248 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1249False : stateResult 7 mc1249 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1250False : stateResult 7 mc1250 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1251False : stateResult 7 mc1251 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1252False : stateResult 7 mc1252 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1253False : stateResult 7 mc1253 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1254False : stateResult 7 mc1254 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1255False : stateResult 7 mc1255 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1256False : stateResult 7 mc1256 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1257False : stateResult 7 mc1257 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1258False : stateResult 7 mc1258 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1259False : stateResult 7 mc1259 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1260False : stateResult 7 mc1260 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1261False : stateResult 7 mc1261 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1262False : stateResult 7 mc1262 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1263False : stateResult 7 mc1263 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1264False : stateResult 7 mc1264 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1265False : stateResult 7 mc1265 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1266False : stateResult 7 mc1266 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1267False : stateResult 7 mc1267 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1237Children : List SearchState := [mc1238,mc1239,mc1240,mc1241,mc1242,mc1243,mc1244,mc1245,mc1246,mc1247,mc1248,mc1249,mc1250,mc1251,mc1252,mc1253,mc1254,mc1255,mc1256,mc1257,mc1258,mc1259,mc1260,mc1261,mc1262,mc1263,mc1264,mc1265,mc1266,mc1267]
theorem mc1237False : stateResult 8 mc1237 = false := by
  apply coverResult (k := 5) (states := mc1237Children)
  · change mc1237Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc1237Children, List.all_cons, List.all_nil, mc1238False, mc1239False, mc1240False, mc1241False, mc1242False, mc1243False, mc1244False, mc1245False, mc1246False, mc1247False, mc1248False, mc1249False, mc1250False, mc1251False, mc1252False, mc1253False, mc1254False, mc1255False, mc1256False, mc1257False, mc1258False, mc1259False, mc1260False, mc1261False, mc1262False, mc1263False, mc1264False, mc1265False, mc1266False, mc1267False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1268False : stateResult 8 mc1268 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1269False : stateResult 8 mc1269 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1270False : stateResult 8 mc1270 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1271False : stateResult 8 mc1271 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1272False : stateResult 8 mc1272 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1273False : stateResult 8 mc1273 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1274False : stateResult 8 mc1274 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1275False : stateResult 8 mc1275 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1276False : stateResult 8 mc1276 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1277False : stateResult 8 mc1277 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1278False : stateResult 8 mc1278 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1279False : stateResult 8 mc1279 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1280False : stateResult 8 mc1280 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1281False : stateResult 8 mc1281 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1152Children : List SearchState := [mc1153,mc1154,mc1155,mc1156,mc1157,mc1191,mc1192,mc1193,mc1194,mc1195,mc1196,mc1197,mc1233,mc1234,mc1235,mc1236,mc1237,mc1268,mc1269,mc1270,mc1271,mc1272,mc1273,mc1274,mc1275,mc1276,mc1277,mc1278,mc1279,mc1280,mc1281]
theorem mc1152False : stateResult 9 mc1152 = false := by
  apply coverResult (k := 6) (states := mc1152Children)
  · change mc1152Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc1152Children, List.all_cons, List.all_nil, mc1153False, mc1154False, mc1155False, mc1156False, mc1157False, mc1191False, mc1192False, mc1193False, mc1194False, mc1195False, mc1196False, mc1197False, mc1233False, mc1234False, mc1235False, mc1236False, mc1237False, mc1268False, mc1269False, mc1270False, mc1271False, mc1272False, mc1273False, mc1274False, mc1275False, mc1276False, mc1277False, mc1278False, mc1279False, mc1280False, mc1281False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1283False : stateResult 8 mc1283 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1284False : stateResult 8 mc1284 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1285False : stateResult 8 mc1285 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1286False : stateResult 8 mc1286 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1287False : stateResult 8 mc1287 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1288False : stateResult 8 mc1288 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1289False : stateResult 8 mc1289 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1290False : stateResult 8 mc1290 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1291False : stateResult 8 mc1291 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1292False : stateResult 8 mc1292 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1293False : stateResult 8 mc1293 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1294False : stateResult 8 mc1294 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1295False : stateResult 8 mc1295 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1296False : stateResult 8 mc1296 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1297False : stateResult 8 mc1297 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1298False : stateResult 8 mc1298 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1299False : stateResult 8 mc1299 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1300False : stateResult 8 mc1300 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1301False : stateResult 8 mc1301 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1302False : stateResult 8 mc1302 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1303False : stateResult 8 mc1303 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1304False : stateResult 8 mc1304 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1305False : stateResult 8 mc1305 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1306False : stateResult 8 mc1306 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1307False : stateResult 8 mc1307 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1308False : stateResult 8 mc1308 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1309False : stateResult 8 mc1309 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1310False : stateResult 8 mc1310 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1311False : stateResult 8 mc1311 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1312False : stateResult 8 mc1312 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1313False : stateResult 8 mc1313 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1314False : stateResult 8 mc1314 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1315False : stateResult 8 mc1315 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1316False : stateResult 8 mc1316 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1317False : stateResult 8 mc1317 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1318False : stateResult 8 mc1318 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1319False : stateResult 8 mc1319 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1282Children : List SearchState := [mc1283,mc1284,mc1285,mc1286,mc1287,mc1288,mc1289,mc1290,mc1291,mc1292,mc1293,mc1294,mc1295,mc1296,mc1297,mc1298,mc1299,mc1300,mc1301,mc1302,mc1303,mc1304,mc1305,mc1306,mc1307,mc1308,mc1309,mc1310,mc1311,mc1312,mc1313,mc1314,mc1315,mc1316,mc1317,mc1318,mc1319]
theorem mc1282False : stateResult 9 mc1282 = false := by
  apply coverResult (k := 6) (states := mc1282Children)
  · change mc1282Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc1282Children, List.all_cons, List.all_nil, mc1283False, mc1284False, mc1285False, mc1286False, mc1287False, mc1288False, mc1289False, mc1290False, mc1291False, mc1292False, mc1293False, mc1294False, mc1295False, mc1296False, mc1297False, mc1298False, mc1299False, mc1300False, mc1301False, mc1302False, mc1303False, mc1304False, mc1305False, mc1306False, mc1307False, mc1308False, mc1309False, mc1310False, mc1311False, mc1312False, mc1313False, mc1314False, mc1315False, mc1316False, mc1317False, mc1318False, mc1319False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1321False : stateResult 8 mc1321 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1322False : stateResult 8 mc1322 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1323False : stateResult 8 mc1323 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1324False : stateResult 8 mc1324 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1325False : stateResult 8 mc1325 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1326False : stateResult 8 mc1326 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1327False : stateResult 8 mc1327 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1328False : stateResult 8 mc1328 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1329False : stateResult 8 mc1329 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1330False : stateResult 8 mc1330 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1331False : stateResult 8 mc1331 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1332False : stateResult 8 mc1332 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1333False : stateResult 8 mc1333 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1334False : stateResult 8 mc1334 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1335False : stateResult 8 mc1335 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1336False : stateResult 8 mc1336 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1337False : stateResult 8 mc1337 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1338False : stateResult 8 mc1338 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1339False : stateResult 8 mc1339 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1340False : stateResult 8 mc1340 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1341False : stateResult 8 mc1341 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1342False : stateResult 8 mc1342 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1343False : stateResult 8 mc1343 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1344False : stateResult 8 mc1344 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1345False : stateResult 8 mc1345 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1346False : stateResult 8 mc1346 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1347False : stateResult 8 mc1347 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1348False : stateResult 8 mc1348 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1349False : stateResult 8 mc1349 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1350False : stateResult 8 mc1350 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1351False : stateResult 8 mc1351 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1352False : stateResult 8 mc1352 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1353False : stateResult 8 mc1353 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1354False : stateResult 8 mc1354 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1355False : stateResult 8 mc1355 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1356False : stateResult 8 mc1356 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1357False : stateResult 8 mc1357 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1358False : stateResult 8 mc1358 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1320Children : List SearchState := [mc1321,mc1322,mc1323,mc1324,mc1325,mc1326,mc1327,mc1328,mc1329,mc1330,mc1331,mc1332,mc1333,mc1334,mc1335,mc1336,mc1337,mc1338,mc1339,mc1340,mc1341,mc1342,mc1343,mc1344,mc1345,mc1346,mc1347,mc1348,mc1349,mc1350,mc1351,mc1352,mc1353,mc1354,mc1355,mc1356,mc1357,mc1358]
theorem mc1320False : stateResult 9 mc1320 = false := by
  apply coverResult (k := 6) (states := mc1320Children)
  · change mc1320Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc1320Children, List.all_cons, List.all_nil, mc1321False, mc1322False, mc1323False, mc1324False, mc1325False, mc1326False, mc1327False, mc1328False, mc1329False, mc1330False, mc1331False, mc1332False, mc1333False, mc1334False, mc1335False, mc1336False, mc1337False, mc1338False, mc1339False, mc1340False, mc1341False, mc1342False, mc1343False, mc1344False, mc1345False, mc1346False, mc1347False, mc1348False, mc1349False, mc1350False, mc1351False, mc1352False, mc1353False, mc1354False, mc1355False, mc1356False, mc1357False, mc1358False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1360False : stateResult 8 mc1360 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1361False : stateResult 8 mc1361 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1362False : stateResult 8 mc1362 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1363False : stateResult 8 mc1363 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1364False : stateResult 8 mc1364 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1365False : stateResult 8 mc1365 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1366False : stateResult 8 mc1366 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1367False : stateResult 8 mc1367 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1368False : stateResult 8 mc1368 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1369False : stateResult 8 mc1369 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1370False : stateResult 8 mc1370 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1371False : stateResult 8 mc1371 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1372False : stateResult 8 mc1372 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1373False : stateResult 8 mc1373 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1374False : stateResult 8 mc1374 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1376False : stateResult 7 mc1376 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1377False : stateResult 7 mc1377 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1378False : stateResult 7 mc1378 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1379False : stateResult 7 mc1379 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1380False : stateResult 7 mc1380 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1381False : stateResult 7 mc1381 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1382False : stateResult 7 mc1382 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1383False : stateResult 7 mc1383 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1384False : stateResult 7 mc1384 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1385False : stateResult 7 mc1385 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1386False : stateResult 7 mc1386 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1387False : stateResult 7 mc1387 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1388False : stateResult 7 mc1388 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1389False : stateResult 7 mc1389 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1390False : stateResult 7 mc1390 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1391False : stateResult 7 mc1391 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1392False : stateResult 7 mc1392 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1393False : stateResult 7 mc1393 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1394False : stateResult 7 mc1394 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1395False : stateResult 7 mc1395 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1396False : stateResult 7 mc1396 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1397False : stateResult 7 mc1397 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1398False : stateResult 7 mc1398 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1399False : stateResult 7 mc1399 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1400False : stateResult 7 mc1400 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1401False : stateResult 7 mc1401 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1402False : stateResult 7 mc1402 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1403False : stateResult 7 mc1403 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1404False : stateResult 7 mc1404 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1405False : stateResult 7 mc1405 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1375Children : List SearchState := [mc1376,mc1377,mc1378,mc1379,mc1380,mc1381,mc1382,mc1383,mc1384,mc1385,mc1386,mc1387,mc1388,mc1389,mc1390,mc1391,mc1392,mc1393,mc1394,mc1395,mc1396,mc1397,mc1398,mc1399,mc1400,mc1401,mc1402,mc1403,mc1404,mc1405]
theorem mc1375False : stateResult 8 mc1375 = false := by
  apply coverResult (k := 5) (states := mc1375Children)
  · change mc1375Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc1375Children, List.all_cons, List.all_nil, mc1376False, mc1377False, mc1378False, mc1379False, mc1380False, mc1381False, mc1382False, mc1383False, mc1384False, mc1385False, mc1386False, mc1387False, mc1388False, mc1389False, mc1390False, mc1391False, mc1392False, mc1393False, mc1394False, mc1395False, mc1396False, mc1397False, mc1398False, mc1399False, mc1400False, mc1401False, mc1402False, mc1403False, mc1404False, mc1405False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1406False : stateResult 8 mc1406 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1407False : stateResult 8 mc1407 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1408False : stateResult 8 mc1408 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1409False : stateResult 8 mc1409 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1410False : stateResult 8 mc1410 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1411False : stateResult 8 mc1411 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1413False : stateResult 7 mc1413 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1414False : stateResult 7 mc1414 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1415False : stateResult 7 mc1415 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1416False : stateResult 7 mc1416 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1417False : stateResult 7 mc1417 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1418False : stateResult 7 mc1418 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1419False : stateResult 7 mc1419 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1420False : stateResult 7 mc1420 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1421False : stateResult 7 mc1421 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1422False : stateResult 7 mc1422 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1423False : stateResult 7 mc1423 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1424False : stateResult 7 mc1424 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1425False : stateResult 7 mc1425 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1426False : stateResult 7 mc1426 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1412Children : List SearchState := [mc1413,mc1414,mc1415,mc1416,mc1417,mc1418,mc1419,mc1420,mc1421,mc1422,mc1423,mc1424,mc1425,mc1426]
theorem mc1412False : stateResult 8 mc1412 = false := by
  apply coverResult (k := 5) (states := mc1412Children)
  · change mc1412Children.all (fun c => !(stateResult 7 c)) = true
    simp only [mc1412Children, List.all_cons, List.all_nil, mc1413False, mc1414False, mc1415False, mc1416False, mc1417False, mc1418False, mc1419False, mc1420False, mc1421False, mc1422False, mc1423False, mc1424False, mc1425False, mc1426False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1427False : stateResult 8 mc1427 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1428False : stateResult 8 mc1428 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1429False : stateResult 8 mc1429 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1430False : stateResult 8 mc1430 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1431False : stateResult 8 mc1431 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1432False : stateResult 8 mc1432 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1433False : stateResult 8 mc1433 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1359Children : List SearchState := [mc1360,mc1361,mc1362,mc1363,mc1364,mc459,mc1365,mc1366,mc1367,mc1368,mc1369,mc1370,mc1333,mc1371,mc1372,mc1373,mc1374,mc1375,mc1406,mc1407,mc1408,mc1409,mc1410,mc1411,mc1412,mc1427,mc1428,mc1429,mc1430,mc1431,mc1432,mc1433]
theorem mc1359False : stateResult 9 mc1359 = false := by
  apply coverResult (k := 6) (states := mc1359Children)
  · change mc1359Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc1359Children, List.all_cons, List.all_nil, mc1360False, mc1361False, mc1362False, mc1363False, mc1364False, mc459False, mc1365False, mc1366False, mc1367False, mc1368False, mc1369False, mc1370False, mc1333False, mc1371False, mc1372False, mc1373False, mc1374False, mc1375False, mc1406False, mc1407False, mc1408False, mc1409False, mc1410False, mc1411False, mc1412False, mc1427False, mc1428False, mc1429False, mc1430False, mc1431False, mc1432False, mc1433False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1435False : stateResult 8 mc1435 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1436False : stateResult 8 mc1436 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1437False : stateResult 8 mc1437 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1438False : stateResult 8 mc1438 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1439False : stateResult 8 mc1439 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1440False : stateResult 8 mc1440 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1441False : stateResult 8 mc1441 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1442False : stateResult 8 mc1442 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1443False : stateResult 8 mc1443 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1444False : stateResult 8 mc1444 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1445False : stateResult 8 mc1445 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1446False : stateResult 8 mc1446 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1447False : stateResult 8 mc1447 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1448False : stateResult 8 mc1448 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1449False : stateResult 8 mc1449 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1450False : stateResult 8 mc1450 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1451False : stateResult 8 mc1451 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1452False : stateResult 8 mc1452 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1453False : stateResult 8 mc1453 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1454False : stateResult 8 mc1454 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1455False : stateResult 8 mc1455 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1456False : stateResult 8 mc1456 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1457False : stateResult 8 mc1457 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1458False : stateResult 8 mc1458 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1459False : stateResult 8 mc1459 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1460False : stateResult 8 mc1460 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1461False : stateResult 8 mc1461 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1462False : stateResult 8 mc1462 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1463False : stateResult 8 mc1463 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1464False : stateResult 8 mc1464 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1465False : stateResult 8 mc1465 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1466False : stateResult 8 mc1466 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1467False : stateResult 8 mc1467 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1468False : stateResult 8 mc1468 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1469False : stateResult 8 mc1469 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1470False : stateResult 8 mc1470 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1471False : stateResult 8 mc1471 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1472False : stateResult 8 mc1472 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1473False : stateResult 8 mc1473 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1474False : stateResult 8 mc1474 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1475False : stateResult 8 mc1475 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1476False : stateResult 8 mc1476 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1477False : stateResult 8 mc1477 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1478False : stateResult 8 mc1478 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1479False : stateResult 8 mc1479 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1480False : stateResult 8 mc1480 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1434Children : List SearchState := [mc1435,mc1436,mc1437,mc1438,mc1439,mc1440,mc1441,mc1442,mc1443,mc1444,mc1445,mc1446,mc1447,mc1448,mc1449,mc1450,mc1451,mc1452,mc1453,mc1454,mc1455,mc1456,mc1457,mc1458,mc1459,mc1460,mc1461,mc1462,mc1463,mc1464,mc1465,mc1466,mc1467,mc1468,mc1469,mc1470,mc1471,mc1472,mc1473,mc1474,mc1475,mc1476,mc1477,mc1478,mc1479,mc1480]
theorem mc1434False : stateResult 9 mc1434 = false := by
  apply coverResult (k := 6) (states := mc1434Children)
  · change mc1434Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc1434Children, List.all_cons, List.all_nil, mc1435False, mc1436False, mc1437False, mc1438False, mc1439False, mc1440False, mc1441False, mc1442False, mc1443False, mc1444False, mc1445False, mc1446False, mc1447False, mc1448False, mc1449False, mc1450False, mc1451False, mc1452False, mc1453False, mc1454False, mc1455False, mc1456False, mc1457False, mc1458False, mc1459False, mc1460False, mc1461False, mc1462False, mc1463False, mc1464False, mc1465False, mc1466False, mc1467False, mc1468False, mc1469False, mc1470False, mc1471False, mc1472False, mc1473False, mc1474False, mc1475False, mc1476False, mc1477False, mc1478False, mc1479False, mc1480False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1482False : stateResult 8 mc1482 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1483False : stateResult 8 mc1483 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1484False : stateResult 8 mc1484 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1485False : stateResult 8 mc1485 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1486False : stateResult 8 mc1486 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1487False : stateResult 8 mc1487 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1488False : stateResult 8 mc1488 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1489False : stateResult 8 mc1489 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1490False : stateResult 8 mc1490 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1491False : stateResult 8 mc1491 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1492False : stateResult 8 mc1492 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1493False : stateResult 8 mc1493 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1494False : stateResult 8 mc1494 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1495False : stateResult 8 mc1495 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1496False : stateResult 8 mc1496 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1497False : stateResult 8 mc1497 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1498False : stateResult 8 mc1498 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1499False : stateResult 8 mc1499 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1500False : stateResult 8 mc1500 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1501False : stateResult 8 mc1501 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1502False : stateResult 8 mc1502 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1503False : stateResult 8 mc1503 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1504False : stateResult 8 mc1504 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1505False : stateResult 8 mc1505 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1506False : stateResult 8 mc1506 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1507False : stateResult 8 mc1507 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1508False : stateResult 8 mc1508 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1509False : stateResult 8 mc1509 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1510False : stateResult 8 mc1510 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1511False : stateResult 8 mc1511 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1512False : stateResult 8 mc1512 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1513False : stateResult 8 mc1513 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1514False : stateResult 8 mc1514 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1515False : stateResult 8 mc1515 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1516False : stateResult 8 mc1516 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1517False : stateResult 8 mc1517 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1518False : stateResult 8 mc1518 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1519False : stateResult 8 mc1519 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1520False : stateResult 8 mc1520 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1521False : stateResult 8 mc1521 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1522False : stateResult 8 mc1522 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1523False : stateResult 8 mc1523 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1524False : stateResult 8 mc1524 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1525False : stateResult 8 mc1525 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1526False : stateResult 8 mc1526 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1527False : stateResult 8 mc1527 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1528False : stateResult 8 mc1528 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1529False : stateResult 8 mc1529 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1530False : stateResult 8 mc1530 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1531False : stateResult 8 mc1531 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1532False : stateResult 8 mc1532 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1533False : stateResult 8 mc1533 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1534False : stateResult 8 mc1534 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1535False : stateResult 8 mc1535 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem mc1536False : stateResult 8 mc1536 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
def mc1481Children : List SearchState := [mc1482,mc1483,mc1484,mc1485,mc1486,mc1487,mc1488,mc1489,mc1490,mc1333,mc1491,mc1492,mc1493,mc1494,mc1495,mc1496,mc1497,mc1498,mc1499,mc1500,mc1501,mc1502,mc1503,mc1504,mc1505,mc1506,mc1507,mc1508,mc1509,mc1510,mc1511,mc1512,mc1513,mc1514,mc1515,mc1516,mc1517,mc1518,mc1519,mc1520,mc1521,mc1522,mc1523,mc1524,mc1525,mc1526,mc1527,mc1528,mc1529,mc1530,mc1531,mc1532,mc1533,mc1534,mc1535,mc1536]
theorem mc1481False : stateResult 9 mc1481 = false := by
  apply coverResult (k := 6) (states := mc1481Children)
  · change mc1481Children.all (fun c => !(stateResult 8 c)) = true
    simp only [mc1481Children, List.all_cons, List.all_nil, mc1482False, mc1483False, mc1484False, mc1485False, mc1486False, mc1487False, mc1488False, mc1489False, mc1490False, mc1333False, mc1491False, mc1492False, mc1493False, mc1494False, mc1495False, mc1496False, mc1497False, mc1498False, mc1499False, mc1500False, mc1501False, mc1502False, mc1503False, mc1504False, mc1505False, mc1506False, mc1507False, mc1508False, mc1509False, mc1510False, mc1511False, mc1512False, mc1513False, mc1514False, mc1515False, mc1516False, mc1517False, mc1518False, mc1519False, mc1520False, mc1521False, mc1522False, mc1523False, mc1524False, mc1525False, mc1526False, mc1527False, mc1528False, mc1529False, mc1530False, mc1531False, mc1532False, mc1533False, mc1534False, mc1535False, mc1536False, Bool.not_false, Bool.and_self]
  · decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf0 : tab0.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf1 : tab1.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf2 : tab2.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf3 : tab3.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf4 : tab4.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc0 && true) = true
  simp [mc0False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf5 : tab5.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf6 : tab6.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf7 : tab7.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc34 && true) = true
  simp [mc34False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf8 : tab8.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf9 : tab9.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf10 : tab10.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf11 : tab11.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc49 && true) = true
  simp [mc49False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf12 : tab12.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf13 : tab13.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc93 && true) = true
  simp [mc93False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf14 : tab14.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf15 : tab15.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf16 : tab16.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf17 : tab17.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf18 : tab18.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc139 && true) = true
  simp [mc139False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf19 : tab19.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf20 : tab20.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc156 && true) = true
  simp [mc156False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf21 : tab21.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf22 : tab22.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf23 : tab23.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc188 && true) = true
  simp [mc188False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf24 : tab24.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc265 && true) = true
  simp [mc265False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf25 : tab25.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc308 && true) = true
  simp [mc308False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf26 : tab26.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf27 : tab27.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc355 && true) = true
  simp [mc355False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf28 : tab28.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf29 : tab29.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc401 && true) = true
  simp [mc401False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf30 : tab30.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf31 : tab31.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc447 && true) = true
  simp [mc447False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf32 : tab32.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf33 : tab33.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc485 && true) = true
  simp [mc485False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf34 : tab34.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf35 : tab35.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc529 && true) = true
  simp [mc529False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf36 : tab36.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf37 : tab37.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc575 && true) = true
  simp [mc575False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf38 : tab38.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf39 : tab39.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf40 : tab40.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc745 && true) = true
  simp [mc745False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf41 : tab41.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc922 && true) = true
  simp [mc922False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf42 : tab42.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc1015 && true) = true
  simp [mc1015False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf43 : tab43.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf44 : tab44.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc1068 && true) = true
  simp [mc1068False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf45 : tab45.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf46 : tab46.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc1110 && true) = true
  simp [mc1110False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf47 : tab47.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf48 : tab48.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf49 : tab49.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc1152 && true) = true
  simp [mc1152False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf50 : tab50.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc1282 && true) = true
  simp [mc1282False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf51 : tab51.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc1320 && true) = true
  simp [mc1320False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf52 : tab52.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf53 : tab53.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf54 : tab54.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc1359 && true) = true
  simp [mc1359False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf55 : tab55.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc1434 && true) = true
  simp [mc1434False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf56 : tab56.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf57 : tab57.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf58 : tab58.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf59 : tab59.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf60 : tab60.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf61 : tab61.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf62 : tab62.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf63 : tab63.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf64 : tab64.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  change (!stateResult 9 mc1481 && true) = true
  simp [mc1481False]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf65 : tab65.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf_all : table.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  simp only [table, List.all_append, leaf0, leaf1, leaf2, leaf3, leaf4, leaf5, leaf6, leaf7, leaf8, leaf9, leaf10, leaf11, leaf12, leaf13, leaf14, leaf15, leaf16, leaf17, leaf18, leaf19, leaf20, leaf21, leaf22, leaf23, leaf24, leaf25, leaf26, leaf27, leaf28, leaf29, leaf30, leaf31, leaf32, leaf33, leaf34, leaf35, leaf36, leaf37, leaf38, leaf39, leaf40, leaf41, leaf42, leaf43, leaf44, leaf45, leaf46, leaf47, leaf48, leaf49, leaf50, leaf51, leaf52, leaf53, leaf54, leaf55, leaf56, leaf57, leaf58, leaf59, leaf60, leaf61, leaf62, leaf63, leaf64, leaf65, Bool.and_self]

def optT (e last : ℕ) (ws : List W) : Bool := if (e, last, ws) ∈ table then false else optimized 9 e last ws

theorem optT_eq : optT = optimized 9 := by
  funext e last ws
  unfold optT
  split_ifs with h
  · have hc := List.all_eq_true.mp leaf_all _ h
    dsimp only at hc
    revert hc
    cases optimized 9 e last ws <;> simp
  · rfl

def optRoot (e last : ℕ) (ws : List W) : Bool :=
  scoreGuard e ws && (ws == [goal] || (pairs ws).any (fun (a, b, r) => dispatch e last optT a b r))

theorem optRoot_eq : optRoot = optimized 10 := by
  funext e last ws
  simp only [optRoot, optT_eq, optimized]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem all_front : inputs.sublists.all
    (fun l => decide (11 < l.length) || (cuts l != -1) || !(optRoot (11 - l.length) 0 l)) = true := by
  decide +kernel

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 10)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨gs, hlen, hord, S, hsub, hl⟩ := normalize_build BitVec.toNat (get_build C hm hr)
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
  have hsearch := optimized_complete 10 l (11 - l.length) 0 gs hnd hlenk (by omega) hord (hlS ▸ hl)
  rw [← optRoot_eq] at hsearch
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp all_front l hmem
  have h4 : decide (11 < l.length) = false := by simp; omega
  have h5 : (cuts l != -1) = false := by simp [hcuts]
  rw [h4, h5, hsearch] at hrow
  exact Bool.noConfusion hrow

end PEqualNP.Outside.L_meta_8973

theorem PEqualNP.Outside.L_meta_8973 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (14285 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_8973.no_small C hm hs hr
