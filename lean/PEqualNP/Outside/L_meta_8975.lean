import PEqualNP.Defs

/- Adapted from the checked live-circuit normalization and search in L-meta-6349. -/

namespace PEqualNP.Outside.L_meta_8975

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
  [0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294]

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
  [⟨64, 69, 114, 3, 0, 1⟩,
   ⟨79, 89, 94, 2, 0, 1⟩,
   ⟨104, 84, 99, 1, 2, 3⟩,
   ⟨74, 64, 89, 1, 0, 2⟩,
   ⟨114, 64, 109, 0, 1, 3⟩,
   ⟨89, 74, 79, 0, 1, 2⟩]

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

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (14302 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) := [(0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1)]

def negL : List (Fin 4 × Fin 4) := [(0, 0), (1, 1), (2, 3), (3, 2), (3, 3)]

def samp (k : Fin 128) : Fin 4 × Fin 4 :=
  if k.val < 64 then negL.getD (k.val % 5) (0, 0) else posL.getD (((k.val - 64) / 5) % 11) (0, 0)

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

def tab0 : List (ℕ × ℕ × List W) :=
  [(1, 0xff8000003fffffff318c6318c6318c63, [0xff8000003fffffff318c6318c6318c63, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab1 : List (ℕ × ℕ × List W) :=
  [(1, 0xff801fffc0007fff5294a5294a5294a5, [0xff801fffc0007fff5294a5294a5294a5, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab2 : List (ℕ × ℕ × List W) :=
  [(1, 0xffffe00000007fff9ce739ce739ce739, [0xffffe00000007fff9ce739ce739ce739, 0xff80000000007fff1084210842108421, 0x7fe000000000008c6318c6318c6318, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab3 : List (ℕ × ℕ × List W) :=
  [(1, 0x1084210842108421, [0x1084210842108421, 0xff80000000007fff1084210842108421, 0x3e007c00f80001084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab4 : List (ℕ × ℕ × List W) :=
  [(3, 0xff83e007c00fffff1084210842108421, [0xff83e007c00fffff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab5 : List (ℕ × ℕ × List W) :=
  [(2, 0xff83e007c00fffff1084210842108421, [0xff83e007c00fffff1084210842108421, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab6 : List (ℕ × ℕ × List W) :=
  [(2, 0xff83e007c00fffff1084210842108421, [0xff83e007c00fffff1084210842108421, 0x3e007c00f80001084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab7 : List (ℕ × ℕ × List W) :=
  [(1, 0xff83e007c00fffff1084210842108421, [0xff83e007c00fffff1084210842108421, 0xff80000000007fff1084210842108421, 0x3e007c00f80001084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab8 : List (ℕ × ℕ × List W) :=
  [(1, 0xf8000000000001f0000000000000000, [0xf8000000000001f0000000000000000, 0xff80000000007fff1084210842108421, 0xffc00f80000001f2108421084210842, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab9 : List (ℕ × ℕ × List W) :=
  [(1, 0xfffc00f800007fff318c6318c6318c63, [0xfffc00f800007fff318c6318c6318c63, 0xff80000000007fff1084210842108421, 0xffc00f80000001f2108421084210842, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab10 : List (ℕ × ℕ × List W) :=
  [(1, 0xf0000000000003e00000000000000000, [0xf0000000000003e00000000000000000, 0xff80000000007fff1084210842108421, 0xf0001f0001f003e08421084210842108, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab11 : List (ℕ × ℕ × List W) :=
  [(1, 0xff801f0001f07fff94a5294a5294a529, [0xff801f0001f07fff94a5294a5294a529, 0xff80000000007fff1084210842108421, 0xf0001f0001f003e08421084210842108, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab12 : List (ℕ × ℕ × List W) :=
  [(1, 0x7c000000000000000000, [0x7c000000000000000000, 0xff80000000007fff1084210842108421, 0x3e007c004a5294a5294a5294, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab13 : List (ℕ × ℕ × List W) :=
  [(1, 0xff8000003e007fff5ad6b5ad6b5ad6b5, [0xff8000003e007fff5ad6b5ad6b5ad6b5, 0xff80000000007fff1084210842108421, 0x3e007c004a5294a5294a5294, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab14 : List (ℕ × ℕ × List W) :=
  [(1, 0x1fffffff80006318c6318c6318c6, [0x1fffffff80006318c6318c6318c6, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0xff80000000007fff1084210842108421, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab15 : List (ℕ × ℕ × List W) :=
  [(1, 0x7fe0003fff8000ad6b5ad6b5ad6b5a, [0x7fe0003fff8000ad6b5ad6b5ad6b5a, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab16 : List (ℕ × ℕ × List W) :=
  [(1, 0xf80000000000000000000, [0xf80000000000000000000, 0x3fff80002108421084210842, 0x3e007c00f80001084210842108421, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab17 : List (ℕ × ℕ × List W) :=
  [(1, 0x3e007ffff8000318c6318c6318c63, [0x3e007ffff8000318c6318c6318c63, 0x3fff80002108421084210842, 0x3e007c00f80001084210842108421, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab18 : List (ℕ × ℕ × List W) :=
  [(1, 0x2108421084210842, [0x2108421084210842, 0x3fff80002108421084210842, 0xffc00f80000001f2108421084210842, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab19 : List (ℕ × ℕ × List W) :=
  [(3, 0xffc00f83fff801f2108421084210842, [0xffc00f83fff801f2108421084210842, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab20 : List (ℕ × ℕ × List W) :=
  [(2, 0xffc00f83fff801f2108421084210842, [0xffc00f83fff801f2108421084210842, 0x3fff80002108421084210842, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab21 : List (ℕ × ℕ × List W) :=
  [(2, 0xffc00f83fff801f2108421084210842, [0xffc00f83fff801f2108421084210842, 0xffc00f80000001f2108421084210842, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab22 : List (ℕ × ℕ × List W) :=
  [(1, 0xffc00f83fff801f2108421084210842, [0xffc00f83fff801f2108421084210842, 0x3fff80002108421084210842, 0xffc00f80000001f2108421084210842, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab23 : List (ℕ × ℕ × List W) :=
  [(1, 0x1f000000000000000000000, [0x1f000000000000000000000, 0x3fff80002108421084210842, 0xf0001f0001f003e08421084210842108, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab24 : List (ℕ × ℕ × List W) :=
  [(1, 0xf0001f003fff83e0a5294a5294a5294a, [0xf0001f003fff83e0a5294a5294a5294a, 0x3fff80002108421084210842, 0xf0001f0001f003e08421084210842108, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab25 : List (ℕ × ℕ × List W) :=
  [(1, 0x3e0000000000000000000000, [0x3e0000000000000000000000, 0x3fff80002108421084210842, 0x3e007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab26 : List (ℕ × ℕ × List W) :=
  [(1, 0x3ffffc006b5ad6b5ad6b5ad6, [0x3ffffc006b5ad6b5ad6b5ad6, 0x3fff80002108421084210842, 0x3e007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab27 : List (ℕ × ℕ × List W) :=
  [(2, 0x7fffffc0000000ce739ce739ce739c, [0x7fffffc0000000ce739ce739ce739c, 0x1fffc00000004210842108421084, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab28 : List (ℕ × ℕ × List W) :=
  [(1, 0x7fffffc0000000ce739ce739ce739c, [0x7fffffc0000000ce739ce739ce739c, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab29 : List (ℕ × ℕ × List W) :=
  [(1, 0x7c00000000000000000000000, [0x7c00000000000000000000000, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab30 : List (ℕ × ℕ × List W) :=
  [(1, 0x3ffffc00f80005294a5294a5294a5, [0x3ffffc00f80005294a5294a5294a5, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab31 : List (ℕ × ℕ × List W) :=
  [(1, 0xf8000000000000000000000000, [0xf8000000000000000000000000, 0x1fffc00000004210842108421084, 0xffc00f80000001f2108421084210842, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab32 : List (ℕ × ℕ × List W) :=
  [(1, 0xffc1fffc000001f6318c6318c6318c6, [0xffc1fffc000001f6318c6318c6318c6, 0x1fffc00000004210842108421084, 0xffc00f80000001f2108421084210842, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab33 : List (ℕ × ℕ × List W) :=
  [(1, 0x1f00000000000000000000000000, [0x1f00000000000000000000000000, 0x1fffc00000004210842108421084, 0xf0001f0001f003e08421084210842108, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab34 : List (ℕ × ℕ × List W) :=
  [(1, 0xf0001fffc1f003e0c6318c6318c6318c, [0xf0001fffc1f003e0c6318c6318c6318c, 0x1fffc00000004210842108421084, 0xf0001f0001f003e08421084210842108, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab35 : List (ℕ × ℕ × List W) :=
  [(1, 0x4210842108421084, [0x4210842108421084, 0x1fffc00000004210842108421084, 0x3e007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab36 : List (ℕ × ℕ × List W) :=
  [(3, 0x1ffffe007c004a5294a5294a5294, [0x1ffffe007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab37 : List (ℕ × ℕ × List W) :=
  [(2, 0x1ffffe007c004a5294a5294a5294, [0x1ffffe007c004a5294a5294a5294, 0x1fffc00000004210842108421084, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab38 : List (ℕ × ℕ × List W) :=
  [(2, 0x1ffffe007c004a5294a5294a5294, [0x1ffffe007c004a5294a5294a5294, 0x3e007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab39 : List (ℕ × ℕ × List W) :=
  [(1, 0x1ffffe007c004a5294a5294a5294, [0x1ffffe007c004a5294a5294a5294, 0x1fffc00000004210842108421084, 0x3e007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab40 : List (ℕ × ℕ × List W) :=
  [(1, 0x3e000000000000000000000000000, [0x3e000000000000000000000000000, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab41 : List (ℕ × ℕ × List W) :=
  [(1, 0x7fe007c00f80009ce739ce739ce739, [0x7fe007c00f80009ce739ce739ce739, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab42 : List (ℕ × ℕ × List W) :=
  [(1, 0x7c0000000000000000000000000000, [0x7c0000000000000000000000000000, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab43 : List (ℕ × ℕ × List W) :=
  [(1, 0xfffe0f80000001fad6b5ad6b5ad6b5a, [0xfffe0f80000001fad6b5ad6b5ad6b5a, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab44 : List (ℕ × ℕ × List W) :=
  [(1, 0x8421084210842108, [0x8421084210842108, 0x7fe000000000008c6318c6318c6318, 0xf0001f0001f003e08421084210842108, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab45 : List (ℕ × ℕ × List W) :=
  [(3, 0xf07fff0001f003e08c6318c6318c6318, [0xf07fff0001f003e08c6318c6318c6318, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab46 : List (ℕ × ℕ × List W) :=
  [(2, 0xf07fff0001f003e08c6318c6318c6318, [0xf07fff0001f003e08c6318c6318c6318, 0x7fe000000000008c6318c6318c6318, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab47 : List (ℕ × ℕ × List W) :=
  [(2, 0xf07fff0001f003e08c6318c6318c6318, [0xf07fff0001f003e08c6318c6318c6318, 0xf0001f0001f003e08421084210842108, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab48 : List (ℕ × ℕ × List W) :=
  [(1, 0xf07fff0001f003e08c6318c6318c6318, [0xf07fff0001f003e08c6318c6318c6318, 0x7fe000000000008c6318c6318c6318, 0xf0001f0001f003e08421084210842108, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab49 : List (ℕ × ℕ × List W) :=
  [(1, 0x842108421084210, [0x842108421084210, 0x7fe000000000008c6318c6318c6318, 0x3e007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab50 : List (ℕ × ℕ × List W) :=
  [(3, 0x7fe0003e007c00ce739ce739ce739c, [0x7fe0003e007c00ce739ce739ce739c, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab51 : List (ℕ × ℕ × List W) :=
  [(2, 0x7fe0003e007c00ce739ce739ce739c, [0x7fe0003e007c00ce739ce739ce739c, 0x7fe000000000008c6318c6318c6318, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab52 : List (ℕ × ℕ × List W) :=
  [(2, 0x7fe0003e007c00ce739ce739ce739c, [0x7fe0003e007c00ce739ce739ce739c, 0x3e007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab53 : List (ℕ × ℕ × List W) :=
  [(1, 0x7fe0003e007c00ce739ce739ce739c, [0x7fe0003e007c00ce739ce739ce739c, 0x7fe000000000008c6318c6318c6318, 0x3e007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab54 : List (ℕ × ℕ × List W) :=
  [(1, 0xfffe0ffc00f801f318c6318c6318c63, [0xfffe0ffc00f801f318c6318c6318c63, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294])]

def tab55 : List (ℕ × ℕ × List W) :=
  [(1, 0xf003ff07c1ff83e094a5294a5294a529, [0xf003ff07c1ff83e094a5294a5294a529, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294])]

def tab56 : List (ℕ × ℕ × List W) :=
  [(1, 0x3e007fe0ffc005ad6b5ad6b5ad6b5, [0x3e007fe0ffc005ad6b5ad6b5ad6b5, 0x3e007c00f80001084210842108421, 0x3e007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108])]

def tab57 : List (ℕ × ℕ × List W) :=
  [(1, 0xfffc1ff801f003ffa5294a5294a5294a, [0xfffc1ff801f003ffa5294a5294a5294a, 0xffc00f80000001f2108421084210842, 0xf0001f0001f003e08421084210842108, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0x3e007c004a5294a5294a5294])]

def tab58 : List (ℕ × ℕ × List W) :=
  [(1, 0xffc00f83e007c1f6b5ad6b5ad6b5ad6, [0xffc00f83e007c1f6b5ad6b5ad6b5ad6, 0xffc00f80000001f2108421084210842, 0x3e007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xf0001f0001f003e08421084210842108])]

def tab59 : List (ℕ × ℕ × List W) :=
  [(2, 0xf0001f003ff07fe0ce739ce739ce739c, [0xf0001f003ff07fe0ce739ce739ce739c, 0xf0001f0001f003e08421084210842108, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842])]

def tab60 : List (ℕ × ℕ × List W) :=
  [(1, 0xf0001f003ff07fe0ce739ce739ce739c, [0xf0001f003ff07fe0ce739ce739ce739c, 0xf0001f0001f003e08421084210842108, 0x3e007c004a5294a5294a5294, 0xff80000000007fff1084210842108421, 0x3fff80002108421084210842, 0x1fffc00000004210842108421084, 0x7fe000000000008c6318c6318c6318, 0x3e007c00f80001084210842108421, 0xffc00f80000001f2108421084210842])]

def table : List (ℕ × ℕ × List W) := tab0 ++ tab1 ++ tab2 ++ tab3 ++ tab4 ++ tab5 ++ tab6 ++ tab7 ++ tab8 ++ tab9 ++ tab10 ++ tab11 ++ tab12 ++ tab13 ++ tab14 ++ tab15 ++ tab16 ++ tab17 ++ tab18 ++ tab19 ++ tab20 ++ tab21 ++ tab22 ++ tab23 ++ tab24 ++ tab25 ++ tab26 ++ tab27 ++ tab28 ++ tab29 ++ tab30 ++ tab31 ++ tab32 ++ tab33 ++ tab34 ++ tab35 ++ tab36 ++ tab37 ++ tab38 ++ tab39 ++ tab40 ++ tab41 ++ tab42 ++ tab43 ++ tab44 ++ tab45 ++ tab46 ++ tab47 ++ tab48 ++ tab49 ++ tab50 ++ tab51 ++ tab52 ++ tab53 ++ tab54 ++ tab55 ++ tab56 ++ tab57 ++ tab58 ++ tab59 ++ tab60

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf12 : tab12.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf13 : tab13.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

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
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf19 : tab19.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf20 : tab20.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

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
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf24 : tab24.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf25 : tab25.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf26 : tab26.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf27 : tab27.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf28 : tab28.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf29 : tab29.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf30 : tab30.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf31 : tab31.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf32 : tab32.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf33 : tab33.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf34 : tab34.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf35 : tab35.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf36 : tab36.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf37 : tab37.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

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
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf41 : tab41.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf42 : tab42.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf43 : tab43.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf44 : tab44.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf45 : tab45.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf46 : tab46.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

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
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf50 : tab50.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf51 : tab51.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

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
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf55 : tab55.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

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
theorem leaf_all : table.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  simp only [table, List.all_append, leaf0, leaf1, leaf2, leaf3, leaf4, leaf5, leaf6, leaf7, leaf8, leaf9, leaf10, leaf11, leaf12, leaf13, leaf14, leaf15, leaf16, leaf17, leaf18, leaf19, leaf20, leaf21, leaf22, leaf23, leaf24, leaf25, leaf26, leaf27, leaf28, leaf29, leaf30, leaf31, leaf32, leaf33, leaf34, leaf35, leaf36, leaf37, leaf38, leaf39, leaf40, leaf41, leaf42, leaf43, leaf44, leaf45, leaf46, leaf47, leaf48, leaf49, leaf50, leaf51, leaf52, leaf53, leaf54, leaf55, leaf56, leaf57, leaf58, leaf59, leaf60, Bool.and_self]

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

end PEqualNP.Outside.L_meta_8975

theorem PEqualNP.Outside.L_meta_8975 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (14302 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_8975.no_small C hm hs hr
