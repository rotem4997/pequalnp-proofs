import PEqualNP.CircuitLowerBounds.Helpers.Switching.CoreBasic

/-!
# Switching lemma: the encoding

Proof plan (Razborov's encoding of Hastad's switching lemma, in our own words). Let `ρ` have
canonical depth at least `s ≥ 1`. The first live term `T` has starred variables `V`, all of
which the canonical tree queries.

* If `s ≤ |V|`, fix the first `s` variables of `V` to the values `T` requires.
* Otherwise some answer `π` on `V` leaves depth at least `s - |V|`; encode `ρ π` recursively
  (fixing `s - |V|` further variables) and then overwrite `V` by the values `T` requires.

The result `θ` has `s` fewer stars. Beside it we write, for each of the `s` variables, its
position in its term, the answer `π` on it and a bit marking the end of its block: `4 w`
possibilities per variable. Decoding: `T` is still the first live term under `θ` (earlier terms
stay dead, and `T` is satisfied on what was fixed), the code tells which of its variables form
the block and what `π` was, so `ρ π` extended is recovered and the recursion continues.
Injectivity is proved directly by induction on the fuel.
-/

namespace PEqualNP.CircuitLowerBounds.Switching.Core

variable {n : ℕ}

/-- The value the term requires of a variable (read from its first literal on it). -/
def Term.sat (T : Term n) : Fin n → Bool := fun v =>
  match T.find? (fun p => decide (p.1 = v)) with
  | some p => p.2
  | none => false

theorem sat_of_mem {T : Term n} {ρ : Restr n} (hT : ¬ T.Dead ρ) {v : Fin n} {b : Bool}
    (h : (v, b) ∈ T) : T.sat v = b := by
  unfold Term.sat
  cases hf : T.find? (fun p => decide (p.1 = v)) with
  | none =>
    have := List.find?_eq_none.1 hf (v, b) h
    simp at this
  | some p =>
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [decide_eq_true_eq] at hp
    show p.2 = b
    by_contra hne
    apply hT
    refine ⟨(v, b), h, Or.inr ?_⟩
    have : p = (v, !b) := by
      refine Prod.ext hp ?_
      show p.2 = !b
      cases hb : p.2 <;> cases b <;> simp_all
    rw [← this]; exact hm

/-- The position of the first literal of `T` on the variable `v`. -/
def pos (T : Term n) (v : Fin n) : ℕ := T.findIdx (fun p => decide (p.1 = v))

theorem pos_lt {T : Term n} {v : Fin n} (h : ∃ b, (v, b) ∈ T) : pos T v < T.length := by
  obtain ⟨b, hb⟩ := h
  exact List.findIdx_lt_length_of_exists ⟨(v, b), hb, by simp⟩

theorem getElem?_pos {T : Term n} {v : Fin n} (h : ∃ b, (v, b) ∈ T) :
    (T[pos T v]?).map Prod.fst = some v := by
  have hlt := pos_lt h
  have := List.findIdx_getElem (w := hlt)
  simp only [decide_eq_true_eq] at this
  rw [List.getElem?_eq_getElem hlt]
  exact congrArg some this

/-- The code of one block of queried variables: position in the term, the answer, and a bit
marking the last variable of the block. -/
def codeBlock (T : Term n) (π : Fin n → Bool) : List (Fin n) → List (ℕ × Bool × Bool)
  | [] => []
  | [v] => [(pos T v, π v, true)]
  | v :: v' :: V => (pos T v, π v, false) :: codeBlock T π (v' :: V)

theorem codeBlock_length (T : Term n) (π : Fin n → Bool) :
    ∀ V : List (Fin n), (codeBlock T π V).length = V.length
  | [] => rfl
  | [_] => rfl
  | _ :: v' :: V => by
    simp only [codeBlock, List.length_cons, codeBlock_length T π (v' :: V)]

theorem codeBlock_fst_lt (T : Term n) (π : Fin n → Bool) :
    ∀ V : List (Fin n), (∀ v ∈ V, ∃ b, (v, b) ∈ T) → ∀ e ∈ codeBlock T π V, e.1 < T.length
  | [], _, e, he => by simp [codeBlock] at he
  | [v], hV, e, he => by
    simp only [codeBlock, List.mem_singleton] at he
    subst he
    exact pos_lt (hV v (by simp))
  | v :: v' :: V, hV, e, he => by
    simp only [codeBlock, List.mem_cons] at he
    rcases he with rfl | he
    · exact pos_lt (hV v (by simp))
    · exact codeBlock_fst_lt T π (v' :: V) (fun u hu => hV u (by simp [List.mem_cons] at hu ⊢; tauto)) e
        (by simpa [List.mem_cons] using he)

theorem codeBlock_inj (T : Term n) (π π₂ : Fin n → Bool) :
    ∀ (V V₂ : List (Fin n)) (c c₂ : List (ℕ × Bool × Bool)), V ≠ [] → V₂ ≠ [] →
      codeBlock T π V ++ c = codeBlock T π₂ V₂ ++ c₂ →
      V.map (fun v => (pos T v, π v)) = V₂.map (fun v => (pos T v, π₂ v)) ∧ c = c₂
  | [], _, _, _, h, _, _ => absurd rfl h
  | _ :: _, [], _, _, _, h, _ => absurd rfl h
  | [v], [v₂], c, c₂, _, _, h => by
    simp only [codeBlock, List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq,
      and_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp [h1, h2, h3]
  | [v], v₂ :: v₂' :: W, c, c₂, _, _, h => by
    simp [codeBlock] at h
  | v :: v' :: V, [v₂], c, c₂, _, _, h => by
    simp [codeBlock] at h
  | v :: v' :: V, v₂ :: v₂' :: W, c, c₂, _, _, h => by
    simp only [codeBlock, List.cons_append, List.cons.injEq, Prod.mk.injEq, and_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have ih := codeBlock_inj T π π₂ (v' :: V) (v₂' :: W) c c₂ (by simp) (by simp) h3
    refine ⟨?_, ih.2⟩
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq]
    exact ⟨⟨h1, h2⟩, by simpa using ih.1⟩

theorem eq_of_map_pos {T : Term n} {π π₂ : Fin n → Bool} :
    ∀ {V V₂ : List (Fin n)}, (∀ v ∈ V, ∃ b, (v, b) ∈ T) → (∀ v ∈ V₂, ∃ b, (v, b) ∈ T) →
      V.map (fun v => (pos T v, π v)) = V₂.map (fun v => (pos T v, π₂ v)) →
      V = V₂ ∧ ∀ v ∈ V, π v = π₂ v
  | [], [], _, _, _ => by simp
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | v :: V, v₂ :: V₂, hV, hV₂, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hv : v = v₂ := by
      have a := getElem?_pos (hV v (by simp))
      have b := getElem?_pos (hV₂ v₂ (by simp))
      rw [h1] at a
      rw [a] at b
      exact Option.some.inj b
    subst hv
    have ih := eq_of_map_pos (fun u hu => hV u (by simp [hu])) (fun u hu => hV₂ u (by simp [hu])) h3
    refine ⟨by rw [ih.1], ?_⟩
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact h2
    · exact ih.2 u hu

open Classical in
/-- An answer on `V` that keeps the canonical depth at least `m`, if there is one. -/
noncomputable def pick (k m : ℕ) (F : DNF n) (ρ : Restr n) (V : List (Fin n)) : Fin n → Bool :=
  if h : ∃ π : Fin n → Bool, m ≤ cdtAux k F (ext ρ V π) then h.choose else fun _ => false

theorem pick_spec {k m : ℕ} {F : DNF n} {ρ : Restr n} {V : List (Fin n)}
    (h : m ≤ Finset.univ.sup fun π : Fin n → Bool => cdtAux k F (ext ρ V π)) :
    m ≤ cdtAux k F (ext ρ V (pick k m F ρ V)) := by
  obtain ⟨π, -, hπ⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun π : Fin n → Bool => cdtAux k F (ext ρ V π))
  have hex : ∃ π : Fin n → Bool, m ≤ cdtAux k F (ext ρ V π) := ⟨π, hπ ▸ h⟩
  unfold pick
  rw [dif_pos hex]
  exact hex.choose_spec

/-- The encoding: the restriction with `s` more variables fixed, and the code. -/
noncomputable def enc : ℕ → ℕ → DNF n → Restr n → Restr n × List (ℕ × Bool × Bool)
  | 0, _, _, ρ => (ρ, [])
  | k + 1, s, F, ρ =>
    match firstLive F ρ with
    | none => (ρ, [])
    | some T =>
      if s ≤ (T.free ρ).length then
        (ext ρ ((T.free ρ).take s) T.sat, codeBlock T (fun _ => false) ((T.free ρ).take s))
      else
        (ext (enc k (s - (T.free ρ).length) F
            (ext ρ (T.free ρ) (pick k (s - (T.free ρ).length) F ρ (T.free ρ)))).1
          (T.free ρ) T.sat,
         codeBlock T (pick k (s - (T.free ρ).length) F ρ (T.free ρ)) (T.free ρ) ++
          (enc k (s - (T.free ρ).length) F
            (ext ρ (T.free ρ) (pick k (s - (T.free ρ).length) F ρ (T.free ρ)))).2)

theorem enc_zero (s : ℕ) (F : DNF n) (ρ : Restr n) : enc 0 s F ρ = (ρ, []) := rfl

theorem enc_succ_none {k s : ℕ} {F : DNF n} {ρ : Restr n} (h : firstLive F ρ = none) :
    enc (k + 1) s F ρ = (ρ, []) := by
  simp only [enc, h]

theorem enc_succ_some {k s : ℕ} {F : DNF n} {ρ : Restr n} {T : Term n}
    (h : firstLive F ρ = some T) :
    enc (k + 1) s F ρ =
      if s ≤ (T.free ρ).length then
        (ext ρ ((T.free ρ).take s) T.sat, codeBlock T (fun _ => false) ((T.free ρ).take s))
      else
        (ext (enc k (s - (T.free ρ).length) F
            (ext ρ (T.free ρ) (pick k (s - (T.free ρ).length) F ρ (T.free ρ)))).1
          (T.free ρ) T.sat,
         codeBlock T (pick k (s - (T.free ρ).length) F ρ (T.free ρ)) (T.free ρ) ++
          (enc k (s - (T.free ρ).length) F
            (ext ρ (T.free ρ) (pick k (s - (T.free ρ).length) F ρ (T.free ρ)))).2) := by
  simp only [enc, h]

/-- Depth at least `s ≥ 1` with positive fuel: there is a first live term with starred
variables, and the depth unfolds. -/
theorem bad_unfold {k s : ℕ} {F : DNF n} {ρ : Restr n} (hs : 1 ≤ s)
    (hb : s ≤ cdtAux (k + 1) F ρ) :
    ∃ T, firstLive F ρ = some T ∧ T.free ρ ≠ [] ∧
      s ≤ (T.free ρ).length +
        Finset.univ.sup fun π : Fin n → Bool => cdtAux k F (ext ρ (T.free ρ) π) := by
  cases hf : firstLive F ρ with
  | none => rw [cdtAux_succ_none hf] at hb; omega
  | some T =>
    rw [cdtAux_succ_some hf] at hb
    by_cases hV : T.free ρ = []
    · rw [if_pos hV] at hb; omega
    · rw [if_neg hV] at hb; exact ⟨T, rfl, hV, hb⟩

theorem free_sub {T : Term n} {ρ : Restr n} : ∀ v ∈ T.free ρ, ∃ b, (v, b) ∈ T :=
  fun _ hv => (mem_free.1 hv).1

/-- The encoded restriction extends the given one. -/
theorem enc_extends : ∀ (k s : ℕ) (F : DNF n) (ρ : Restr n) (v : Fin n) (b : Bool),
    ρ v = some b → (enc k s F ρ).1 v = some b
  | 0, _, _, _, _, _, h => h
  | k + 1, s, F, ρ, v, b, h => by
    cases hf : firstLive F ρ with
    | none => rw [enc_succ_none hf]; exact h
    | some T =>
      rw [enc_succ_some hf]
      have hv : v ∉ T.free ρ := fun hv => by rw [free_star hv] at h; cases h
      split_ifs with hle
      · show ext ρ ((T.free ρ).take s) T.sat v = some b
        rw [ext_of_not_mem (fun hv' => hv (List.mem_of_mem_take hv'))]; exact h
      · show ext _ (T.free ρ) T.sat v = some b
        rw [ext_of_not_mem hv]
        exact enc_extends k _ F _ v b (by rw [ext_of_not_mem hv]; exact h)

theorem enc_s_zero (k : ℕ) (F : DNF n) (ρ : Restr n) : enc k 0 F ρ = (ρ, []) := by
  cases k with
  | zero => rfl
  | succ k =>
    cases hf : firstLive F ρ with
    | none => exact enc_succ_none hf
    | some T => rw [enc_succ_some hf]; simp [ext_nil, codeBlock]

/-- The encoded restriction has exactly `s` fewer stars. -/
theorem enc_stars : ∀ (k s : ℕ) (F : DNF n) (ρ : Restr n), s ≤ cdtAux k F ρ →
    stars (enc k s F ρ).1 + s = stars ρ := by
  intro k
  induction k with
  | zero =>
    intro s F ρ hb
    rw [cdtAux_zero] at hb
    have : s = 0 := by omega
    subst this; rfl
  | succ k ih =>
    intro s F ρ hb
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rw [enc_s_zero]; rfl
    · obtain ⟨T, hf, hV, hb'⟩ := bad_unfold hs hb
      rw [enc_succ_some hf]
      split_ifs with hle
      · have := stars_ext (ρ := ρ) T.sat ((free_nodup T ρ).sublist (List.take_sublist s _))
          (fun v hv => free_star (List.mem_of_mem_take hv))
        rw [List.length_take, Nat.min_eq_left hle] at this
        exact this
      · have hp := pick_spec (k := k) (m := s - (T.free ρ).length) (F := F) (ρ := ρ)
          (V := T.free ρ) (by omega)
        have h1 := ih _ F _ hp
        have h2 := stars_ext (ρ := ρ) (pick k (s - (T.free ρ).length) F ρ (T.free ρ))
          (free_nodup T ρ) (fun v hv => free_star hv)
        have h3 := stars_ext_fixed (ρ := (enc k (s - (T.free ρ).length) F
            (ext ρ (T.free ρ) (pick k (s - (T.free ρ).length) F ρ (T.free ρ)))).1)
          (V := T.free ρ) T.sat (fun v hv => by
            rw [enc_extends k _ F _ v _ (ext_of_mem hv)]; simp)
        show stars (ext _ (T.free ρ) T.sat) + s = stars ρ
        rw [h3]; omega

/-- The code has length `s`. -/
theorem enc_code_length : ∀ (k s : ℕ) (F : DNF n) (ρ : Restr n), s ≤ cdtAux k F ρ →
    (enc k s F ρ).2.length = s := by
  intro k
  induction k with
  | zero =>
    intro s F ρ hb
    rw [cdtAux_zero] at hb
    have : s = 0 := by omega
    subst this; rfl
  | succ k ih =>
    intro s F ρ hb
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rw [enc_s_zero]; rfl
    · obtain ⟨T, hf, hV, hb'⟩ := bad_unfold hs hb
      rw [enc_succ_some hf]
      split_ifs with hle
      · show (codeBlock T _ ((T.free ρ).take s)).length = s
        rw [codeBlock_length, List.length_take, Nat.min_eq_left hle]
      · have hp := pick_spec (k := k) (m := s - (T.free ρ).length) (F := F) (ρ := ρ)
          (V := T.free ρ) (by omega)
        have h1 := ih _ F _ hp
        show (codeBlock T _ (T.free ρ) ++ _).length = s
        rw [List.length_append, codeBlock_length, h1]; omega

/-- Every position in the code is below the width. -/
theorem enc_code_lt {w : ℕ} : ∀ (k s : ℕ) (F : DNF n) (ρ : Restr n),
    (∀ T ∈ F, T.length ≤ w) → ∀ e ∈ (enc k s F ρ).2, e.1 < w
  | 0, _, _, _, _, e, he => by simp [enc_zero] at he
  | k + 1, s, F, ρ, hw, e, he => by
    cases hf : firstLive F ρ with
    | none => rw [enc_succ_none hf] at he; simp at he
    | some T =>
      rw [enc_succ_some hf] at he
      have hT := hw T (firstLive_mem hf)
      split_ifs at he with hle
      · exact lt_of_lt_of_le (codeBlock_fst_lt T _ _
          (fun v hv => free_sub v (List.mem_of_mem_take hv)) e he) hT
      · rcases List.mem_append.1 he with he | he
        · exact lt_of_lt_of_le (codeBlock_fst_lt T _ _ free_sub e he) hT
        · exact enc_code_lt k _ F _ hw e he

/-- The first live term is still the first live term after encoding. -/
theorem enc_firstLive {k s : ℕ} {F : DNF n} {ρ : Restr n} {T : Term n}
    (hf : firstLive F ρ = some T) : firstLive F (enc (k + 1) s F ρ).1 = some T := by
  have hnd := firstLive_not_dead hf
  refine firstLive_of_mono hf (fun T' => dead_mono (enc_extends (k + 1) s F ρ)) ?_
  rintro ⟨p, hp, h1 | h2⟩
  · cases hρ : ρ p.1 with
    | some c =>
      rw [enc_extends (k + 1) s F ρ p.1 c hρ] at h1
      exact hnd ⟨p, hp, Or.inl (by rw [hρ]; exact h1)⟩
    | none =>
      have hmem : p.1 ∈ T.free ρ := mem_free.2 ⟨⟨p.2, hp⟩, hρ⟩
      have hsat : T.sat p.1 = p.2 := sat_of_mem hnd (v := p.1) (b := p.2) hp
      rw [enc_succ_some hf] at h1
      split_ifs at h1 with hle
      · change ext ρ ((T.free ρ).take s) T.sat p.1 = some (!p.2) at h1
        by_cases hv : p.1 ∈ (T.free ρ).take s
        · rw [ext_of_mem hv, hsat] at h1
          cases hb : p.2 <;> simp [hb] at h1
        · rw [ext_of_not_mem hv, hρ] at h1; cases h1
      · change ext _ (T.free ρ) T.sat p.1 = some (!p.2) at h1
        rw [ext_of_mem hmem, hsat] at h1
        cases hb : p.2 <;> simp [hb] at h1
  · exact hnd ⟨p, hp, Or.inr h2⟩

/-- The encoding is injective on the restrictions of depth at least `s ≥ 1`. -/
theorem enc_inj : ∀ (k s : ℕ) (F : DNF n) (ρ ρ₂ : Restr n), 1 ≤ s → s ≤ cdtAux k F ρ →
    s ≤ cdtAux k F ρ₂ → enc k s F ρ = enc k s F ρ₂ → ρ = ρ₂ := by
  intro k
  induction k with
  | zero =>
    intro s F ρ ρ₂ hs hb _ _
    rw [cdtAux_zero] at hb; omega
  | succ k ih =>
    intro s F ρ ρ₂ hs hb hb₂ he
    obtain ⟨T, hf, hV, hb'⟩ := bad_unfold hs hb
    obtain ⟨T₂, hf₂, hV₂, hb₂'⟩ := bad_unfold hs hb₂
    have hTT : T = T₂ := by
      have a := enc_firstLive (k := k) (s := s) hf
      have b := enc_firstLive (k := k) (s := s) hf₂
      rw [he] at a
      rw [a] at b
      exact Option.some.inj b
    subst hTT
    rw [enc_succ_some hf, enc_succ_some hf₂] at he
    by_cases hle : s ≤ (T.free ρ).length <;> by_cases hle₂ : s ≤ (T.free ρ₂).length
    · rw [if_pos hle, if_pos hle₂] at he
      obtain ⟨heθ, hec⟩ := Prod.mk.inj he
      have hne : (T.free ρ).take s ≠ [] := by
        intro h0
        have := congrArg List.length h0
        rw [List.length_take, Nat.min_eq_left hle] at this
        simp at this; omega
      have hne₂ : (T.free ρ₂).take s ≠ [] := by
        intro h0
        have := congrArg List.length h0
        rw [List.length_take, Nat.min_eq_left hle₂] at this
        simp at this; omega
      have h1 := codeBlock_inj T _ _ _ _ [] [] hne hne₂ (by simpa using hec)
      have h2 := eq_of_map_pos (fun v hv => free_sub v (List.mem_of_mem_take hv))
        (fun v hv => free_sub v (List.mem_of_mem_take hv)) h1.1
      funext v
      by_cases hv : v ∈ (T.free ρ).take s
      · have hv₂ : v ∈ (T.free ρ₂).take s := h2.1 ▸ hv
        rw [free_star (List.mem_of_mem_take hv), free_star (List.mem_of_mem_take hv₂)]
      · have hv₂ : v ∉ (T.free ρ₂).take s := fun h => hv (h2.1 ▸ h)
        have := congrFun heθ v
        rwa [ext_of_not_mem hv, ext_of_not_mem hv₂] at this
    · rw [if_pos hle, if_neg hle₂] at he
      obtain ⟨heθ, hec⟩ := Prod.mk.inj he
      have hne : (T.free ρ).take s ≠ [] := by
        intro h0
        have := congrArg List.length h0
        rw [List.length_take, Nat.min_eq_left hle] at this
        simp at this; omega
      have h1 := codeBlock_inj T _ _ _ _ [] _ hne hV₂ (by simpa using hec)
      have := congrArg List.length h1.1
      rw [List.length_map, List.length_map, List.length_take, Nat.min_eq_left hle] at this
      omega
    · rw [if_neg hle, if_pos hle₂] at he
      obtain ⟨heθ, hec⟩ := Prod.mk.inj he
      have hne₂ : (T.free ρ₂).take s ≠ [] := by
        intro h0
        have := congrArg List.length h0
        rw [List.length_take, Nat.min_eq_left hle₂] at this
        simp at this; omega
      have h1 := codeBlock_inj T _ _ _ _ _ [] hV hne₂ (by simpa using hec)
      have := congrArg List.length h1.1
      rw [List.length_map, List.length_map, List.length_take, Nat.min_eq_left hle₂] at this
      omega
    · rw [if_neg hle, if_neg hle₂] at he
      obtain ⟨heθ, hec⟩ := Prod.mk.inj he
      have h1 := codeBlock_inj T _ _ _ _ _ _ hV hV₂ hec
      have h2 := eq_of_map_pos free_sub free_sub h1.1
      have hVV : T.free ρ₂ = T.free ρ := h2.1.symm
      rw [hVV] at heθ h1 hle₂ hb₂'
      have hπ : ext ρ₂ (T.free ρ) (pick k (s - (T.free ρ).length) F ρ₂ (T.free ρ))
          = ext ρ₂ (T.free ρ) (pick k (s - (T.free ρ).length) F ρ (T.free ρ)) := by
        apply ext_congr
        intro v hv
        have := h2.2 v hv
        rw [hVV] at this
        exact this.symm
      have hp := pick_spec (k := k) (m := s - (T.free ρ).length) (F := F) (ρ := ρ)
        (V := T.free ρ) (by omega)
      have hp₂ := pick_spec (k := k) (m := s - (T.free ρ).length) (F := F) (ρ := ρ₂)
        (V := T.free ρ) (by omega)
      rw [hπ] at hp₂ heθ
      rw [hπ] at h1
      have hr : enc k (s - (T.free ρ).length) F
            (ext ρ (T.free ρ) (pick k (s - (T.free ρ).length) F ρ (T.free ρ)))
          = enc k (s - (T.free ρ).length) F
            (ext ρ₂ (T.free ρ) (pick k (s - (T.free ρ).length) F ρ (T.free ρ))) := by
        refine Prod.ext ?_ h1.2
        funext v
        by_cases hv : v ∈ T.free ρ
        · rw [enc_extends k _ F _ v _ (ext_of_mem hv), enc_extends k _ F _ v _ (ext_of_mem hv)]
        · have := congrFun heθ v
          rwa [ext_of_not_mem hv, ext_of_not_mem hv] at this
      have hee := ih _ F _ _ (by omega) hp hp₂ hr
      funext v
      by_cases hv : v ∈ T.free ρ
      · have hv₂ : v ∈ T.free ρ₂ := by rw [hVV]; exact hv
        rw [free_star hv, free_star hv₂]
      · have := congrFun hee v
        rwa [ext_of_not_mem hv, ext_of_not_mem hv] at this

end PEqualNP.CircuitLowerBounds.Switching.Core
