import PEqualNP.Library.Evasion.Plan
import PEqualNP.Library.L002
import PEqualNP.Library.Machines.ComposeTime

/-!
# Evasion chain: the rung, reduced to named pieces

Plan module of the slowdown side. `rung_of_pieces` proves `StmtRung` from the pieces below and
`StmtNoScaledCollapse`; every machine fact is a named `Prop`. Paper derivation:
`notes/evasion-build/f5.md`.

Exponent bookkeeping. For `L` in `DTIMEO (2^(q v^3 s m))`, pad to length `N = v^3 s m + 1`
(`StmtPadExp` at scale `v^3 s`). The padded language is in `DTIMEO (2^(q N))`; `FP3` puts it in
`SigmaV 3 (K 2^(p N) + K)`; the slowdown `StmtSlow3` at a constructible `g` with
`g n ^ v ≤ A n^u + A` (`StmtRootDom`) gives time `y3 = g (C g (C g (C X + C) + C) + C)`,
`X = K 2^(p N) + K`, and `y3 ^ (v^3) ≤ D (2^(p N))^(u^3) = D 2^(p u^3) (2^(p u^3 s m))^(v^3)`.
Taking the `v^3`-th root is exact: `y3 ≤ D' 2^(p u^3 s m)`.
-/

namespace PEqualNP.Library

namespace Evasion

/-! ## The pieces -/

/-- The slowdown at three alternations for an abstract constructible collapse bound `g`.
The constant `C` depends on the language (it absorbs the verifier's constant). -/
def StmtSlow3 : Prop :=
  ∀ g : ℕ → ℕ, Constructible g → (∀ a : ℕ, NLIN a ⊆ DTIMEO g) →
    ∀ T : ℕ → ℕ, Constructible T → ∀ L ∈ SigmaV 3 T, ∃ C : ℕ,
      L ∈ DTIMEO (fun n => g (C * g (C * g (C * T n + C) + C) + C))

/-- A constructible bound above the rounded root `ceil (n^(u/v))`, of the same order. The rounded
root itself is one choice (`A = 2^v`); a dominating step function `2^(u k)`, `k` least with
`n ≤ 2^(v k)`, is another (`A = 2^(u v)`). -/
def StmtRootDom : Prop :=
  ∀ u v : ℕ, 1 ≤ v → v ≤ u → ∃ g : ℕ → ℕ, Constructible g ∧
    (∀ n, rootUp v (n ^ u) ≤ g n) ∧ ∃ A : ℕ, ∀ n, g n ^ v ≤ A * n ^ u + A

/-- Padding at scale `s` (note 210, 3.4 and 3.5 (a), (c)): the padded language is in
`DTIMEO (2^(q N))`, and any bound `t` for it gives `t (s m + 1)` plus the cost of the pad. -/
def StmtPadExp : Prop :=
  ∀ s q : ℕ, 1 ≤ s → 1 ≤ q → ∀ L ∈ DTIMEO (fun m => 2 ^ (q * s * m)),
    ∃ L' : Language Bool, L' ∈ DTIMEO (fun N => 2 ^ (q * N)) ∧
      ∀ t : ℕ → ℕ, Monotone t → L' ∈ DTIMEO t → L ∈ DTIMEO (fun m => t (s * m + 1) + 2 ^ m)

/-! ## Pure lemmas -/

theorem dtimeo_O {t t' : ℕ → ℕ} (A : ℕ) (h : ∀ n, t n ≤ A * t' n + A) :
    DTIMEO t ⊆ DTIMEO t' := by
  rintro L ⟨K, hK⟩
  refine ⟨K * A + K, L002 _ _ (fun n => ?_) hK⟩
  have := h n
  calc K * t n + K ≤ K * (A * t' n + A) + K := by gcongr
    _ = (K * A) * t' n + (K * A + K) := by ring
    _ ≤ (K * A + K) * t' n + (K * A + K) := by gcongr; omega

/-- One level of the root bound. -/
theorem root_step {g : ℕ → ℕ} {u v A : ℕ} (hgb : ∀ n, g n ^ v ≤ A * n ^ u + A)
    (C : ℕ) {y : ℕ} (hy : 1 ≤ y) :
    g (C * y + C) ^ v ≤ (A * (2 * C) ^ u + A) * y ^ u := by
  have h1 : C * y + C ≤ 2 * C * y := by nlinarith
  have h2 : (C * y + C) ^ u ≤ (2 * C) ^ u * y ^ u := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left h1 u
  have h3 : 1 ≤ y ^ u := Nat.one_le_pow _ _ hy
  calc g (C * y + C) ^ v ≤ A * (C * y + C) ^ u + A := hgb _
    _ ≤ A * ((2 * C) ^ u * y ^ u) + A * y ^ u := by gcongr; nlinarith
    _ = (A * (2 * C) ^ u + A) * y ^ u := by ring

/-- Chaining two levels. -/
theorem root_chain {a b W E F u v V U : ℕ} (ha : a ^ v ≤ E * b ^ u) (hb : b ^ V ≤ F * W ^ U) :
    a ^ (v * V) ≤ E ^ V * F ^ u * W ^ (U * u) := by
  calc a ^ (v * V) = (a ^ v) ^ V := by rw [pow_mul]
    _ ≤ (E * b ^ u) ^ V := Nat.pow_le_pow_left ha V
    _ = E ^ V * (b ^ V) ^ u := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm u V]
    _ ≤ E ^ V * (F * W ^ U) ^ u := by gcongr
    _ = E ^ V * F ^ u * W ^ (U * u) := by rw [mul_pow, ← pow_mul]; ring

theorem g3_mono {g : ℕ → ℕ} (hg : Monotone g) {C C' X X' : ℕ} (hC : C ≤ C') (hX : X ≤ X') :
    g (C * g (C * g (C * X + C) + C) + C) ≤ g (C' * g (C' * g (C' * X' + C') + C') + C') := by
  have h1 : g (C * X + C) ≤ g (C' * X' + C') :=
    hg (Nat.add_le_add (Nat.mul_le_mul hC hX) hC)
  have h2 : g (C * g (C * X + C) + C) ≤ g (C' * g (C' * X' + C') + C') :=
    hg (Nat.add_le_add (Nat.mul_le_mul hC h1) hC)
  exact hg (Nat.add_le_add (Nat.mul_le_mul hC h2) hC)

/-- The triple bound: `y3 ^ (v^3) ≤ D * W ^ (u^3)` for `y0 ≤ 2 K W`, `1 ≤ y0`. -/
theorem root_triple {g : ℕ → ℕ} {u v A : ℕ} (hgb : ∀ n, g n ^ v ≤ A * n ^ u + A)
    (hg : ∀ n, n ≤ g n) {C K : ℕ} (hC : 1 ≤ C) :
    ∃ D : ℕ, ∀ X W : ℕ, 1 ≤ X → X ≤ 2 * K * W →
      g (C * g (C * g (C * X + C) + C) + C) ^ (v ^ 3) ≤ D * W ^ (u ^ 3) := by
  set E := A * (2 * C) ^ u + A
  refine ⟨E ^ (v ^ 2) * (E ^ v * (E * (2 * K) ^ u) ^ u) ^ u, fun X W hX hXW => ?_⟩
  have hy1 : 1 ≤ g (C * X + C) := le_trans (by nlinarith) (hg _)
  have hy2 : 1 ≤ g (C * g (C * X + C) + C) := le_trans (by nlinarith) (hg _)
  have s1 := root_step hgb C hX
  have s2 := root_step hgb C hy1
  have s3 := root_step hgb C hy2
  have b0 : X ^ 1 ≤ (2 * K) * W ^ 1 := by simpa using hXW
  have c1 := root_chain s1 b0
  have c2 := root_chain s2 c1
  have c3 := root_chain s3 c2
  have e1 : v * (v * (v * 1)) = v ^ 3 := by ring
  have e2 : 1 * u * u * u = u ^ 3 := by ring
  rw [e1, e2] at c3
  calc _ ≤ _ := c3
    _ = _ := by ring

/-! ## The rung -/

theorem rung_of_pieces (hSlow : StmtSlow3) (hRoot : StmtRootDom) (hPad : StmtPadExp)
    (hCLK : StmtCLK) (hNSC : StmtNoScaledCollapse) : StmtRung := by
  intro p q u v hp hv hvu hpq hFP hColl
  have hu : 1 ≤ u := le_trans hv hvu
  obtain ⟨g, hgC, hgr, A, hgb⟩ := hRoot u v hv hvu
  have hgmono : Monotone g := hgC.1
  have hgid : ∀ n, n ≤ g n := hgC.2.1
  have hcoll : ∀ a, NLIN a ⊆ DTIMEO g := fun a =>
    (hColl a).trans (dtimeo_O 1 (fun n => by have := hgr n; omega))
  have hq : 1 ≤ q := by
    have : 1 ≤ q * v ^ 3 := le_trans (by
      have := Nat.one_le_pow 3 u hu; nlinarith) hpq
    rcases Nat.eq_zero_or_pos q with h | h
    · simp [h] at this
    · exact h
  have hv3 : 1 ≤ v ^ 3 := Nat.one_le_pow _ _ hv
  refine hNSC (p * u ^ 3) (q * v ^ 3) (by have := Nat.one_le_pow 3 u hu; nlinarith) hpq ?_
  intro s hs L hL
  have hs' : 1 ≤ v ^ 3 * s := by nlinarith
  have hL2 : L ∈ DTIMEO (fun m => 2 ^ (q * (v ^ 3 * s) * m)) := by
    have e : (fun m => 2 ^ (q * v ^ 3 * s * m)) = (fun m => 2 ^ (q * (v ^ 3 * s) * m)) := by
      funext m; ring_nf
    rw [← e]; exact hL
  obtain ⟨L', hL', hback⟩ := hPad (v ^ 3 * s) q hs' hq L hL2
  obtain ⟨K, hK1, hKL⟩ := hFP L' hL'
  have hT := hCLK p K hp hK1
  obtain ⟨C0, hC0⟩ := hSlow g hgC hcoll _ hT L' hKL
  set C := C0 + 1 with hCdef
  have hC : 1 ≤ C := by omega
  set Ψ : ℕ → ℕ := fun N => g (C * g (C * g (C * (K * 2 ^ (p * N) + K) + C) + C) + C) with hΨ
  have hΨmono : Monotone Ψ := by
    intro a b hab
    exact g3_mono hgmono le_rfl (Nat.add_le_add_right (Nat.mul_le_mul_left K
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left p hab))) K)
  have hL'Ψ : L' ∈ DTIMEO Ψ := by
    refine dtimeo_O 1 (fun N => ?_) hC0
    have : g (C0 * g (C0 * g (C0 * (K * 2 ^ (p * N) + K) + C0) + C0) + C0) ≤ Ψ N := by
      exact g3_mono hgmono (by omega) le_rfl
    omega
  have hLΨ := hback Ψ hΨmono hL'Ψ
  obtain ⟨D, hD⟩ := root_triple (K := K) hgb hgid hC
  refine dtimeo_O (D * 2 ^ (p * u ^ 3) + 2) (fun m => ?_) hLΨ
  -- the arithmetic at length `N = v^3 s m + 1`
  set N := v ^ 3 * s * m + 1
  set Z := 2 ^ (p * u ^ 3 * s * m)
  have hW1 : 1 ≤ 2 ^ (p * N) := Nat.one_le_two_pow
  have hX1 : 1 ≤ K * 2 ^ (p * N) + K := by omega
  have hXW : K * 2 ^ (p * N) + K ≤ 2 * K * 2 ^ (p * N) := by nlinarith
  have hy := hD _ _ hX1 hXW
  have hWu : (2 ^ (p * N)) ^ (u ^ 3) = 2 ^ (p * u ^ 3) * Z ^ (v ^ 3) := by
    simp only [Z, N, ← pow_mul, ← pow_add]; congr 1; ring
  have hD1 : 1 ≤ D * 2 ^ (p * u ^ 3) + 1 := by omega
  have hroot : Ψ N ≤ (D * 2 ^ (p * u ^ 3) + 1) * Z := by
    have h3 : 0 < v ^ 3 := hv3
    rw [← Nat.pow_le_pow_iff_left (n := v ^ 3) (by omega)]
    calc Ψ N ^ (v ^ 3) ≤ D * (2 ^ (p * N)) ^ (u ^ 3) := hy
      _ = (D * 2 ^ (p * u ^ 3)) * Z ^ (v ^ 3) := by rw [hWu]; ring
      _ ≤ (D * 2 ^ (p * u ^ 3) + 1) ^ (v ^ 3) * Z ^ (v ^ 3) := by
          gcongr
          calc D * 2 ^ (p * u ^ 3) ≤ D * 2 ^ (p * u ^ 3) + 1 := by omega
            _ = (D * 2 ^ (p * u ^ 3) + 1) ^ 1 := (pow_one _).symm
            _ ≤ _ := Nat.pow_le_pow_right hD1 hv3
      _ = _ := (mul_pow _ _ _).symm
  have hm : 2 ^ m ≤ Z := by
    apply Nat.pow_le_pow_right (by norm_num)
    have : 1 ≤ p * u ^ 3 * s := by
      have := Nat.one_le_pow 3 u hu; have : 1 ≤ p * u ^ 3 := by nlinarith
      nlinarith
    nlinarith
  show Ψ (v ^ 3 * s * m + 1) + 2 ^ m ≤
    (D * 2 ^ (p * u ^ 3) + 2) * 2 ^ (p * u ^ 3 * s * m) + (D * 2 ^ (p * u ^ 3) + 2)
  have : (2 : ℕ) ^ (p * u ^ 3 * s * m) = Z := rfl
  rw [this]
  have : Ψ (v ^ 3 * s * m + 1) = Ψ N := rfl
  rw [this]
  nlinarith [hroot, hm]


/-! ## The slowdown, split (route note 209, with `n ^ c` replaced by an abstract `g`)

Proof-internal definitions: the block length read off a padded input, the rest of the input,
the witness cut to a given length, and the level bound of the induction. -/

/-- The number of leading `true`s. -/
def lead (s : List Bool) : ℕ := (s.takeWhile id).length

/-- What follows the leading `true`s and the first `false`. -/
def body (s : List Bool) : List Bool := (s.dropWhile id).drop 1

/-- `w` cut or filled with `false` to length exactly `k`. -/
def fixLen (k : ℕ) (w : List Bool) : List Bool := (w ++ List.replicate k false).take k

/-- The level bound: `lvl g C 0 n = n`, `lvl g C (j+1) n = g (C * lvl g C j (C * n + C) + C)`. -/
def lvl (g : ℕ → ℕ) (C : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | j + 1, n => g (C * lvl g C j (C * n + C) + C)

/-- M2 of note 209 at pair inputs: negating a decider costs nine steps. -/
def StmtNotTime : Prop :=
  ∀ (f : List Bool × List Bool → Bool) (t : ℕ → ℕ),
    ComputableInTime encodePair Computability.encodeBool f t →
      ComputableInTime encodePair Computability.encodeBool (fun a => !f a) (fun n => t n + 9)

/-- M1 of note 209 followed by `sepPair_time`: the pad `1^(N |x|) 0 x` in time `O(N)`. -/
def StmtPadClock : Prop :=
  ∀ N : ℕ → ℕ, Constructible N → ∃ c : ℕ,
    ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => List.replicate (N x.length) true ++ false :: x) (fun n => c * N n + c)

/-- Constructible bounds compose. -/
def StmtConstrComp : Prop :=
  ∀ f g : ℕ → ℕ, Constructible f → Constructible g → Constructible (fun n => g (f n))

/-- Affine bounds are constructible (the `scale` of note 210, 2.6). -/
def StmtConstrAff : Prop :=
  ∀ C : ℕ, 1 ≤ C → Constructible (fun n => C * n + C)

/-- M4 of note 209, verbatim: a verifier run under a budget equal to the pad length. -/
def StmtBudget : Prop :=
  ∀ (S : Set (List Bool × List Bool)) (t : ℕ → ℕ), DecidableInTime encodePair S t →
    ∃ (B : Set (List Bool × List Bool)) (K : ℕ),
      DecidableInTime encodePair B (fun l => K * l + K) ∧
      (∀ k s w, (List.replicate k true ++ false :: s, w) ∈ B → (s, w) ∈ S) ∧
      (∀ k s w, t (s.length + w.length) ≤ k → (s, w) ∈ S →
        (List.replicate k true ++ false :: s, w) ∈ B)

/-- The witness bound `|w| ≤ |z|` added to a linear-time relation keeps it linear (needed
because `NLIN` carries the witness bound inside the relation, note 210 F7). -/
def StmtLenGuard : Prop :=
  ∀ (B : Set (List Bool × List Bool)) (K : ℕ),
    DecidableInTime encodePair B (fun l => K * l + K) → ∃ K' : ℕ,
      DecidableInTime encodePair {p | p.2.length ≤ p.1.length ∧ p ∈ B} (fun l => K' * l + K')

/-- M5 of note 209, verbatim. -/
def StmtFixLead : Prop :=
  ∃ K : ℕ, ComputableInTime encodePair encodePair
    (fun p : List Bool × List Bool => (p.1, fixLen (lead p.1) p.2)) (fun n => K * n + K)

/-- M6 of note 209, the two fixed transducers. -/
def StmtToPairBody : Prop :=
  ∃ K : ℕ,
    ComputableInTime (fun x : List Bool => x) encodePair (fun s => (s, ([] : List Bool)))
      (fun n => K * n + K) ∧
    ComputableInTime encodePair encodePair
      (fun p : List Bool × List Bool => (body p.1, p.2)) (fun n => K * n + K)

/-- M6 of note 209, the inner encoding `E` and its reader `D`, with P0's `lead_E`, `E_mem_G`,
`D_E` folded in. -/
def StmtED : Prop :=
  ∃ (E : List Bool × List Bool → List Bool) (D : List Bool × List Bool → List Bool × List Bool)
    (K : ℕ),
    ComputableInTime encodePair (fun x : List Bool => x) E (fun n => K * n + K) ∧
    ComputableInTime encodePair encodePair D (fun n => K * n + K) ∧
    (∀ p, (E p).length ≤ 2 * (p.1.length + p.2.length) + 1) ∧
    (∀ p, (encodePair (D p)).length ≤ (encodePair p).length) ∧
    ∀ s y w : List Bool, false ∈ s →
      lead (E (s, y)) = lead s ∧ false ∈ E (s, y) ∧ D (E (s, y), w) = (s, y ++ w)

/-- L1 of note 209 at an abstract `g`: one existential block of length `lead s`. -/
def StmtL1g : Prop :=
  ∀ g : ℕ → ℕ, Constructible g → (∀ a : ℕ, NLIN a ⊆ DTIMEO g) →
    ∀ h : ℕ → ℕ, Constructible h → ∀ (S : Set (List Bool × List Bool)) (A : ℕ),
      DecidableInTime encodePair S (fun l => A * h l + A) →
      ∃ (f : List Bool → Bool) (C : ℕ),
        ComputableInTime (fun x : List Bool => x) Computability.encodeBool f
          (fun n => C * g (C * h (C * n + C) + C) + C) ∧
        ∀ s, f s = true ↔ ∃ y : List Bool, y.length = lead s ∧ (s, y) ∈ S

/-- LeadC of note 209 at an abstract `g`: `j` blocks of length `lead s`, on inputs with a
`false`. -/
def StmtLeadC : Prop :=
  ∀ g : ℕ → ℕ, Constructible g → (∀ a : ℕ, NLIN a ⊆ DTIMEO g) →
    ∀ (j : ℕ) (R : Set (List Bool × List Bool)) (K : ℕ),
      DecidableInTime encodePair R (fun l => K * l + K) →
      ∃ (f : List Bool → Bool) (C : ℕ),
        ComputableInTime (fun x : List Bool => x) Computability.encodeBool f
          (fun n => C * lvl g C j n + C) ∧
        ∀ s, false ∈ s → (f s = true ↔ Alt j (lead s) (fun w => (s, w) ∈ R))

/-! ### The top assembly: `StmtSlow3` from `StmtLeadC` -/

theorem lead_pad (k : ℕ) (x : List Bool) :
    lead (List.replicate k true ++ false :: x) = k := by
  induction k with
  | zero => simp [lead]
  | succ k ih => simp [lead, List.replicate_succ]

theorem body_pad (k : ℕ) (x : List Bool) :
    body (List.replicate k true ++ false :: x) = x := by
  induction k with
  | zero => simp [body]
  | succ k ih => simp [body, List.replicate_succ]

theorem lvl_mono {g : ℕ → ℕ} (hg : Monotone g) (C : ℕ) : ∀ j, Monotone (lvl g C j)
  | 0 => fun _ _ h => h
  | j + 1 => fun a b h => by
      simp only [lvl]
      exact hg (Nat.add_le_add_right (Nat.mul_le_mul_left C
        (lvl_mono hg C j (Nat.add_le_add_right (Nat.mul_le_mul_left C h) C))) C)

theorem cit_mono {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    {t t' : ℕ → ℕ} (h : ComputableInTime ea eb f t) (ht : ∀ n, t n ≤ t' n) :
    ComputableInTime ea eb f t' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun n => (hc n).trans (ht n)⟩

theorem aff_le {a α T C : ℕ} (h : a ≤ α * T + α) :
    C * a + C ≤ (C * α + C) * T + (C * α + C) := by
  have : C * a ≤ C * (α * T + α) := Nat.mul_le_mul_left C h
  nlinarith

theorem g3a_mono {g : ℕ → ℕ} (hg : Monotone g) {C C' a a' : ℕ} (hC : C ≤ C') (ha : a ≤ a') :
    g (C * g (C * g a + C) + C) ≤ g (C' * g (C' * g a' + C') + C') := by
  have h1 : g (C * g a + C) ≤ g (C' * g a' + C') :=
    hg (Nat.add_le_add (Nat.mul_le_mul hC (hg ha)) hC)
  exact hg (Nat.add_le_add (Nat.mul_le_mul hC h1) hC)

theorem slow3_of_leadC (hLC : StmtLeadC) (hPC : StmtPadClock) (hTB : StmtToPairBody) :
    StmtSlow3 := by
  intro g hgC hH T hT L hL
  obtain ⟨R, K, ⟨fR, hfR, hcR⟩, hLR⟩ := hL
  obtain ⟨Kb, -, hbody⟩ := hTB
  -- the top relation reads the block length off the pad
  have hRtop := Machines.comp_time encodePair encodePair Computability.encodeBool
    (fun p : List Bool × List Bool => (body p.1, p.2)) fR (fun n => Kb * n + Kb)
    (fun l => K * l + K) (fun n => n) hbody hcR
    (fun a b h => Nat.add_le_add_right (Nat.mul_le_mul_left K h) K)
    (fun p => by
      simp only [encodePair, List.length_append, List.length_map, body, List.length_drop]
      have := (List.dropWhile_suffix (l := p.1) id).length_le
      omega)
  have hRtop' := cit_mono hRtop (t' := fun n => (Kb + K + 2) * n + (Kb + K + 2))
    (fun n => by nlinarith)
  obtain ⟨f, C, hf, hspec⟩ := hLC g hgC hH 3 {p | (body p.1, p.2) ∈ R} (Kb + K + 2)
    ⟨fun p => fR (body p.1, p.2), fun p => hfR _, hRtop'⟩
  obtain ⟨c, hpad⟩ := hPC T hT
  have hdec := Machines.comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    Computability.encodeBool (fun x => List.replicate (T x.length) true ++ false :: x) f
    (fun n => c * T n + c) (fun n => C * lvl g C 3 n + C) (fun n => T n + n + 1) hpad hf
    (fun a b h => Nat.add_le_add_right (Nat.mul_le_mul_left C (lvl_mono hgC.1 C 3 h)) C)
    (fun x => by simp; omega)
  -- the constant of the target bound
  set α4 := C * (C * (C * (2 * C + C) + C) + C) + C with hα4
  set C' := α4 + C + 1 with hC'
  refine ⟨C', c + C + 6, L002 _ _ (fun n => ?_)
    ⟨fun x => f (List.replicate (T x.length) true ++ false :: x), fun x => ?_, hdec⟩⟩
  · -- the time bound
    have hTn : n ≤ T n := hT.2.1 n
    have hgid := hgC.2.1
    set m := T n + n + 1
    have hm : m ≤ 2 * T n + 2 := by omega
    have a1 : C * m + C ≤ (C * 2 + C) * T n + (C * 2 + C) := aff_le (by omega)
    have a2 := aff_le (C := C) a1
    have a3 := aff_le (C := C) a2
    have a4 := aff_le (C := C) a3
    have hCC' : C ≤ C' := by omega
    have hA : C * (C * (C * (C * m + C) + C) + C) + C ≤ C' * T n + C' := by
      have e : C * (C * (C * (C * 2 + C) + C) + C) + C = α4 := by rw [hα4]; ring
      rw [e] at a4
      nlinarith
    have hlvl : lvl g C 3 m ≤ g (C' * g (C' * g (C' * T n + C') + C') + C') := by
      show g (C * g (C * g (C * (C * (C * (C * m + C) + C) + C) + C) + C) + C) ≤ _
      exact g3a_mono hgC.1 hCC' hA
    have hC1 : 1 ≤ C' := by omega
    have hTΨ : T n ≤ g (C' * g (C' * g (C' * T n + C') + C') + C') := by
      have e1 : T n ≤ C' * T n + C' := by nlinarith
      have e2 : g (C' * T n + C') ≤ C' * g (C' * T n + C') + C' := by nlinarith
      have e3 : g (C' * g (C' * T n + C') + C') ≤
          C' * g (C' * g (C' * T n + C') + C') + C' := by nlinarith
      exact e1.trans ((hgid _).trans (e2.trans ((hgid _).trans (e3.trans (hgid _)))))
    have p1 := Nat.mul_le_mul_left c hTΨ
    have p2 := Nat.mul_le_mul_left C hlvl
    show c * T n + c + (2 * m + 2) + (C * lvl g C 3 m + C) ≤ _
    nlinarith
  · -- correctness
    refine (hLR x).trans ?_
    show _ ↔ f _ = true
    rw [hspec _ (by simp)]
    simp only [lead_pad, Set.mem_ofPred_eq, body_pad]

/-! ### `StmtLeadC` from `StmtL1g` and the machine pieces -/

theorem lvl_mono_C {g : ℕ → ℕ} (hg : Monotone g) {C C' : ℕ} (hC : C ≤ C') :
    ∀ j n, lvl g C j n ≤ lvl g C' j n
  | 0, _ => le_rfl
  | j + 1, n => by
      simp only [lvl]
      have h1 : lvl g C j (C * n + C) ≤ lvl g C' j (C' * n + C') :=
        (lvl_mono hg C j (Nat.add_le_add (Nat.mul_le_mul_right n hC) hC)).trans
          (lvl_mono_C hg hC j _)
      exact hg (Nat.add_le_add (Nat.mul_le_mul hC h1) hC)

theorem lvl_ge {g : ℕ → ℕ} (hg : ∀ n, n ≤ g n) {C : ℕ} (hC : 1 ≤ C) :
    ∀ j n, n ≤ lvl g C j n
  | 0, _ => le_rfl
  | j + 1, n => by
      simp only [lvl]
      have h1 := lvl_ge hg hC j (C * n + C)
      have h2 : n ≤ C * n + C := by nlinarith
      have h3 : lvl g C j (C * n + C) ≤ C * lvl g C j (C * n + C) + C := by nlinarith
      exact h2.trans (h1.trans (h3.trans (hg _)))

theorem lvl_constr (hComp : StmtConstrComp) (hAff : StmtConstrAff) {g : ℕ → ℕ}
    (hg : Constructible g) {C : ℕ} (hC : 1 ≤ C) :
    ∀ j (f : ℕ → ℕ), Constructible f → Constructible (fun n => lvl g C j (f n))
  | 0, _, hf => hf
  | j + 1, f, hf => by
      have h1 : Constructible (fun n => C * f n + C) := hComp _ _ hf (hAff C hC)
      have h2 := lvl_constr hComp hAff hg hC j _ h1
      have h3 := hComp _ _ h2 (hAff C hC)
      exact hComp _ g h3 hg

theorem encodePair_len (p : List Bool × List Bool) :
    (encodePair p).length = p.1.length + p.2.length := by
  simp [encodePair]

theorem leadC_of_pieces (hL1 : StmtL1g) (hNot : StmtNotTime) (hTB : StmtToPairBody)
    (hED : StmtED) (hComp : StmtConstrComp) (hAff : StmtConstrAff) : StmtLeadC := by
  intro g hgC hH j
  induction j with
  | zero =>
    intro R K ⟨fR, hfR, hcR⟩
    obtain ⟨Kt, hpair, -⟩ := hTB
    have h := Machines.comp_time (fun x : List Bool => x) encodePair Computability.encodeBool
      (fun s => (s, ([] : List Bool))) fR (fun n => Kt * n + Kt) (fun l => K * l + K)
      (fun n => n) hpair hcR (fun a b h => Nat.add_le_add_right (Nat.mul_le_mul_left K h) K)
      (fun s => by simp [encodePair_len])
    refine ⟨fun s => fR (s, []), Kt + K + 2, cit_mono h (fun n => ?_), fun s _ => ?_⟩
    · show Kt * n + Kt + (2 * n + 2) + (K * n + K) ≤ (Kt + K + 2) * n + (Kt + K + 2)
      nlinarith
    · exact (hfR _).symm
  | succ j ih =>
    intro R K ⟨fR, hfR, hcR⟩
    obtain ⟨E, D, KE, hE, hD, hElen, hDlen, hEDs⟩ := hED
    -- R' := {p | D p ∉ R}, linear
    have hR'0 := Machines.comp_time encodePair encodePair Computability.encodeBool D fR
      (fun n => KE * n + KE) (fun l => K * l + K) (fun n => n) hD hcR
      (fun a b h => Nat.add_le_add_right (Nat.mul_le_mul_left K h) K) hDlen
    have hR'1 := hNot _ _ hR'0
    have hR' : DecidableInTime encodePair {p | D p ∉ R}
        (fun l => (KE + K + 11) * l + (KE + K + 11)) := by
      refine ⟨fun p => !fR (D p), fun p => ?_, cit_mono hR'1 (fun n => ?_)⟩
      · simp [hfR]
      · show KE * n + KE + (2 * n + 2) + (K * n + K) + 9 ≤ _
        nlinarith
    obtain ⟨fj, Cj0, hfj0, hspecj⟩ := ih _ _ hR'
    set Cj := Cj0 + 1 with hCj
    have hCj1 : 1 ≤ Cj := by omega
    have hfj : ComputableInTime (fun x : List Bool => x) Computability.encodeBool fj
        (fun n => Cj * lvl g Cj j n + Cj) := cit_mono hfj0 (fun n => by
      have := lvl_mono_C hgC.1 (show Cj0 ≤ Cj by omega) j n
      show Cj0 * lvl g Cj0 j n + Cj0 ≤ Cj * lvl g Cj j n + Cj
      have := Nat.mul_le_mul (show Cj0 ≤ Cj by omega) this
      omega)
    -- S := {p | fj (E p) = false}
    set A := KE + Cj + 13 with hA
    set h : ℕ → ℕ := fun l => lvl g Cj j (A * l + A) with hh
    have hhC : Constructible h := lvl_constr hComp hAff hgC hCj1 j _ (hAff A (by omega))
    have hS0 := Machines.comp_time encodePair (fun x : List Bool => x) Computability.encodeBool
      E fj (fun n => KE * n + KE) (fun n => Cj * lvl g Cj j n + Cj) (fun n => 2 * n + 1) hE hfj
      (fun a b hab => Nat.add_le_add_right (Nat.mul_le_mul_left Cj (lvl_mono hgC.1 Cj j hab)) Cj)
      (fun p => by have := hElen p; rw [encodePair_len]; simpa using this)
    have hS1 := hNot _ _ hS0
    have hS : DecidableInTime encodePair {p | fj (E p) = false} (fun l => A * h l + A) := by
      refine ⟨fun p => !fj (E p), fun p => ?_, cit_mono hS1 (fun n => ?_)⟩
      · simp
      · show KE * n + KE + (2 * (2 * n + 1) + 2) + (Cj * lvl g Cj j (2 * n + 1) + Cj) + 9 ≤
          A * lvl g Cj j (A * n + A) + A
        have e1 : lvl g Cj j (2 * n + 1) ≤ lvl g Cj j (A * n + A) :=
          lvl_mono hgC.1 Cj j (by nlinarith)
        have e2 : A * n + A ≤ lvl g Cj j (A * n + A) := lvl_ge hgC.2.1 hCj1 j _
        have e3 : n ≤ lvl g Cj j (A * n + A) := le_trans (by nlinarith) e2
        have e4 := Nat.mul_le_mul_left Cj e1
        have e5 := Nat.mul_le_mul_left (KE + 4) e3
        nlinarith
    obtain ⟨f, C1, hf, hspec1⟩ := hL1 g hgC hH h hhC _ A hS
    set C2 := C1 + Cj + A * C1 + A + 1 with hC2
    refine ⟨f, C2, cit_mono hf (fun n => ?_), fun s hs => ?_⟩
    · show C1 * g (C1 * lvl g Cj j (A * (C1 * n + C1) + A) + C1) + C1 ≤
        C2 * g (C2 * lvl g C2 j (C2 * n + C2) + C2) + C2
      have e1 : lvl g Cj j (A * (C1 * n + C1) + A) ≤ lvl g C2 j (C2 * n + C2) :=
        (lvl_mono hgC.1 Cj j (show A * (C1 * n + C1) + A ≤ C2 * n + C2 by nlinarith)).trans
          (lvl_mono_C hgC.1 (show Cj ≤ C2 by omega) j _)
      have e2 : g (C1 * lvl g Cj j (A * (C1 * n + C1) + A) + C1) ≤
          g (C2 * lvl g C2 j (C2 * n + C2) + C2) :=
        hgC.1 (Nat.add_le_add (Nat.mul_le_mul (by omega) e1) (by omega))
      have e3 := Nat.mul_le_mul (show C1 ≤ C2 by omega) e2
      omega
    · rw [hspec1 s]
      show _ ↔ ∃ y : List Bool, y.length = lead s ∧
        ¬ Alt j (lead s) (fun w => ¬ (fun w => (s, w) ∈ R) (y ++ w))
      refine exists_congr fun y => and_congr_right fun _ => ?_
      obtain ⟨h1, h2, -⟩ := hEDs s y [] hs
      have hfun : (fun w => (E (s, y), w) ∈ {p | D p ∉ R}) = (fun w => ¬ (s, y ++ w) ∈ R) :=
        funext fun w => by
          show (D (E (s, y), w) ∉ R) = _
          rw [(hEDs s y w hs).2.2]
      have := hspecj (E (s, y)) h2
      rw [h1, hfun] at this
      show fj (E (s, y)) = false ↔ _
      rw [← this]
      simp

/-! ### `StmtL1g` from the machine pieces -/

theorem lead_le (s : List Bool) : lead s ≤ s.length :=
  (List.takeWhile_prefix (l := s) id).length_le

theorem fixLen_length (k : ℕ) (w : List Bool) : (fixLen k w).length = k := by
  simp [fixLen]

theorem fixLen_self {k : ℕ} {w : List Bool} (h : w.length = k) : fixLen k w = w :=
  List.take_left' h

theorem l1g_of_pieces (hB : StmtBudget) (hG : StmtLenGuard) (hFL : StmtFixLead)
    (hPC : StmtPadClock) (hComp : StmtConstrComp) (hAff : StmtConstrAff) : StmtL1g := by
  intro g hgC hH h hhC S A ⟨fS, hfS, hcS⟩
  obtain ⟨F, hF⟩ := hFL
  -- S' : the witness cut to the block length
  have hS'0 := Machines.comp_time encodePair encodePair Computability.encodeBool
    (fun p : List Bool × List Bool => (p.1, fixLen (lead p.1) p.2)) fS (fun n => F * n + F)
    (fun l => A * h l + A) (fun n => 2 * n) hF hcS
    (fun a b hab => Nat.add_le_add_right (Nat.mul_le_mul_left A (hhC.1 hab)) A)
    (fun p => by
      simp only [encodePair_len, fixLen_length]
      have := lead_le p.1
      omega)
  set t₁ : ℕ → ℕ := fun l => F * l + F + (2 * (2 * l) + 2) + (A * h (2 * l) + A) with ht₁
  have ht₁m : Monotone t₁ := by
    intro a b hab
    have := hhC.1 (Nat.mul_le_mul_left 2 hab)
    simp only [ht₁]
    have := Nat.mul_le_mul_left A this
    nlinarith
  obtain ⟨Bset, KB, hBdec, hBsound, hBcomp⟩ :=
    hB {p | (p.1, fixLen (lead p.1) p.2) ∈ S} t₁ ⟨_, fun p => hfS _, hS'0⟩
  obtain ⟨K', hB'⟩ := hG Bset KB hBdec
  -- the padded language
  have hLp : {z : List Bool | ∃ w, (z, w) ∈ {p : List Bool × List Bool |
      p.2.length ≤ p.1.length ∧ p ∈ Bset}} ∈ NLIN 1 :=
    ⟨_, K', hB', fun z w hzw => by simpa using hzw.1, fun z => Iff.rfl⟩
  obtain ⟨Kp, fp, hfp, hcp⟩ := hH 1 hLp
  -- the pad length
  set Bc := 2 * F + A + 10 with hBc
  set N : ℕ → ℕ := fun n => Bc * h (Bc * n + Bc) + Bc with hN
  have hNC : Constructible N := by
    have h1 := hComp _ h (hAff Bc (by omega)) hhC
    exact hComp _ (fun n => Bc * n + Bc) h1 (hAff Bc (by omega))
  have hhid := hhC.2.1
  have hNt : ∀ n, t₁ (2 * n) ≤ N n := by
    intro n
    show F * (2 * n) + F + (2 * (2 * (2 * n)) + 2) + (A * h (2 * (2 * n)) + A) ≤
      Bc * h (Bc * n + Bc) + Bc
    have e1 : h (2 * (2 * n)) ≤ h (Bc * n + Bc) := hhC.1 (by nlinarith)
    have e2 : n ≤ h (Bc * n + Bc) := le_trans (by nlinarith) (hhid _)
    have e3 := Nat.mul_le_mul_left A e1
    have e4 := Nat.mul_le_mul_left (2 * F + 8) e2
    nlinarith
  have hNn : ∀ n, n + 1 ≤ N n := by
    intro n
    have e2 : n ≤ h (Bc * n + Bc) := le_trans (by nlinarith) (hhid _)
    show n + 1 ≤ Bc * h (Bc * n + Bc) + Bc
    nlinarith
  obtain ⟨c, hpad⟩ := hPC N hNC
  have hdec := Machines.comp_time (fun x : List Bool => x) (fun x : List Bool => x)
    Computability.encodeBool (fun x => List.replicate (N x.length) true ++ false :: x) fp
    (fun n => c * N n + c) (fun n => Kp * g n + Kp) (fun n => 2 * N n) hpad hcp
    (fun a b hab => Nat.add_le_add_right (Nat.mul_le_mul_left Kp (hgC.1 hab)) Kp)
    (fun x => by have := hNn x.length; simp; omega)
  set C := 2 * Bc + c + Kp + 4 with hC
  refine ⟨fun s => fp (List.replicate (N s.length) true ++ false :: s), C,
    cit_mono hdec (fun n => ?_), fun s => ?_⟩
  · show c * N n + c + (2 * (2 * N n) + 2) + (Kp * g (2 * N n) + Kp) ≤
      C * g (C * h (C * n + C) + C) + C
    have e1 : 2 * N n ≤ C * h (C * n + C) + C := by
      show 2 * (Bc * h (Bc * n + Bc) + Bc) ≤ _
      have := hhC.1 (show Bc * n + Bc ≤ C * n + C by nlinarith)
      have := Nat.mul_le_mul (show 2 * Bc ≤ C by omega) this
      nlinarith
    have e2 := hgC.1 e1
    have e3 : 2 * N n ≤ g (2 * N n) := hgC.2.1 _
    have e4 := Nat.mul_le_mul_left (c + 4) (e3.trans e2)
    have e5 := Nat.mul_le_mul_left Kp e2
    nlinarith
  · rw [← hfp]
    constructor
    · rintro ⟨w, -, hw⟩
      exact ⟨fixLen (lead s) w, fixLen_length _ _, hBsound _ s w hw⟩
    · rintro ⟨y, hy, hyS⟩
      refine ⟨y, ?_, hBcomp _ s y ?_ ?_⟩
      · simp; have := lead_le s; omega
      · have := lead_le s
        exact (ht₁m (show s.length + y.length ≤ 2 * s.length by omega)).trans (hNt _)
      · show (s, fixLen (lead s) y) ∈ S
        rwa [fixLen_self hy]

/-! ## The rung from the machine pieces alone -/

theorem rung_of_machine_pieces (hRoot : StmtRootDom) (hPad : StmtPadExp) (hCLK : StmtCLK)
    (hPC : StmtPadClock) (hComp : StmtConstrComp) (hAff : StmtConstrAff) (hB : StmtBudget)
    (hG : StmtLenGuard) (hFL : StmtFixLead) (hNot : StmtNotTime) (hTB : StmtToPairBody)
    (hED : StmtED) (hNSC : StmtNoScaledCollapse) : StmtRung :=
  rung_of_pieces
    (slow3_of_leadC
      (leadC_of_pieces (l1g_of_pieces hB hG hFL hPC hComp hAff) hNot hTB hED hComp hAff)
      hPC hTB)
    hRoot hPad hCLK hNSC

end Evasion

end PEqualNP.Library
