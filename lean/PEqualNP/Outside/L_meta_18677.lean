import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18677_aux


def bin (op a b : Bool) := if op then a && b else a || b

def val (S : Finset ℕ) (g : (ℕ → Bool × ℕ × ℕ)) (x : ℕ → Bool) (w : ℕ) : Bool :=
  if w ∈ S then bin (g w).1
    (if (g w).2.1 < w then val S g x (g w).2.1 else false)
    (if (g w).2.2 < w then val S g x (g w).2.2 else false)
  else x w
termination_by w

def Good (H : ℕ) (S : Finset ℕ) (g : (ℕ → Bool × ℕ × ℕ)) : Prop :=
  ∀ w ∈ S, H ≤ w ∧ (g w).2.1 < w ∧ (g w).2.2 < w

theorem vin {S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {x : ℕ → Bool} {w H : ℕ} (h : Good H S g) (hw : w ∈ S) :
    val S g x w = bin (g w).1 (val S g x (g w).2.1) (val S g x (g w).2.2) := by
  rw [val, ite_eq_left hw, ite_eq_left (h w hw).2.1, ite_eq_left (h w hw).2.2]

theorem vout {S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {x : ℕ → Bool} {w : ℕ} (hw : w ∉ S) : val S g x w = x w := by
  rw [val, ite_eq_right hw]

def lport (i : ℕ) := 2 * i + 2

def rport (i : ℕ) := 2 * i + 3

def point (M : Finset ℕ) (u v w : ℕ) : Bool :=
  decide (w = 0 ∨ w = lport u ∨ w = rport v ∨ (u ∉ M ∧ w = rport u) ∨ (v ∉ M ∧ w = lport v))

def Solves (K M S : Finset ℕ) (g : (ℕ → Bool × ℕ × ℕ)) (o : ℕ) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, val S g (point M u v) o = decide (u ≠ v)

def Dark (K S : Finset ℕ) (g : (ℕ → Bool × ℕ × ℕ)) (w : ℕ) : Prop :=
  ∀ i ∈ K, val S g (point ∅ i i) w = false

def Normal (K S : Finset ℕ) (g : (ℕ → Bool × ℕ × ℕ)) : Prop :=
  ∀ w ∈ S, Dark K S g (g w).2.1 ∨ Dark K S g (g w).2.2 → Dark K S g w

def Alias (K M S : Finset ℕ) (g : (ℕ → Bool × ℕ × ℕ)) (w : ℕ) : Prop :=
  ∃ t < w, ∀ u ∈ K, ∀ v ∈ K, val S g (point M u v) w = val S g (point M u v) t


theorem nrDiag (M : Finset ℕ) (i : ℕ) : point M i i = point ∅ i i := by
  funext w
  unfold point
  congr 1
  apply propext
  tauto

def nrAlias (t b w : ℕ) := if w = t then b else w

theorem nrAliasLe {b t : ℕ} (hb : b < t) (w : ℕ) : nrAlias t b w ≤ w := by
  by_cases hw : w = t <;> simp [nrAlias, hw, hb.le]

def nrSet (S : Finset ℕ) (t f : ℕ) := insert f (S.erase t)

def nrGate (g : (ℕ → Bool × ℕ × ℕ)) (t b d o f : ℕ) : (ℕ → Bool × ℕ × ℕ) := fun w =>
  if w = f then (false, d, nrAlias t b o)
  else ((g w).1, nrAlias t b (g w).2.1, nrAlias t b (g w).2.2)

theorem nrEval {H t b d o f : ℕ} {S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)}
    (hg : Good H S g) (hT : Good H (nrSet S t f) (nrGate g t b d o f)) (hb : b < t)
    (hv : ∀ x, val S g x t = (val S g x d || val S g x b)) (x : ℕ → Bool) (w : ℕ) :
    w < f → (w < t ∨ val S g x d = false) →
      val (nrSet S t f) (nrGate g t b d o f) x (nrAlias t b w) = val S g x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwf hx
    by_cases hwt : w = t
    · subst w
      have hd : val S g x d = false := hx.resolve_left (Nat.lt_irrefl _)
      have hB := ih b hb (hb.trans hwf) (Or.inl hb)
      simpa [nrAlias, hb.ne, hv x, hd] using hB
    · rw [show nrAlias t b w = w by simp [nrAlias, hwt]]
      by_cases hw : w ∈ S
      · have hnew : w ∈ nrSet S t f := Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwt, hw⟩)
        rw [vin hT hnew, vin hg hw]
        simp only [nrGate, ite_eq_right hwf.ne]
        have hrec (c : ℕ) (hc : c < w) := ih c hc (hc.trans hwf) (hx.imp_left (fun h => hc.trans h))
        rw [hrec _ (hg w hw).2.1, hrec _ (hg w hw).2.2]
      · have hnew : w ∉ nrSet S t f := by simp [nrSet, hwf.ne, hw]
        rw [vout hnew, vout hw]

theorem nrChoice {K S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {H t : ℕ} (hg : Good H S g) (ht : t ∈ S)
    (hc : Dark K S g (g t).2.1 ∨ Dark K S g (g t).2.2) (hn : ¬Dark K S g t) :
    ∃ d b : ℕ, d < t ∧ b < t ∧ Dark K S g d ∧
      ∀ x, val S g x t = (val S g x d || val S g x b) := by
  have hop : (g t).1 = false := by
    cases hh : (g t).1 with
    | false => rfl
    | true =>
      exfalso
      apply hn
      intro i hi
      rw [vin hg ht, hh]
      rcases hc with hd | hd <;> simp [bin, hd i hi]
  rcases hc with hd | hd
  · refine ⟨(g t).2.1, (g t).2.2, (hg t ht).2.1, (hg t ht).2.2, hd, ?_⟩
    intro x
    rw [vin hg ht, hop]
    rfl
  · refine ⟨(g t).2.2, (g t).2.1, (hg t ht).2.2, (hg t ht).2.1, hd, ?_⟩
    intro x
    rw [vin hg ht, hop]
    exact Bool.or_comm _ _

noncomputable def nrLit (K S : Finset ℕ) (g : (ℕ → Bool × ℕ × ℕ)) : Finset ℕ := by
  classical
  exact S.filter (fun w => ¬Dark K S g w)

theorem nrStep {K M S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {H o : ℕ}
    (hg : Good H S g) (hs : Solves K M S g o) (hn : ¬Normal K S g) :
    ∃ T : Finset ℕ, ∃ h : (ℕ → Bool × ℕ × ℕ), ∃ p : ℕ, Good H T h ∧ Solves K M T h p ∧
      T.card ≤ S.card ∧ (nrLit K T h).card < (nrLit K S g).card := by
  classical
  unfold Normal at hn
  push Not at hn
  obtain ⟨t, ht, hc, hnt⟩ := hn
  obtain ⟨d, b, hdt, hbt, hdark, hv⟩ := nrChoice hg ht hc hnt
  let f := S.sup id + o + H + 1
  have hf (w : ℕ) (hw : w ∈ S) : w < f := by
    have hh : id w ≤ S.sup id := Finset.le_sup hw
    change w ≤ S.sup id at hh
    dsimp [f]
    omega
  have hof : o < f := by dsimp [f]; omega
  have hHf : H ≤ f := by dsimp [f]; omega
  have hdf : d < f := hdt.trans (hf t ht)
  let T := nrSet S t f
  let h := nrGate g t b d o f
  have hT : Good H T h := by
    intro w hw
    change w ∈ insert f (S.erase t) at hw
    rcases Finset.mem_insert.mp hw with he | he
    · subst w
      simpa [h, nrGate] using And.intro hHf (And.intro hdf ((nrAliasLe hbt o).trans_lt hof))
    · have hws := (Finset.mem_erase.mp he).2
      have hwf := (hf w hws).ne
      obtain ⟨hH, ha, hb⟩ := hg w hws
      simpa [h, nrGate, hwf] using And.intro hH (And.intro ((nrAliasLe hbt _).trans_lt ha) ((nrAliasLe hbt _).trans_lt hb))
  have heq (x : ℕ → Bool) (w : ℕ) (hwf : w < f) (hx : w < t ∨ val S g x d = false) :
      val T h x (nrAlias t b w) = val S g x w :=
    nrEval hg hT hbt hv x w hwf hx
  have hdeq (x : ℕ → Bool) : val T h x d = val S g x d := by
    simpa only [nrAlias, ite_eq_right hdt.ne] using heq x d hdf (Or.inl hdt)
  have hfT : f ∈ T := Finset.mem_insert_self _ _
  have hfeq (x : ℕ → Bool) : val T h x f = (val S g x d || val T h x (nrAlias t b o)) := by
    rw [vin hT hfT]
    simp [h, nrGate, bin, hdeq]
  have hsol : Solves K M T h f := by
    intro u hu v hw
    let x := point M u v
    change val T h x f = _
    rw [hfeq]
    cases hdx : val S g x d with
    | false =>
      rw [Bool.false_or, heq x o hof (Or.inr hdx)]
      exact hs u hu v hw
    | true =>
      have huv : u ≠ v := by
        intro he
        have hx : x = point ∅ u u := by change point M u v = _; rw [← he, nrDiag]
        rw [hx, hdark u hu] at hdx
        contradiction
      simp [huv]
  have hfdark : Dark K T h f := by
    intro i hi
    simpa only [nrDiag M i, ne_self_iff_false, decide_false] using hsol i hi i hi
  have hsub : nrLit K T h ⊆ (nrLit K S g).erase t := by
    intro w hw
    obtain ⟨hwT, hnw⟩ := Finset.mem_filter.mp hw
    rcases Finset.mem_insert.mp hwT with he | he
    · exact (hnw (he ▸ hfdark)).elim
    · obtain ⟨hwt, hws⟩ := Finset.mem_erase.mp he
      apply Finset.mem_erase.mpr
      refine ⟨hwt, Finset.mem_filter.mpr ⟨hws, ?_⟩⟩
      intro hd
      apply hnw
      intro i hi
      have hval := heq (point ∅ i i) w (hf w hws) (Or.inr (hdark i hi))
      simpa only [nrAlias, ite_eq_right hwt, hd i hi] using hval
  have hcs : T.card ≤ S.card := by
    exact (Finset.card_insert_le f (S.erase t)).trans (Finset.card_erase_add_one ht).le
  have htLit : t ∈ nrLit K S g := Finset.mem_filter.mpr ⟨ht, hnt⟩
  exact ⟨T, h, f, hT, hsol, hcs, (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem htLit)⟩

theorem nrNormalize {n : ℕ} {K M S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {o : ℕ}
    (hg : Good (2*n+2) S g) (hs : Solves K M S g o) :
    ∃ T : Finset ℕ, ∃ h : (ℕ → Bool × ℕ × ℕ), ∃ p : ℕ,
      Good (2*n+2) T h ∧ Solves K M T h p ∧ Normal K T h ∧ T.card ≤ S.card := by
  classical
  generalize hq : (nrLit K S g).card = q
  induction q using Nat.strong_induction_on generalizing S g o with
  | ind q ih =>
    by_cases hn : Normal K S g
    · exact ⟨S, g, o, hg, hs, hn, le_rfl⟩
    · obtain ⟨T, h, p, hT, hsol, hle, hlt⟩ := nrStep hg hs hn
      obtain ⟨U, k, a, hU, hsol', hnorm, hle'⟩ := ih _ (hlt.trans_le hq.le) hT hsol rfl
      exact ⟨U, k, a, hU, hsol', hnorm, hle'.trans hle⟩

def crPort (b : Bool) (i : ℕ) := if b then rport i else lport i

def crOriented (M : Finset ℕ) (b : Bool) (u v : ℕ) := if b then point M v u else point M u v

def crSide (M : Finset ℕ) (b : Bool) (u w : ℕ) := w = crPort b u ∨ (u ∉ M ∧ w = crPort (!b) u)

theorem crHit {M : Finset ℕ} {b : Bool} {u v w : ℕ} : crOriented M b u v w = true ↔ w = 0 ∨ crSide M b u w ∨ crSide M (!b) v w := by
  cases b <;> simp [crOriented, point, crSide, crPort] <;> tauto

theorem crEq {b c : Bool} {i j : ℕ} : crPort b i = crPort c j ↔ b = c ∧ i = j := by
  cases b <;> cases c <;> simp [crPort, lport, rport] <;> omega

theorem crNeZero (b : Bool) (i : ℕ) : crPort b i ≠ 0 := by cases b <;> simp [crPort, lport, rport]

theorem crDiag {i w : ℕ} {b : Bool} : point ∅ i i w = true ↔ w = 0 ∨ w = crPort b i ∨ w = crPort (!b) i := by
  cases b <;> simp [point, crPort] <;> tauto

theorem crDiagM {M : Finset ℕ} {i : ℕ} : point M i i = point ∅ i i := by
  funext w
  apply Bool.eq_iff_iff.mpr
  simp [point]; tauto

theorem crSolve {K M S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {o : ℕ} (hs : Solves K M S g o) {b : Bool} {i j : ℕ} (hi : i ∈ K) (hj : j ∈ K) (hij : i ≠ j) : val S g (crOriented M b i j) o = true := by
  cases b <;> simp [crOriented, hs i hi j hj, hs j hj i hi, hij, Ne.symm hij]

theorem crDout {K M S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {o : ℕ} (hs : Solves K M S g o) {i : ℕ} (hi : i ∈ K) : val S g (point ∅ i i) o = false := by simpa [crDiagM] using hs i hi i hi

theorem crAgainst {M : Finset ℕ} {b : Bool} {i j w : ℕ} (hi : i ∈ M) (hw : w ≠ crPort b i) (hx : crOriented M b i j w = true) : point ∅ j j w = true := by
  apply (crDiag (b := b)).2
  rw [crHit] at hx
  simp [crSide, hi, hw] at hx
  tauto

theorem crOff {M : Finset ℕ} {b : Bool} {i j : ℕ} (hi : i ∈ M) (hij : i ≠ j) : crOriented M b i j (crPort (!b) i) = false := by
  apply Bool.eq_false_iff.mpr
  simp [crHit, crSide, crEq, crNeZero, hi, hij]

theorem crGone {M : Finset ℕ} {b : Bool} {i u v : ℕ} (hu : u ≠ i) (hv : v ≠ i) : point M u v (crPort b i) = false := by
  cases b <;> simp [crPort, point, lport, rport] <;> omega

theorem crDiagPort (b : Bool) (i : ℕ) : point ∅ i i (crPort b i) = true := (crDiag (b := b)).2 (Or.inr (Or.inl rfl))

theorem crMerge {M : Finset ℕ} {b : Bool} {i u v : ℕ} (hp : point (M.erase i) u v (crPort b i) = true) {w : ℕ} (hw : point ∅ i i w = true) : point (M.erase i) u v w = true := by
  have h : u = i ∨ v = i := by by_contra! h; simp [crGone h.1 h.2] at hp
  rcases h with rfl | rfl <;> rcases (crDiag (b := false)).1 hw with rfl | rfl | rfl <;> simp [point, crPort]

def crReads (g : (ℕ → Bool × ℕ × ℕ)) (t p : ℕ) := (g t).2.1 = p ∨ (g t).2.2 = p

theorem crView {g : (ℕ → Bool × ℕ × ℕ)} {t p : ℕ} (h : crReads g t p) : ∃ W, ((g t).2.1 = p ∧ (g t).2.2 = W) ∨ ((g t).2.1 = W ∧ (g t).2.2 = p) := by
  rcases h with h | h
  · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨_, Or.inr ⟨rfl, h⟩⟩

theorem crEval {H S g t p W} (hg : Good H S g) (ht : t ∈ S) (hf : ((g t).2.1 = p ∧ (g t).2.2 = W) ∨ ((g t).2.1 = W ∧ (g t).2.2 = p)) (x : ℕ → Bool) : val S g x t = bin (g t).1 (val S g x p) (val S g x W) := by
  rw [vin hg ht]; rcases hf with h | h <;> rw [h.1, h.2]
  cases (g t).1 <;> simp [bin, Bool.and_comm, Bool.or_comm]

theorem crLess {H S g t p W} (hg : Good H S g) (ht : t ∈ S) (hf : ((g t).2.1 = p ∧ (g t).2.2 = W) ∨ ((g t).2.1 = W ∧ (g t).2.2 = p)) : p < t ∧ W < t := by
  obtain ⟨_, ha, hb⟩ := hg t ht
  rcases hf with h | h <;> grind

theorem crCut {H S g} (hg : Good H S g) {x y : ℕ → Bool} {B : ℕ → Prop} {d : ℕ}
    (hraw : ∀ w, ¬B w → w ∉ S → x w = true → y w = true)
    (hgate : ∀ w ∈ S, w ≤ d → ¬B w → (B (g w).2.1 ∨ B (g w).2.2) → val S g x w = true → val S g y w = true)
    {w : ℕ} (hd : w ≤ d) (hw : ¬B w) (hx : val S g x w = true) : val S g y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hS : w ∈ S
    · by_cases ha : B (g w).2.1 ∨ B (g w).2.2
      · exact hgate w hS hd hw ha hx
      · push Not at ha
        obtain ⟨_, hl, hr⟩ := hg w hS
        have l := ih _ hl (by omega) ha.1
        have r := ih _ hr (by omega) ha.2
        rw [vin hg hS] at hx ⊢
        cases ho : (g w).1 <;> simp [bin, ho] at hx ⊢ <;> tauto
    · rw [vout hS] at hx ⊢; exact hraw _ hw hS hx

theorem crMono {H S g} (hg : Good H S g) {x y : ℕ → Bool} (h : ∀ w, x w = true → y w = true) {w : ℕ} (hx : val S g x w = true) : val S g y w = true :=
  crCut (B := fun _ => False) hg (fun w _ _ => h w) (by simp) (Nat.le_refl _) (by simp) hx

theorem crRaw {n S g i} (hg : Good (2*n+2) S g) (hi : i ∈ Finset.range n) (b : Bool) : crPort b i ∉ S := by
  intro h; have hz := (hg _ h).1; have := Finset.mem_range.mp hi
  cases b <;> simp [crPort, lport, rport] at hz <;> omega

theorem crZero {n S g} (hg : Good (2*n+2) S g) : 0 ∉ S := by intro h; have := (hg _ h).1; omega

theorem crTwo {K : Finset ℕ} {i : ℕ} (hi : i ∈ K) (h3 : 3 ≤ K.card) : ∃ j ∈ K, ∃ k ∈ K, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
  have hc : 1 < (K.erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hc
  exact ⟨j, (Finset.mem_erase.mp hj).2, k, (Finset.mem_erase.mp hk).2, (Finset.mem_erase.mp hj).1, (Finset.mem_erase.mp hk).1, hjk⟩

theorem crOutput {K M S g o i j} (hs : Solves K M S g o) (hi : i ∈ K) (hj : j ∈ K) (hij : i ≠ j) : o ∈ S := by
  by_contra ho
  have hx := crSolve (b := false) hs hi hj hij
  rw [vout ho, crHit] at hx
  have a := crDout hs hi; have b := crDout hs hj
  rw [vout ho] at a b
  have aux (u : ℕ) (hu : point ∅ u u o = false) : ¬ (o = 0 ∨ o = crPort false u ∨ o = crPort true u) := fun h => by have := (crDiag (b := false)).2 h; simp_all
  have := aux i a; have := aux j b
  simp [crSide] at hx; tauto

theorem crSeen {n K M S g o i j} (hg : Good (2*n+2) S g) (hs : Solves K M S g o) (hi : i ∈ M) (him : i ∈ K) (hin : i ∈ Finset.range n) (hj : j ∈ K) (hij : i ≠ j) (b : Bool) : ∃ t ∈ S, crReads g t (crPort b i) := by
  by_contra! h
  have hout := crOutput hs him hj hij
  have ho : o ≠ crPort b i := fun e => crRaw hg hin b (e ▸ hout)
  have hz := crCut (B := fun w => w = crPort b i) hg (fun _ hw _ => crAgainst hi hw) (fun w hw _ _ hr => False.elim (h w hw hr)) (Nat.le_refl o) ho (crSolve (b := b) hs him hj hij)
  simp [crDout hs hj] at hz

theorem crKilled {n K M S g w p} (hg : Good (2*n+2) S g) (hw : w ∈ S) (hr : crReads g w p) (hz : ∀ u ∈ K, ∀ v ∈ K, val S g (point M u v) p = false) : Alias K M S g w := by
  obtain ⟨W, hf⟩ := crView hr
  obtain ⟨hp, hW⟩ := crLess hg hw hf
  cases he : (g w).1
  · refine ⟨W, hW, fun u hu v hv => ?_⟩; simp [crEval hg hw hf, hz u hu v hv, he, bin]
  · refine ⟨p, hp, fun u hu v hv => ?_⟩; simp [crEval hg hw hf, hz u hu v hv, he, bin]

theorem crDeadPort {n S g i w} {K M : Finset ℕ} (hg : Good (2*n+2) S g) (hin : i ∈ Finset.range n) (hw : w ∈ S) {b : Bool} (hr : crReads g w (crPort b i)) : Alias (K.erase i) (M.erase i) S g w := by
  apply crKilled hg hw hr
  intro u hu v hv; exact (vout (crRaw hg hin b)).trans (crGone (Finset.mem_erase.mp hu).1 (Finset.mem_erase.mp hv).1)

theorem crFour {S : Finset ℕ} {A : ℕ → Prop} {a b c d : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (aa : A a) (ab : A b) (ac : A c) (ad : A d) : ∃ F : Finset ℕ, F ⊆ S ∧ 4 ≤ F.card ∧ ∀ w ∈ F, A w := by
  refine ⟨{a,b,c,d}, ?_, ?_, ?_⟩
  · intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> assumption
  · simp [hab, hac, had, hbc, hbd, hcd]
  · intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> assumption

theorem crSame {H K M S g t p W} (hg : Good H S g) (ht : t ∈ S) (hf : ((g t).2.1 = p ∧ (g t).2.2 = W) ∨ ((g t).2.1 = W ∧ (g t).2.2 = p)) (heq : ∀ u ∈ K, ∀ v ∈ K, val S g (point M u v) p = val S g (point M u v) W) : Alias K M S g t := by
  refine ⟨W, (crLess hg ht hf).2, fun u hu v hv => ?_⟩
  rw [crEval hg ht hf, heq u hu v hv]; cases (g t).1 <;> simp [bin]

theorem crPair {n K S g t i} {M : Finset ℕ} (hg : Good (2*n+2) S g) (hin : i ∈ Finset.range n) (ht : t ∈ S) (hL : crReads g t (crPort false i)) (hR : crReads g t (crPort true i)) : Alias K (M.erase i) S g t := by
  obtain ⟨W, hf⟩ := crView hL
  have he : W = crPort true i := by unfold crReads at hR; rcases hf with h | h <;> simp [h.1, h.2, crEq] at hR <;> exact hR
  subst W
  apply crSame hg ht hf
  intro u hu v hv; rw [vout (crRaw hg hin false), vout (crRaw hg hin true)]
  apply Bool.eq_iff_iff.mpr; constructor <;> intro h <;> exact crMerge h (crDiagPort _ i)

theorem crForce {n K M S g o i b t} (hg : Good (2*n+2) S g) (hs : Solves K M S g o) (hi : i ∈ M) (him : i ∈ K) (hin : i ∈ Finset.range n) (honly : ∀ w ∈ S, crReads g w (crPort b i) → w = t) {j} (hj : j ∈ K) (hij : i ≠ j) : val S g (crOriented M b i j) t = true ∧ val S g (point ∅ j j) t = false := by
  have ho : o ≠ crPort b i := fun e => crRaw hg hin b (e ▸ crOutput hs him hj hij)
  have hh : ¬(val S g (crOriented M b i j) t = true → val S g (point ∅ j j) t = true) := by
    intro h
    have hz := crCut (B := fun w => w = crPort b i) hg (fun _ hw _ => crAgainst hi hw) (fun w hw _ _ hr => honly w hw hr ▸ h) (Nat.le_refl o) ho (crSolve (b := b) hs him hj hij)
    simp [crDout hs hj] at hz
  simpa using hh

theorem crRest {n M S g t W i b j} (hg : Good (2*n+2) S g) (hi : i ∈ M) (honly : ∀ w ∈ S, crReads g w (crPort b i) → w = t) (hlt : W < t) (hne : W ≠ crPort b i) (hx : val S g (crOriented M b i j) W = true) (k : ℕ) : val S g (crOriented (M.erase i) b k j) W = true := by
  apply crCut (B := fun w => w = crPort b i) hg _ _ (Nat.le_refl W) hne hx
  · intro w hw _ hp
    rw [crHit] at hp ⊢
    simp [crSide, hi, hw] at hp
    simp [crSide]
    grind
  · intro w hw hle _ hr
    have := honly w hw hr; omega

theorem crNotBoth {g : (ℕ → Bool × ℕ × ℕ)} {S : Finset ℕ} {i w : ℕ} (h : ¬∃ w ∈ S, crReads g w (crPort false i) ∧ crReads g w (crPort true i)) (hw : w ∈ S) {b : Bool} (hp : crReads g w (crPort b i)) : ¬crReads g w (crPort (!b) i) := by
  intro hq; apply h; refine ⟨w, hw, ?_⟩; cases b <;> simp_all

theorem crAndHard {n K M S g o i b t W} (hK : K ⊆ Finset.range n) (hi : i ∈ M) (him : i ∈ K) (h3 : 3 ≤ K.card)
    (hg : Good (2*n+2) S g) (hs : Solves K M S g o) (hn : Normal K S g)
    (ht : t ∈ S) (hp : crReads g t (crPort b i)) (honly : ∀ w ∈ S, crReads g w (crPort b i) → w = t)
    (hnq : ¬crReads g t (crPort (!b) i))
    (hf : ((g t).2.1 = crPort b i ∧ (g t).2.2 = W) ∨ ((g t).2.1 = W ∧ (g t).2.2 = crPort b i))
    (hop : (g t).1 = true) (hW : W ≠ crPort b i) (hd : val S g (point ∅ i i) W = false) :
    ∃ F : Finset ℕ, F ⊆ S ∧ 4 ≤ F.card ∧ ∀ w ∈ F, Alias (K.erase i) (M.erase i) S g w := by
  have hin := hK him
  have hlt := (crLess hg ht hf).2
  have raw := crRaw hg hin b
  have qraw := crRaw hg hin (!b)
  obtain ⟨j, hj, k, hk, hji, hki, hjk⟩ := crTwo him h3
  have hpos (a : ℕ) (ha : a ∈ K) (hia : i ≠ a) : val S g (crOriented M b i a) W = true := by
    have h := (crForce hg hs hi him hin honly ha hia).1
    rw [crEval hg ht hf, hop] at h; exact (Bool.and_eq_true_iff.mp h).2
  have hgate : W ∈ S := by
    by_contra h
    have a := hpos j hj hji.symm; have c := hpos k hk hki.symm
    rw [vout h] at a c hd
    have hjd := (crDiag (b := b)).1 (crAgainst hi hW a)
    have hkd := (crDiag (b := b)).1 (crAgainst hi hW c)
    have h0 : W ≠ 0 := fun e => by simp [e, point] at hd
    rcases hjd with z | z | z <;> rcases hkd with y | y | y <;> first | exact h0 z | exact h0 y | exact hjk (crEq.mp (z.symm.trans y)).2
  have hOne (u : ℕ) (hu : u ∈ K.erase i) (v : ℕ) (hv : v ∈ K.erase i) : val S g (point (M.erase i) u v) W = true := by
    obtain ⟨hu', huK⟩ := Finset.mem_erase.mp hu
    obtain ⟨hv', hvK⟩ := Finset.mem_erase.mp hv
    cases b
    · exact crRest hg hi honly hlt hW (hpos v hvK hv'.symm) u
    · exact crRest hg hi honly hlt hW (hpos u huK hu'.symm) v
  have hAW : Alias (K.erase i) (M.erase i) S g W := by
    refine ⟨0, ?_, fun u hu v hv => ?_⟩
    · have := (hg W hgate).1; omega
    · simp [vout (crZero hg), point, hOne u hu v hv]
  have hDark : Dark K S g t := by
    intro a ha; rw [crEval hg ht hf, hop, vout raw]
    by_cases he : a = i
    · subst a; simp [hd, bin]
    · simp [crGone he he, bin]
  have hDead (u : ℕ) (hu : u ∈ K.erase i) (v : ℕ) (hv : v ∈ K.erase i) : val S g (point (M.erase i) u v) t = false := by
    simp [crEval hg ht hf, hop, bin, vout raw, crGone (Finset.mem_erase.mp hu).1 (Finset.mem_erase.mp hv).1]
  have hWq : ¬crReads g W (crPort (!b) i) := by
    intro h; obtain ⟨V, hv⟩ := crView h
    cases he : (g W).1
    · simp [crEval hg hgate hv, he, bin, vout qraw, crDiagPort] at hd
    · have hz := hpos j hj hji.symm
      simp [crEval hg hgate hv, he, bin, vout qraw, crOff hi hji.symm] at hz
  have ho : o ≠ t := by
    intro e; have hz := hs j hj k hk
    simp [e, hjk, crEval hg ht hf, hop, bin, vout raw, crGone hji hki] at hz
  have hor : o ≠ crPort b i := fun e => raw (e ▸ crOutput hs hj hk hjk)
  have hr : ∃ a ∈ S, crReads g a t ∧ ¬crReads g a (crPort (!b) i) := by
    by_contra! h
    have hnDark (a : ℕ) (ha : a ∈ S) (hat : crReads g a t) : Dark K S g a := by
      apply hn a ha; rcases hat with e | e
      · exact Or.inl (e ▸ hDark)
      · exact Or.inr (e ▸ hDark)
    have hz := crCut (B := fun w => w = crPort b i ∨ w = t) hg
      (fun _ hw _ => crAgainst hi (fun e => hw (Or.inl e)))
      (d := o) (x := crOriented M b i j) (y := point ∅ j j) (by
        intro a ha _ hao hr hx
        have hat : crReads g a t := by
          by_contra H
          have har : crReads g a (crPort b i) := by unfold crReads at H ⊢; tauto
          exact hao (Or.inr (honly a ha har))
        have haq := h a ha hat
        obtain ⟨V, hv⟩ := crView haq
        cases he : (g a).1
        · have hdi := hnDark a ha hat i him
          simp [crEval hg ha hv, he, bin, vout qraw, crDiagPort] at hdi
        · simp [crEval hg ha hv, he, bin, vout qraw, crOff hi hji.symm] at hx)
      (Nat.le_refl _) (not_or_intro hor ho) (crSolve (b := b) hs him hj hji.symm)
    simp [crDout hs hj] at hz
  obtain ⟨a, ha, hat, haq⟩ := hr
  obtain ⟨d, hdS, hdq⟩ := crSeen hg hs hi him hin hj hji.symm (!b)
  have hta : t < a := by obtain ⟨V, hv⟩ := crView hat; exact (crLess hg ha hv).1
  exact crFour hgate ht ha hdS (by omega) (by omega) (fun e => hWq (e ▸ hdq)) (by omega) (fun e => hnq (e ▸ hdq)) (fun e => haq (e ▸ hdq)) hAW (crDeadPort hg hin ht hp) (crKilled hg ha hat hDead) (crDeadPort hg hin hdS hdq)

theorem crUnique {n K M S g o i b t} (hK : K ⊆ Finset.range n) (hi : i ∈ M) (him : i ∈ K) (h3 : 3 ≤ K.card)
    (hg : Good (2*n+2) S g) (hs : Solves K M S g o) (hn : Normal K S g)
    (ht : t ∈ S) (hp : crReads g t (crPort b i)) (honly : ∀ w ∈ S, crReads g w (crPort b i) → w = t)
    (hnq : ¬crReads g t (crPort (!b) i)) :
    (∃ w ∈ S, Alias K (M.erase i) S g w) ∨ ∃ F : Finset ℕ, F ⊆ S ∧ 4 ≤ F.card ∧ ∀ w ∈ F, Alias (K.erase i) (M.erase i) S g w := by
  obtain ⟨W, hf⟩ := crView hp
  have hin := hK him
  have raw := crRaw hg hin b
  by_cases he : W = crPort b i
  · exact Or.inl ⟨t, ht, crSame hg ht hf (fun _ _ _ _ => congrArg _ he.symm)⟩
  have hsoft (hd : val S g (point ∅ i i) W = true) (u v : ℕ) (h : val S g (point (M.erase i) u v) (crPort b i) = true) : val S g (point (M.erase i) u v) W = true := by
    rw [vout raw] at h; exact crMono hg (fun _ => crMerge h) hd
  cases hop : (g t).1
  · have hnd : ¬Dark K S g W := by
      intro hd
      have hh : Dark K S g t := by
        apply hn t ht; rcases hf with h | h
        · exact Or.inr (h.2 ▸ hd)
        · exact Or.inl (h.1 ▸ hd)
      have h := hh i him
      simp [crEval hg ht hf, hop, bin, vout raw, crDiagPort] at h
    unfold Dark at hnd; push Not at hnd
    obtain ⟨a, ha, hwa⟩ := hnd
    have e : a = i := by
      by_contra h
      have hz := (crForce hg hs hi him hin honly ha (Ne.symm h)).2
      simp [crEval hg ht hf, hop, bin, hwa] at hz
    subst a
    refine Or.inl ⟨t, ht, W, (crLess hg ht hf).2, fun u hu v hv => ?_⟩
    rw [crEval hg ht hf, hop]
    have h := hsoft (by simpa using hwa) u v
    cases e : val S g (point (M.erase i) u v) (crPort b i) <;> simp_all [bin]
  · cases hd : val S g (point ∅ i i) W
    · exact Or.inr (crAndHard hK hi him h3 hg hs hn ht hp honly hnq hf hop he hd)
    · refine Or.inl ⟨t, ht, crPort b i, (crLess hg ht hf).1, fun u hu v hv => ?_⟩
      rw [crEval hg ht hf, hop]
      have h := hsoft hd u v
      cases e : val S g (point (M.erase i) u v) (crPort b i) <;> simp_all [bin]

theorem crStep {n : ℕ} {K M S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {o i : ℕ} (hK : K ⊆ Finset.range n) (hM : M ⊆ K) (hi : i ∈ M) (h3 : 3 ≤ K.card) (hg : Good (2*n+2) S g) (hs : Solves K M S g o) (hn : Normal K S g) : (∃ w ∈ S, Alias K (M.erase i) S g w) ∨ ∃ F : Finset ℕ, F ⊆ S ∧ 4 ≤ F.card ∧ ∀ w ∈ F, Alias (K.erase i) (M.erase i) S g w := by
  have him := hM hi
  have hin := hK him
  by_cases hp : ∃ w ∈ S, crReads g w (crPort false i) ∧ crReads g w (crPort true i)
  · obtain ⟨w, hw, hl, hr⟩ := hp
    exact Or.inl ⟨w, hw, crPair hg hin hw hl hr⟩
  obtain ⟨j, hj, _, _, hji, _, _⟩ := crTwo him h3
  obtain ⟨a, ha, al⟩ := crSeen hg hs hi him hin hj hji.symm false
  obtain ⟨c, hc, cr⟩ := crSeen hg hs hi him hin hj hji.symm true
  by_cases au : ∀ w ∈ S, crReads g w (crPort false i) → w = a
  · exact crUnique hK hi him h3 hg hs hn ha al au (crNotBoth hp ha al)
  by_cases cu : ∀ w ∈ S, crReads g w (crPort true i) → w = c
  · exact crUnique hK hi him h3 hg hs hn hc cr cu (crNotBoth hp hc cr)
  push Not at au cu
  obtain ⟨b, hb, bl, hba⟩ := au
  obtain ⟨d, hd, dr, hdc⟩ := cu
  have dis : ∀ x ∈ S, crReads g x (crPort false i) → ∀ y, crReads g y (crPort true i) → x ≠ y := by
    intro x hx hl y hr e; subst y; exact hp ⟨_, hx, hl, hr⟩
  exact Or.inr (crFour ha hb hc hd hba.symm (dis a ha al c cr) (dis a ha al d dr) (dis b hb bl c cr) (dis b hb bl d dr) hdc.symm (crDeadPort hg hin ha al) (crDeadPort hg hin hb bl) (crDeadPort hg hin hc cr) (crDeadPort hg hin hd dr))

def bypass (F : Finset ℕ) (r : ℕ → ℕ) (w : ℕ) : ℕ :=
  if w ∈ F ∧ r w < w then bypass F r (r w) else w
termination_by w

theorem bypass_le (F : Finset ℕ) (r : ℕ → ℕ) (w : ℕ) : bypass F r w ≤ w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [bypass]
    split_ifs with hw
    · exact (ih _ hw.2).trans hw.2.le
    · rfl

theorem prune {H : ℕ} {K M S F : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {o : ℕ}
    (hg : Good H S g) (hs : Solves K M S g o) (_hF : F ⊆ S) (ha : ∀ w ∈ F, Alias K M S g w) :
    ∃ h : (ℕ → Bool × ℕ × ℕ), ∃ p : ℕ, Good H (S \ F) h ∧ Solves K M (S \ F) h p := by
  classical
  let r (w : ℕ) := if hw : w ∈ F then (ha w hw).choose else w
  have hr w (hw : w ∈ F) : r w < w ∧ ∀ u ∈ K, ∀ v ∈ K,
      val S g (point M u v) w = val S g (point M u v) (r w) := by
    simpa only [r, dite_eq_left hw] using (ha w hw).choose_spec
  let d := bypass F r
  let h (w : ℕ) := ((g w).1, d (g w).2.1, d (g w).2.2)
  have hh : Good H (S \ F) h := by
    intro w hw
    have hw' := hg w (Finset.mem_sdiff.mp hw).1
    exact ⟨hw'.1, (bypass_le ..).trans_lt hw'.2.1, (bypass_le ..).trans_lt hw'.2.2⟩
  refine ⟨h, d o, hh, ?_⟩
  intro u hu v hv
  suffices ∀ w, val (S \ F) h (point M u v) (d w) = val S g (point M u v) w by
    rw [this, hs u hu v hv]
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hf : w ∈ F
    · have he : d w = d (r w) := by rw [show d w = bypass F r w from rfl, bypass, ite_eq_left ⟨hf, (hr w hf).1⟩]
      rw [he, ih _ (hr w hf).1, (hr w hf).2 u hu v hv]
    · have he : d w = w := by rw [show d w = bypass F r w from rfl, bypass, ite_eq_right (fun h => hf h.1)]
      rw [he]
      by_cases hw : w ∈ S
      · rw [vin hh (Finset.mem_sdiff.mpr ⟨hw, hf⟩), vin hg hw]
        change bin _ (val _ _ _ (d _)) (val _ _ _ (d _)) = _
        rw [ih _ (hg w hw).2.1, ih _ (hg w hw).2.2]
      · rw [vout hw, vout (fun (e : w ∈ S \ F) => hw (Finset.mem_sdiff.mp e).1)]

theorem bin_mono {op a b c d : Bool} (ha : a = true → c = true) (hb : b = true → d = true) :
    bin op a b = true → bin op c d = true := by
  cases op <;> simp [bin] <;> tauto

theorem val_mono {H S g} (hg : Good H S g) {x y : ℕ → Bool} (hxy : ∀ w, x w = true → y w = true) :
    ∀ w, val S g x w = true → val S g y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w ∈ S
    · rw [vin hg hw, vin hg hw]
      exact bin_mono (ih _ (hg w hw).2.1) (ih _ (hg w hw).2.2)
    · simpa only [vout hw] using hxy w

theorem point_grow {M : Finset ℕ} {i u v w : ℕ} (ht : point M u v w = true) :
    point (M.erase i) u v w = true := by
  simp [point] at ht ⊢
  tauto

theorem point_diag (M : Finset ℕ) (i w : ℕ) : point M i i w = point ∅ i i w := by
  unfold point
  rw [decide_eq_decide]
  simp only [Finset.notMem_empty]
  tauto

theorem merge_solves {H K M S g o} (hg : Good H S g) (hs : Solves K M S g o) (i : ℕ) :
    Solves K (M.erase i) S g o := by
  intro u hu v hv
  have h0 := hs u hu v hv
  by_cases huv : u = v
  · subst v
    simpa only [funext (point_diag M u), funext (point_diag (M.erase i) u)] using h0
  · simpa only [decide_eq_true huv] using val_mono hg (fun _ => point_grow) o (by simpa [huv] using h0)

theorem delete_solves {H K M S g o} (hg : Good H S g) (hs : Solves K M S g o) (i : ℕ) :
    Solves (K.erase i) (M.erase i) S g o := by
  intro u hu v hv
  exact merge_solves hg hs i u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv)

def plug (g : (ℕ → Bool × ℕ × ℕ)) (z : ℕ) (t : Bool × ℕ × ℕ) : (ℕ → Bool × ℕ × ℕ) := fun w => if w = z then t else g w

theorem plug_good {S H g} (hg : Good H S g) {z a b : ℕ} (hz : z ∉ S)
    (hzH : H ≤ z) (ha : a < z) (hb : b < z) (op : Bool) :
    Good H (insert z S) (plug g z (op, a, b)) := by
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · simpa [plug] using And.intro hzH (And.intro ha hb)
  · have hne : w ≠ z := fun e => hz (e ▸ hw)
    simpa [plug, hne] using hg w hw

theorem plug_old {S H g} (hg : Good H S g) {z a b : ℕ} {op : Bool}
    (hg' : Good H (insert z S) (plug g z (op,a,b))) (x : ℕ → Bool) (w : ℕ) (hw : w < z) :
    val (insert z S) (plug g z (op,a,b)) x w = val S g x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hn := Nat.ne_of_lt hw
    by_cases h : w ∈ S
    · rw [vin hg' (Finset.mem_insert_of_mem h), vin hg h]
      simp only [plug, ite_eq_right hn]
      rw [ih _ (hg w h).2.1 ((hg w h).2.1.trans hw), ih _ (hg w h).2.2 ((hg w h).2.2.trans hw)]
    · rw [vout h, vout (by simp [hn,h] : w ∉ insert z S)]

theorem plug_new {S H g} (hg : Good H S g) {z a b : ℕ} {op : Bool} (ha : a < z) (hb : b < z)
    (hg' : Good H (insert z S) (plug g z (op,a,b))) (x : ℕ → Bool) :
    val (insert z S) (plug g z (op,a,b)) x z = bin op (val S g x a) (val S g x b) := by
  rw [vin hg' (Finset.mem_insert_self ..)]
  simp only [plug, ite_true]
  rw [plug_old hg hg' x a ha, plug_old hg hg' x b hb]

theorem point_full (u v w : ℕ) : point ∅ u v w = true ↔
    w = 0 ∨ w = lport u ∨ w = rport u ∨ w = lport v ∨ w = rport v := by
  simp only [point, decide_eq_true_eq, Finset.notMem_empty]
  tauto

theorem left_full (u v i : ℕ) : point ∅ u v (lport i) = true ↔ i = u ∨ i = v := by
  rw [point_full]
  unfold lport rport
  omega

def moved (H i j w : ℕ) := if w < H then
    if w = lport i ∨ w = rport i then 1 else if w = lport j ∨ w = rport j then H else w
  else w+1

theorem move_lt {H i j w k : ℕ} (_hH : 2 ≤ H) (hk : H ≤ k) (hw : w < k) : moved H i j w < k+1 := by
  unfold moved
  split_ifs <;> omega

theorem extend {n : ℕ} {K S : Finset ℕ} {i j o : ℕ} {g : (ℕ → Bool × ℕ × ℕ)} (hK : K ⊆ Finset.range n)
    (hi : i ∈ K) (hj : j ∈ K) (hij : i ≠ j) (hg : Good (2*n+2) S g) (hs : Solves (K.erase i) ∅ S g o) :
    ∃ T : Finset ℕ, ∃ h : (ℕ → Bool × ℕ × ℕ), ∃ p : ℕ, Good (2*n+2) T h ∧ Solves K ∅ T h p ∧ T.card ≤ S.card + 3 := by
  classical
  let H := 2*n+2
  have li : lport i < H := by have := Finset.mem_range.mp (hK hi); dsimp [lport,H]; omega
  have lj : lport j < H := by have := Finset.mem_range.mp (hK hj); dsimp [lport,H]; omega
  let m := moved H i j
  let T := insert H (S.image Nat.succ)
  let h : (ℕ → Bool × ℕ × ℕ) := fun w => if w = H then (false,lport i,lport j) else
    ((g (w-1)).1,m (g (w-1)).2.1,m (g (w-1)).2.2)
  have hp (w : ℕ) (hw : w < H) : w ∉ T := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with e | hh
    · omega
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hh
    have : H ≤ k := (hg k hk).1
    omega
  have hT : Good H T h := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simpa [h] using And.intro (le_refl H) (And.intro li lj)
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hkg,ha,hb⟩ := hg k hk
    change H ≤ k at hkg
    have hne : k.succ ≠ H := by omega
    simp only [h, ite_eq_right hne, Nat.succ_sub_one]
    exact ⟨by omega, move_lt (by dsimp [H]; omega) hkg ha, move_lt (by dsimp [H]; omega) hkg hb⟩
  let f (k : ℕ) := if k = i then j else k
  have fm {k : ℕ} (hk : k ∈ K) : f k ∈ K.erase i := by
    by_cases e : k = i <;> simp [f,e,Finset.mem_erase,hij.symm,hj,hk]
  have sim (u v : ℕ) (hu : u ∈ K) (hv : v ∈ K) (w : ℕ) :
      val T h (point ∅ u v) (m w) = val S g (point ∅ (f u) (f v)) w := by
    have un := Finset.mem_range.mp (hK hu)
    have vn := Finset.mem_range.mp (hK hv)
    have fun' := Finset.mem_range.mp (hK (Finset.mem_of_mem_erase (fm hu)))
    have fvn := Finset.mem_range.mp (hK (Finset.mem_of_mem_erase (fm hv)))
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw : w ∈ S
      · obtain ⟨hkg,ha,hb⟩ := hg w hw
        change H ≤ w at hkg
        have hm : m w = w+1 := by simp [m,moved, Nat.not_lt.mpr hkg]
        have hws : w+1 ∈ T := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
        have hne : w+1 ≠ H := by omega
        rw [hm,vin hT hws,vin hg hw]
        simp only [h,ite_eq_right hne,Nat.add_sub_cancel]
        rw [ih _ ha, ih _ hb]
      · rw [vout hw]
        by_cases hx : w < H
        · by_cases h1 : w = lport i ∨ w = rport i
          · have hm : m w = 1 := by simp [m,moved,hx,h1]
            rw [hm,vout (hp _ (by dsimp [H]; omega)),Bool.eq_iff_iff,point_full,point_full]
            have hfi := (Finset.mem_erase.mp (fm hu)).1
            have hfj := (Finset.mem_erase.mp (fm hv)).1
            unfold lport rport at *
            omega
          · by_cases h2 : w = lport j ∨ w = rport j
            · have hm : m w = H := by simp [m,moved,hx,h1,h2]
              rw [hm,vin hT (Finset.mem_insert_self ..)]
              simp only [h,ite_eq_left rfl,bin,Bool.false_eq_true,ite_false]
              rw [vout (hp _ li),vout (hp _ lj),Bool.eq_iff_iff,Bool.or_eq_true,left_full,left_full,point_full]
              dsimp [f,lport,rport] at *
              split_ifs <;> omega
            · have hm : m w = w := by simp [m,moved,hx,h1,h2]
              rw [hm,vout (hp _ hx),Bool.eq_iff_iff,point_full,point_full]
              unfold f
              split_ifs <;> grind
        · have hm : m w = w+1 := by simp [m,moved,hx]
          have ht : w+1 ∉ T := by
            intro he
            rcases Finset.mem_insert.mp he with he | he
            · omega
            obtain ⟨k,hk,hke⟩ := Finset.mem_image.mp he
            exact hw (Nat.succ.inj hke ▸ hk)
          rw [hm,vout ht,Bool.eq_iff_iff,point_full,point_full]
          dsimp [H,lport,rport] at *
          omega
  let z := max (max (T.sup id) H) (m o) + 1
  have zS : z ∉ T := fun hz => by have hle : z ≤ T.sup id := Finset.le_sup (f := id) hz; dsimp [z] at hle; omega
  have zH : H < z := by dsimp [z]; omega
  have zo : m o < z := by dsimp [z]; omega
  let h1 := plug h z (true,lport i,lport j)
  have hg1 : Good H (insert z T) h1 := plug_good hT zS zH.le (li.trans zH) (lj.trans zH) true
  have z1S : z+1 ∉ insert z T := by
    simp only [Finset.mem_insert,not_or]
    refine ⟨by omega, fun hz => ?_⟩
    have hle : z+1 ≤ T.sup id := Finset.le_sup (f := id) hz
    dsimp [z] at hle
    omega
  let h2 := plug h1 (z+1) (false,z,m o)
  have hg2 : Good H (insert (z+1) (insert z T)) h2 := plug_good hg1 z1S (by omega) (by omega) (by omega) false
  refine ⟨_,h2,z+1,hg2,?_,?_⟩
  · intro u hu v hv
    rw [plug_new hg1 (by omega) (by omega) hg2, plug_new hT (li.trans zH) (lj.trans zH) hg1,
      vout (hp _ li),vout (hp _ lj),plug_old hT hg1 _ _ zo,sim u v hu hv,hs _ (fm hu) _ (fm hv)]
    rw [Bool.eq_iff_iff]
    simp only [bin,ite_true,Bool.false_eq_true,ite_false,Bool.or_eq_true,Bool.and_eq_true,left_full,decide_eq_true_eq]
    dsimp [f]
    split_ifs <;> omega
  · have ht := Finset.card_insert_le H (S.image Nat.succ)
    have ht' := Finset.card_image_le (s := S) (f := Nat.succ)
    rw [Finset.card_insert_of_notMem z1S, Finset.card_insert_of_notMem zS]
    change (insert H (S.image Nat.succ)).card + 1 + 1 ≤ _
    omega

theorem frontier {H S g} (hg : Good H S g) (k : ℕ) (T : Finset ℕ) (hT : ∀ w ∈ T, w ∈ S → w < k) :
    ∃ U : Finset ℕ, U.card ≤ T.card + ((Finset.range k).filter (· ∈ S)).card ∧
      ∀ x y : ℕ → Bool, (∀ w ∈ U, x w = true → y w = true) →
        ∀ w ∈ T, val S g x w = true → val S g y w = true := by
  classical
  induction k generalizing T with
  | zero =>
    refine ⟨T,by simp,?_⟩
    intro x y hxy w hw
    have hn : w ∉ S := fun e => Nat.not_lt_zero _ (hT w hw e)
    simpa only [vout hn] using hxy w hw
  | succ k ih =>
    have step : ((Finset.range k).filter (· ∈ S)).card ≤ ((Finset.range (k+1)).filter (· ∈ S)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
    by_cases h : k ∈ T ∧ k ∈ S
    · obtain ⟨hkt,hks⟩ := h
      let a := (g k).2.1
      let b := (g k).2.2
      let T' := insert a (insert b (T.erase k))
      have ha : a < k := (hg k hks).2.1
      have hb : b < k := (hg k hks).2.2
      obtain ⟨U,hU,hs⟩ := ih T' (by
        intro w hw hwS
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact ha
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hb
        have h' := Finset.mem_erase.mp hw
        have := hT w h'.2 hwS
        omega)
      refine ⟨U,?_,?_⟩
      · have c1 := Finset.card_insert_le a (insert b (T.erase k))
        have c2 := Finset.card_insert_le b (T.erase k)
        have c3 := Finset.card_erase_add_one hkt
        change U.card ≤ (insert a (insert b (T.erase k))).card + _ at hU
        rw [Finset.range_add_one,Finset.filter_insert]
        have eh : k ∉ (Finset.range k).filter (· ∈ S) := by simp
        rw [ite_eq_left hks,Finset.card_insert_of_notMem eh]
        omega
      · intro x y hxy w hw
        by_cases he : w = k
        · subst w
          rw [vin hg hks,vin hg hks]
          exact bin_mono (hs x y hxy a (Finset.mem_insert_self ..))
            (hs x y hxy b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))
        · exact hs x y hxy w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,hw⟩)))
    · obtain ⟨U,hU,hs⟩ := ih T (by
        intro w hw hws
        have := hT w hw hws
        have hne : w ≠ k := fun e => h ⟨e ▸ hw, e ▸ hws⟩
        omega)
      exact ⟨U,by omega,hs⟩

theorem input_bound {H : ℕ} {K M S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {o : ℕ} (hk : 2 ≤ K.card)
    (hm : M ⊆ K) (hg : Good H S g) (hs : Solves K M S g o) :
    K.card + M.card ≤ S.card + 1 := by
  classical
  obtain ⟨U,hu,hsup⟩ := frontier hg (o+1) {o} (by simp)
  have cc : U.card ≤ S.card+1 := by
    have : ((Finset.range (o+1)).filter (· ∈ S)).card ≤ S.card :=
      Finset.card_le_card fun k h => (Finset.mem_filter.mp h).2
    simp only [Finset.card_singleton] at hu
    omega
  have wit (i j : ℕ) (hi : i ∈ K) (hj : j ∈ K) (hne : i ≠ j) :
      (∃ w ∈ U, w = lport i ∨ (i ∉ M ∧ w = rport i)) ∧
      (∃ w ∈ U, w = rport i ∨ (i ∉ M ∧ w = lport i)) := by
    have left_bad (a b : ℕ) (ha : a ∈ K) (hb : b ∈ K) (hab : a ≠ b) :
        ∃ w ∈ U, point M a b w = true ∧ point M j j w = false := by
      by_contra! hn
      have ff := hsup (point M a b) (point M j j) (by
        intro w hw ht
        simpa using hn w hw ht) o (Finset.mem_singleton_self o) (by rw [hs a ha b hb]; simp [hab])
      simp [hs j hj j hj] at ff
    constructor
    · obtain ⟨w,hw,h1,h2⟩ := left_bad i j hi hj hne
      refine ⟨w,hw,?_⟩
      simp [point] at h1 h2
      tauto
    · obtain ⟨w,hw,h1,h2⟩ := left_bad j i hj hi hne.symm
      refine ⟨w,hw,?_⟩
      simp [point] at h1 h2
      tauto
  let f (i : ℕ) := if lport i ∈ U then lport i else rport i
  have grab (i : ℕ) (hi : i ∈ K) : f i ∈ U ∧ (i ∈ M → lport i ∈ U ∧ rport i ∈ U) := by
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < (K.erase i).card by have := Finset.card_erase_add_one hi; omega)
    obtain ⟨h1,h2⟩ := wit i j hi (Finset.mem_of_mem_erase hj) (Finset.mem_erase.mp hj).1.symm
    obtain ⟨a,ha,ha'⟩ := h1
    obtain ⟨b,hb,hb'⟩ := h2
    dsimp only [f]
    split_ifs <;> grind
  have fits : K.image f ∪ M.image rport ⊆ U := by
    intro w hw
    rcases Finset.mem_union.mp hw with hl | hr
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
      exact (grab i hi).1
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
      exact ((grab i (hm hi)).2 hi).2
  have dis : Disjoint (K.image f) (M.image rport) := by
    rw [Finset.disjoint_left]
    rintro _ hw hl
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hl
    have hj' := ((grab j (hm hj)).2 hj).1
    dsimp only [f] at he
    split_ifs at he with h
    · unfold lport rport at he
      omega
    · have : j = i := by unfold rport at he; omega
      subst j
      exact h hj'
  have inj : Function.Injective f := by
    intro i j he
    dsimp only [f] at he
    split_ifs at he <;> unfold lport rport at * <;> omega
  have inj' : Function.Injective rport := by intro i j he; unfold rport at he; omega
  have ct := Finset.card_le_card fits
  rw [Finset.card_union_of_disjoint dis, Finset.card_image_of_injective _ inj,Finset.card_image_of_injective _ inj'] at ct
  omega

theorem base_two {n : ℕ} {K M S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {o : ℕ}
    (hK : K ⊆ Finset.range n) (hm : M ⊆ K) (hk : K.card = 2)
    (hg : Good (2*n+2) S g) (hs : Solves K M S g o) :
    ∃ T : Finset ℕ, ∃ h : (ℕ → Bool × ℕ × ℕ), ∃ p : ℕ, Good (2*n+2) T h ∧ Solves K ∅ T h p ∧ T.card + M.card ≤ S.card := by
  have cb := input_bound (by omega : 2 ≤ K.card) hm hg hs
  obtain ⟨i,j,hij,hpair⟩ := Finset.card_eq_two.mp hk
  have hi : i < n := Finset.mem_range.mp (hK (by simp [hpair]))
  have hj : j < n := Finset.mem_range.mp (hK (by simp [hpair]))
  let H := 2*n+2
  let h : (ℕ → Bool × ℕ × ℕ) := fun _ => (true,lport i,lport j)
  have li : lport i < H := by dsimp [lport,H]; omega
  have lj : lport j < H := by dsimp [lport,H]; omega
  have hgood : Good H {H} h := by
    intro w hw
    obtain rfl := Finset.mem_singleton.mp hw
    exact ⟨le_rfl,li,lj⟩
  refine ⟨{H},h,H,hgood,?_,by simp only [Finset.card_singleton]; omega⟩
  intro u hu v hv
  rw [vin hgood (Finset.mem_singleton_self H)]
  change bin true (val {H} h _ (lport i)) (val {H} h _ (lport j)) = _
  rw [vout (by simpa using li.ne : lport i ∉ ({H} : Finset ℕ)), vout (by simpa using lj.ne : lport j ∉ ({H} : Finset ℕ)),Bool.eq_iff_iff]
  simp only [bin,ite_true,Bool.and_eq_true,left_full,decide_eq_true_eq]
  simp only [hpair,Finset.mem_insert,Finset.mem_singleton] at hu hv
  omega

theorem discount {n : ℕ} {K M S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {o : ℕ}
    (hK : K ⊆ Finset.range n) (hm : M ⊆ K) (hk : 2 ≤ K.card)
    (hg : Good (2*n+2) S g) (hs : Solves K M S g o) :
    ∃ T : Finset ℕ, ∃ h : (ℕ → Bool × ℕ × ℕ), ∃ p : ℕ, Good (2*n+2) T h ∧ Solves K ∅ T h p ∧ T.card + M.card ≤ S.card := by
  classical
  generalize hc : M.card = c
  induction c using Nat.strong_induction_on generalizing K M S g o with
  | ind c ih =>
    by_cases h0 : M = ∅
    · subst M
      exact ⟨S,g,o,hg,hs,by simp [← hc]⟩
    by_cases hk2 : K.card = 2
    · simpa only [← hc] using base_two hK hm hk2 hg hs
    have hk3 : 3 ≤ K.card := by omega
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    have cm := Finset.card_erase_add_one hi
    have ck := Finset.card_erase_add_one (hm hi)
    have clt : (M.erase i).card < c := by omega
    obtain ⟨N,d,q,hd,hq,hn,cs⟩ := nrNormalize hg hs
    rcases crStep hK hm hi hk3 hd hq hn with ⟨w,hw,ha⟩ | ⟨F,hF,cf,ha⟩
    · have hf : {w} ⊆ N := Finset.singleton_subset_iff.mpr hw
      obtain ⟨d',q',hd',hq'⟩ := prune hd (merge_solves hd hq i) hf (by simpa using ha)
      obtain ⟨T,h,p,ht,hp,ct⟩ := ih _ clt hK ((Finset.erase_subset i M).trans hm) hk hd' hq' rfl
      have ce := Finset.card_sdiff_add_card_eq_card hf
      simp only [Finset.card_singleton] at ce
      exact ⟨T,h,p,ht,hp,by omega⟩
    · obtain ⟨d',q',hd',hq'⟩ := prune hd (delete_solves hd hq i) hF ha
      have hkm : K.erase i ⊆ Finset.range n := (Finset.erase_subset i K).trans hK
      have hmm : M.erase i ⊆ K.erase i := Finset.erase_subset_erase i hm
      obtain ⟨T,h,p,ht,hp,ct⟩ := ih _ clt hkm hmm (by omega) hd' hq' rfl
      obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < (K.erase i).card by omega)
      obtain ⟨T',h',p',ht',hp',ct'⟩ := extend hK (hm hi) (Finset.mem_of_mem_erase hj) (Finset.mem_erase.mp hj).1.symm ht hp
      have ce := Finset.card_sdiff_add_card_eq_card hF
      exact ⟨T',h',p',ht',hp',by omega⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ioRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem ioSnoc (gs : List Gate) (g : Gate) (x : List Bool) :
    ioRun (gs ++ [g]) x = ioRun gs x ++ [g.op.eval (g.inputs.map fun i => (ioRun gs x).getD i false)] := by
  simp [ioRun, List.foldl_append]

theorem ioLen (gs : List Gate) (x : List Bool) : (ioRun gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [ioRun]
  | append_singleton gs g ih => rw [ioSnoc]; simp [ih]; omega

theorem ioGet (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem ioLast (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem ioPrefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (ioRun (gs ++ hs) x).getD i false = (ioRun gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, ioSnoc, ioGet _ _ _ (by rw [ioLen, List.length_append]; omega), ih]

theorem ioInput (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (ioRun gs x).getD i false = x.getD i false := by
  simpa [ioRun] using ioPrefix [] gs x i (by simpa using hi)

theorem ioGate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (ioRun gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (ioRun gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen := ioLen gs x
    have same (k : ℕ) (hk : k ≤ gs.length) (l : List ℕ) :
        (l.map fun i => if i < x.length + k then (ioRun (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (ioRun gs x).getD i false else false := by
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact ioPrefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), ioPrefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, ioSnoc, ← hlen, ioLast]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def ioWire (n j i : ℕ) := if i < n then lport i else if i < 2*n then rport (i-n)
  else if i < 2*n+j then i+2 else 1

theorem ioWireLt (n j i : ℕ) : ioWire n j i < 2*n+2+j := by
  unfold ioWire lport rport; split_ifs <;> omega

def ioArg (n j k : ℕ) (b : Bool) (l : List ℕ) :=
  (l[k]?.map (ioWire n j)).getD (if b then 0 else 1)

theorem ioArgLt (n j k : ℕ) (b : Bool) (l : List ℕ) : ioArg n j k b l < 2*n+2+j := by
  unfold ioArg
  cases l[k]? with
  | none => cases b <;> simp; omega
  | some i => exact ioWireLt n j i

def ioPairGate (n j : ℕ) (q : Gate) : Bool × ℕ × ℕ :=
  let b := match q.op with | .and => true | _ => false
  (b, ioArg n j 0 b q.inputs, ioArg n j 1 b q.inputs)

theorem ioPairEval (n j : ℕ) (q : Gate) (V R : ℕ → Bool) (h0 : V 0 = true) (h1 : V 1 = false)
    (hv : ∀ i, V (ioWire n j i) = R i) (hop : q.op = GateOp.and ∨ q.op = GateOp.or)
    (hq : q.inputs.length ≤ 2) :
    bin (ioPairGate n j q).1 (V (ioPairGate n j q).2.1) (V (ioPairGate n j q).2.2) = q.op.eval (q.inputs.map R) := by
  rcases q with ⟨op,l⟩
  change op = _ ∨ op = _ at hop
  change l.length ≤ 2 at hq
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> rcases hop with rfl | rfl <;>
    simp_all [ioPairGate, ioArg, bin, GateOp.eval]

theorem ioFrom {n s : ℕ} (hn : 2 ≤ n)
    (hr : RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) :
    ∃ S : Finset ℕ, ∃ g : (ℕ → Bool × ℕ × ℕ), ∃ o : ℕ, Good (2*n+2) S g ∧
      Solves (Finset.range n) (Finset.range n) S g o ∧ S.card ≤ s := by
  obtain ⟨C, hC, hc, hrep⟩ := hr
  let H := 2*n+2
  let S := Finset.Ico H (H + C.gates.length)
  let g : (ℕ → Bool × ℕ × ℕ) := fun w => if h : w-H < C.gates.length then ioPairGate n (w-H) C.gates[w-H] else (false,0,0)
  have good : Good H S g := by
    intro w hw
    obtain ⟨ha,hb⟩ := Finset.mem_Ico.mp hw
    have hj : w-H < C.gates.length := by omega
    simp only [g, dite_eq_left hj, ioPairGate]
    have h : 2*n+2+(w-H) = w := by dsimp [H] at ha ⊢; omega
    exact ⟨ha, (ioArgLt _ _ _ _ _).trans_le h.le, (ioArgLt _ _ _ _ _).trans_le h.le⟩
  refine ⟨S, g, ioWire n C.gates.length C.output, good, ?_, by simpa [S, Circuit.size] using hc⟩
  intro u hu v hv
  have hu' := Finset.mem_range.mp hu
  have hv' := Finset.mem_range.mp hv
  let U : Fin n := ⟨u,hu'⟩
  let V : Fin n := ⟨v,hv'⟩
  let x := oneEach U V
  let p := point (Finset.range n) u v
  have px (w : ℕ) : p w = decide (w = 0 ∨ w = lport u ∨ w = rport v) := by simp [p,point,hu,hv]
  have xl : x.length = 2*n := by simp [x,oneEach]; omega
  have lower (w : ℕ) (hw : w < H) : val S g p w = p w := vout (by simp [S, not_le.mpr hw])
  have h0 : val S g p 0 = true := by rw [lower 0 (by dsimp [H]; omega),px]; simp
  have h1 : val S g p 1 = false := by rw [lower 1 (by dsimp [H]; omega),px]; simp [lport,rport]
  have simw : ∀ w, val S g p (ioWire n C.gates.length w) = (ioRun C.gates x).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hin : w < 2*n
      · have hwin : w < x.length := by omega
        rw [ioInput C.gates x w hwin]
        simp only [x,oneEach] at hwin ⊢
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwin]
        simp only [Option.getD_some]
        by_cases hl : w < n
        · rw [ioWire, ite_eq_left hl, lower _ (by dsimp [H,lport]; omega), px]
          have hw' : w < (List.ofFn fun i : Fin n => decide (i=U)).length := by simpa using hl
          rw [List.getElem_append_left hw']
          simp only [List.getElem_ofFn]
          rw [decide_eq_decide]
          simp only [lport,rport,Fin.ext_iff,U]
          omega
        · rw [ioWire, ite_eq_right hl, ite_eq_left hin, lower _ (by dsimp [H,rport]; omega), px]
          have hw' : ¬ w < (List.ofFn fun i : Fin n => decide (i=U)).length := by simpa using hl
          rw [List.getElem_append_right (Nat.le_of_not_gt hw')]
          simp only [List.getElem_ofFn]
          rw [decide_eq_decide]
          simp only [List.length_ofFn,lport,rport,Fin.ext_iff,V]
          omega
      · by_cases hw : w < 2*n+C.gates.length
        · let j := w-2*n
          have hj : j < C.gates.length := by dsimp [j]; omega
          have hwj : 2*n+j = w := by dsimp [j]; omega
          have hsub : w+2-H = j := by dsimp [H,j]; omega
          have hgp : g (w+2) = ioPairGate n j C.gates[j] := by simp [g,hsub,hj]
          have hwm : w+2 ∈ S := by simp [S,H]; omega
          rw [ioWire, ite_eq_right (by omega), ite_eq_right hin, ite_eq_left hw, vin good hwm, hgp]
          have hg := ioGate C.gates x j hj
          rw [xl, hwj] at hg
          rw [hg]
          apply ioPairEval _ _ _ _ _ h0 h1 _ (by simpa using (hC _ (List.getElem_mem hj)).1) (hC _ (List.getElem_mem hj)).2
          intro i
          split_ifs with h
          · rw [← ih i h]; congr 1; unfold ioWire; split_ifs <;> omega
          · have e : ioWire n j i = 1 := by unfold ioWire; split_ifs <;> omega
            rw [e,h1]
        · rw [ioWire, ite_eq_right (by omega), ite_eq_right hin, ite_eq_right hw, h1,
            List.getD_eq_default _ _ (by rw [ioLen,xl]; omega)]
  rw [simw]
  change C.eval (oneEach U V) = _
  simpa [U,V,Fin.ext_iff] using hrep U V

def ioRv (x : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr i => x.getD i false

def ioSeed (n w : ℕ) : Bool ⊕ ℕ :=
  if w = 0 then .inl true else if 2 ≤ w ∧ (w-2)/2 < n then .inr ((w-2)/2) else .inl false

def ioBits {n : ℕ} (x : Fin n → Bool) (w : ℕ) := ioRv (List.ofFn x) (ioSeed n w)

def ioOK (q : Gate) := (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ q.inputs.length ≤ 2

theorem ioEmit (n : ℕ) (hs : List Gate) (op : Bool) (a b : Bool ⊕ ℕ) :
    ∃ (e : List Gate) (r : Bool ⊕ ℕ), (∀ q ∈ e, ioOK q) ∧ e.length ≤ 1 ∧
      ((∀ t, a = .inr t → t < n+hs.length) → (∀ t, b = .inr t → t < n+hs.length) →
        ∀ t, r = .inr t → t < n+hs.length+e.length) ∧
      ∀ x : Fin n → Bool, ioRv (ioRun (hs++e) (List.ofFn x)) r =
        bin op (ioRv (ioRun hs (List.ofFn x)) a) (ioRv (ioRun hs (List.ofFn x)) b) := by
  rcases a with c | i
  · refine ⟨[], if c = op then b else .inl c, by simp, by simp, ?_, ?_⟩
    · cases op <;> cases c <;> simp
    · cases op <;> cases c <;> simp [ioRv,bin]
  · rcases b with d | j
    · refine ⟨[], if d = op then .inr i else .inl d, by simp, by simp, ?_, ?_⟩
      · cases op <;> cases d <;> simp
      · cases op <;> cases d <;> simp [ioRv,bin]
    · let q : Gate := ⟨if op then GateOp.and else GateOp.or, [i,j]⟩
      refine ⟨[q], .inr (n+hs.length), by cases op <;> simp [q,ioOK], by simp, by simp, ?_⟩
      intro x
      have hl : (ioRun hs (List.ofFn x)).length = n+hs.length := by simp [ioLen]
      simp only [ioRv]
      rw [ioSnoc, ← hl, ioLast]
      cases op <;> simp [q,bin,GateOp.eval]

theorem ioCompile {n H : ℕ} {S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} (hg : Good H S g) (k : ℕ) :
    ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ q ∈ hs, ioOK q) ∧
      hs.length ≤ (S.filter (· < k)).card ∧
      (∀ w < k, ∀ t, m w = .inr t → t < n+hs.length) ∧
      ∀ w < k, ∀ x : Fin n → Bool, ioRv (ioRun hs (List.ofFn x)) (m w) = val S g (ioBits x) w := by
  induction k with
  | zero => exact ⟨[], fun _ => .inl false, by simp, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨hs,m,hok,hlen,hb,he⟩ := ih
    have step : ∃ (e : List Gate) (r : Bool ⊕ ℕ), (∀ q ∈ e, ioOK q) ∧
        hs.length+e.length ≤ (S.filter (· < k+1)).card ∧
        (∀ t, r = .inr t → t < n+hs.length+e.length) ∧
        ∀ x : Fin n → Bool, ioRv (ioRun (hs++e) (List.ofFn x)) r = val S g (ioBits x) k := by
      by_cases hk : k ∈ S
      · have ha := (hg k hk).2
        obtain ⟨e,r,h1,h2,h3,h4⟩ := ioEmit n hs (g k).1 (m (g k).2.1) (m (g k).2.2)
        have hf : S.filter (· < k+1) = insert k (S.filter (· < k)) := by
          ext i
          by_cases heq : i = k
          · subst i; simp [hk]
          · simp only [Finset.mem_filter, Finset.mem_insert, heq, false_or]
            rw [show i < k+1 ↔ i < k by omega]
        refine ⟨e,r,h1,?_, h3 (hb _ ha.1) (hb _ ha.2), ?_⟩
        · rw [hf,Finset.card_insert_of_notMem (by simp)]; omega
        · intro x; rw [h4,he _ ha.1,he _ ha.2,vin hg hk]
      · refine ⟨[], ioSeed n k, by simp, ?_, ?_, ?_⟩
        · simp only [List.length_nil,Nat.add_zero]
          apply hlen.trans (Finset.card_le_card ?_)
          intro i hi
          obtain ⟨him,hik⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨him, by omega⟩
        · intro t ht
          unfold ioSeed at ht
          split_ifs at ht with h z
          cases ht; simp; omega
        · intro x
          rw [List.append_nil,vout hk]
          unfold ioBits ioSeed
          split_ifs with h z
          · rfl
          · exact ioInput _ _ _ (by simpa using z.2)
          · rfl
    obtain ⟨e,r,hq,hl,hr,hev⟩ := step
    refine ⟨hs++e,Function.update m k r,fun q h => (List.mem_append.mp h).elim (hok q) (hq q),
      by simpa using hl, ?_, ?_⟩
    · intro w hw t ht
      by_cases h : w = k
      · subst w; simpa [Function.update_self,List.length_append,Nat.add_assoc] using hr t (by simpa using ht)
      · rw [Function.update_of_ne h] at ht
        have := hb w (by omega) t ht
        rw [List.length_append]; omega
    · intro w hw x
      by_cases h : w = k
      · subst w; simpa using hev x
      · rw [Function.update_of_ne h, ← he w (by omega) x]
        cases hmw : m w with
        | inl b => rfl
        | inr t => exact ioPrefix _ _ _ _ (by simpa using hb w (by omega) t hmw)

theorem ioMonobin {a b c d : Bool} (op : Bool) (h1 : a ≤ c) (h2 : b ≤ d) :
    bin op a b ≤ bin op c d := by
  cases op <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all [bin]

theorem ioMono {H : ℕ} {S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} (hg : Good H S g) {a b : ℕ → Bool}
    (h : ∀ i, a i ≤ b i) (w : ℕ) : val S g a w ≤ val S g b w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w ∈ S
    · rw [vin hg hw,vin hg hw]
      exact ioMonobin _ (ih _ (hg _ hw).2.1) (ih _ (hg _ hw).2.2)
    · simpa [vout hw] using h w

def ioPt {n : ℕ} (a b i : Fin n) := decide (i=a ∨ i=b)

theorem ioPairBits {n : ℕ} (a b : Fin n) : ioBits (ioPt a b) = point ∅ a b := by
  funext w
  unfold ioBits ioSeed
  split_ifs with h h
  · simp [ioRv,point,h]
  · have hi : (w-2)/2 < (List.ofFn (ioPt a b)).length := by simpa using h.2
    simp only [ioRv,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some,
      List.getElem_ofFn,ioPt,Fin.ext_iff,point,Finset.notMem_empty,not_false_eq_true,true_and,decide_eq_decide,lport,rport]
    omega
  · simp only [ioRv,point,lport,rport,Finset.notMem_empty,not_false_eq_true,true_and]
    symm
    apply decide_eq_false
    have := a.isLt; have := b.isLt; omega

theorem ioBitsMono {n : ℕ} {x y : Fin n → Bool} (h : ∀ i, x i ≤ y i) (w : ℕ) : ioBits x w ≤ ioBits y w := by
  unfold ioBits ioSeed
  split_ifs with h0 hi
  · exact le_rfl
  · have h₁ : (w-2)/2 < (List.ofFn x).length := by simpa using hi.2
    have h₂ : (w-2)/2 < (List.ofFn y).length := by simpa using hi.2
    simpa only [ioRv,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h₁,List.getElem?_eq_getElem h₂,
      Option.getD_some,List.getElem_ofFn] using h ⟨(w-2)/2,hi.2⟩
  · exact le_rfl

theorem ioTo {n : ℕ} (hn : 2 ≤ n) {S : Finset ℕ} {g : (ℕ → Bool × ℕ × ℕ)} {o : ℕ}
    (hg : Good (2*n+2) S g) (hs : Solves (Finset.range n) ∅ S g o) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ S.card ∧
      (∀ x : Fin n → Bool, (List.ofFn x).count true = 2 → C.eval (List.ofFn x) = true) ∧
      (∀ x : Fin n → Bool, (List.ofFn x).count true ≤ 1 → C.eval (List.ofFn x) = false) := by
  classical
  have pair (a b : Fin n) : val S g (ioBits (ioPt a b)) o = decide (a ≠ b) := by
    rw [ioPairBits]
    simpa [Fin.ext_iff] using hs a (Finset.mem_range.mpr a.isLt) b (Finset.mem_range.mpr b.isLt)
  obtain ⟨qs,m,hok,hlen,_,he⟩ := ioCompile (n:=n) hg (o+1)
  have ev := he o (by omega)
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  have ab : a ≠ b := by simp [a,b]
  cases hm : m o with
  | inl c =>
    have v0 := ev (ioPt a a)
    have v1 := ev (ioPt a b)
    simp [hm,ioRv,pair,ab] at v0 v1
    simp_all
  | inr t =>
    let C : Circuit := ⟨qs,t⟩
    have hval (x : Fin n → Bool) : C.eval (List.ofFn x) = val S g (ioBits x) o := by
      simpa [hm,ioRv,C,Circuit.eval,Circuit.wires,ioRun] using ev x
    refine ⟨C,fun q hq => ⟨by simpa using (hok q hq).1,(hok q hq).2⟩,
      hlen.trans (Finset.card_le_card (Finset.filter_subset _ _)), ?_, ?_⟩
    · intro x hx
      rw [List.count_ofFn] at hx
      obtain ⟨i,j,hij,heq⟩ := Finset.card_eq_two.mp hx
      have ex : x = ioPt i j := by
        funext k
        have hk := Finset.ext_iff.mp heq k
        simp at hk
        cases hb : x k <;> simp_all [ioPt]
      rw [ex,hval,pair]; simp [hij]
    · intro x hx
      rw [List.count_ofFn] at hx
      let _ : Nonempty (Fin n) := ⟨a⟩
      obtain ⟨i,hi⟩ := Finset.card_le_one_iff_subset_singleton.mp hx
      have bound (j : Fin n) : x j ≤ ioPt i i j := by
        cases hj : x j
        · simp
        · have eq : j = i := by simpa using hi (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)
          simp [ioPt,eq]
      have h := ioMono hg (ioBitsMono bound) o
      rw [pair] at h
      rw [hval]
      exact le_antisymm (by simpa using h) (Bool.false_le _)

end PEqualNP.Outside.L_meta_18677_aux


namespace PEqualNP.Outside.L_meta_18677_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem crown_discount_18508 :
    ∀ n s : ℕ, 2 ≤ n →
      RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s →
      ∃ C : Circuit, Monotone2 C ∧ C.size + n ≤ s ∧
        (∀ x : Fin n → Bool, (List.ofFn x).count true = 2 → C.eval (List.ofFn x) = true) ∧
        (∀ x : Fin n → Bool, (List.ofFn x).count true ≤ 1 → C.eval (List.ofFn x) = false) := by
  intro n s hn hr
  obtain ⟨S, g, o, hg, hs, cs⟩ := ioFrom hn hr
  obtain ⟨T, h, p, ht, hp, ct⟩ := discount (n := n)
    (K := Finset.range n) (M := Finset.range n) (fun _ h => h) (fun _ h => h) (by simpa using hn) hg hs
  obtain ⟨C, hC, hsize, hpos, hneg⟩ := ioTo hn ht hp
  simp only [Finset.card_range] at ct
  exact ⟨C, hC, by omega, hpos, hneg⟩

def shiftGates (L : ℕ) (gs : List Gate) : List Gate :=
  gs.map fun g => ⟨g.op, g.inputs.map (L + ·)⟩

theorem ioRun_shift (L : ℕ) (gs : List Gate) (pref x : List Bool) (hL : pref.length = L) :
    ioRun (shiftGates L gs) (pref ++ x) = pref ++ ioRun gs x := by
  induction gs using List.reverseRecOn with
  | nil => simp [shiftGates, ioRun]
  | append_singleton gs g ih =>
    have hmap : shiftGates L (gs ++ [g]) = shiftGates L gs ++ [⟨g.op, g.inputs.map (L + ·)⟩] := by
      simp [shiftGates]
    rw [hmap, ioSnoc, ioSnoc, ih, List.append_assoc]
    congr 2
    have hget : ∀ i : ℕ, (pref ++ ioRun gs x).getD (L + i) false = (ioRun gs x).getD i false := by
      intro i
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : pref.length ≤ L + i), hL]
    congr 1
    apply congrArg g.op.eval
    rw [List.map_map]
    exact List.map_congr_left fun i _ => hget i

def pairOrGates (n : ℕ) : List Gate :=
  List.ofFn fun a : Fin n => ⟨GateOp.or, [a.val, n + a.val]⟩

theorem pairOrGates_mon (n : ℕ) : ∀ q ∈ pairOrGates n, (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ q.inputs.length ≤ 2 := by
  intro q hq
  simp [pairOrGates] at hq
  rcases hq with ⟨a, rfl⟩
  simp

theorem pairOrGates_eval (n : ℕ) (u v : Fin n) :
    ioRun (pairOrGates n) (oneEach u v) = oneEach u v ++ List.ofFn (fun a : Fin n => decide (a = u ∨ a = v)) := by
  have hlen : (ioRun (pairOrGates n) (oneEach u v)).length = (oneEach u v ++ List.ofFn (fun a : Fin n => decide (a = u ∨ a = v))).length := by
    simp [ioLen, pairOrGates, oneEach]; omega
  apply List.ext_getElem hlen
  intro i hi1 hi2
  have hxl : (oneEach u v).length = 2 * n := by simp [oneEach]; omega
  have hget : ∀ k, (ioRun (pairOrGates n) (oneEach u v)).getD k false =
      (oneEach u v ++ List.ofFn (fun a : Fin n => decide (a = u ∨ a = v))).getD k false := by
    intro k
    by_cases hk : k < 2 * n
    · rw [ioInput (pairOrGates n) (oneEach u v) k (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : k < (oneEach u v).length)]
    · by_cases hk2 : k < 3 * n
      · let j := k - 2 * n
        have hjlt : j < n := by omega
        have hj : j < (pairOrGates n).length := by simp [pairOrGates, hjlt]
        have hkj : (oneEach u v).length + j = k := by omega
        rw [← hkj, ioGate (pairOrGates n) (oneEach u v) j hj]
        have hgj : (pairOrGates n)[j] = ⟨GateOp.or, [j, n + j]⟩ := by simp [pairOrGates]
        rw [hgj]
        have hj1 : j < (oneEach u v).length + j := by omega
        have hj2 : n + j < (oneEach u v).length + j := by omega
        have hi_a : (ioRun (pairOrGates n) (oneEach u v)).getD j false = decide (⟨j, hjlt⟩ = u) := by
          rw [ioInput _ _ j (by omega)]
          have h1 : j < (List.ofFn fun x : Fin n => decide (x = u)).length := by simp [hjlt]
          simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left h1, hjlt]
        have hi_b : (ioRun (pairOrGates n) (oneEach u v)).getD (n + j) false = decide (⟨j, hjlt⟩ = v) := by
          rw [ioInput _ _ (n + j) (by omega)]
          have h1 : (List.ofFn fun x : Fin n => decide (x = u)).length ≤ n + j := by simp
          simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right h1, hjlt]
        simp only [List.map_cons, List.map_nil, hj1, hj2, ↓reduceIte, hi_a, hi_b, GateOp.eval]
        have hrhs : (oneEach u v ++ List.ofFn (fun a : Fin n => decide (a = u ∨ a = v))).getD ((oneEach u v).length + j) false =
            decide ((⟨j, hjlt⟩ : Fin n) = u ∨ (⟨j, hjlt⟩ : Fin n) = v) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _), hjlt]
        rw [hrhs]
        cases hdu : decide ((⟨j, hjlt⟩ : Fin n) = u) <;> cases hdv : decide ((⟨j, hjlt⟩ : Fin n) = v) <;>
          simp_all [decide_eq_true_iff]
      · rw [List.getD_eq_default _ _ (by rw [ioLen, hxl]; simp [pairOrGates]; omega),
            List.getD_eq_default _ _ (by simp [hxl]; omega)]
  have hgi := hget i
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at hgi
  simpa using hgi

def simpleTh2Step (n : ℕ) : ℕ → List Gate
  | 0 => [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 1]⟩]
  | k + 1 =>
    let prev := simpleTh2Step n k
    let base := n + prev.length
    let s1 := base - 2
    let s2 := base - 1
    let w := k + 2
    prev ++ [⟨GateOp.and, [s1, w]⟩, ⟨GateOp.or, [s1, w]⟩, ⟨GateOp.or, [s2, base]⟩]

theorem simpleTh2Step_mon (n k : ℕ) : ∀ q ∈ simpleTh2Step n k, (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ q.inputs.length ≤ 2 := by
  induction k with
  | zero => intro q hq; simp [simpleTh2Step] at hq; rcases hq with rfl | rfl <;> simp
  | succ k ih =>
    intro q hq
    simp [simpleTh2Step] at hq
    rcases hq with h | rfl | rfl | rfl
    · exact ih q h
    · simp
    · simp
    · simp

theorem simpleTh2Step_len (n k : ℕ) : (simpleTh2Step n k).length = 3 * k + 2 := by
  induction k with
  | zero => simp [simpleTh2Step]
  | succ k ih => simp [simpleTh2Step, ih]; omega

theorem simpleTh2Step_spec (n : ℕ) (x : Fin n → Bool) : ∀ k (hk : k + 1 < n),
    (ioRun (simpleTh2Step n k) (List.ofFn x)).getD (n + (simpleTh2Step n k).length - 2) false =
      decide (∃ i : Fin n, i.val ≤ k + 1 ∧ x i = true) ∧
    (ioRun (simpleTh2Step n k) (List.ofFn x)).getD (n + (simpleTh2Step n k).length - 1) false =
      decide (∃ i j : Fin n, i.val < j.val ∧ j.val ≤ k + 1 ∧ x i = true ∧ x j = true) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : 0 < n := by omega
    have h1 : 1 < n := by omega
    have ha : (List.ofFn x).getD 0 false = x ⟨0, h0⟩ := by
      simp [List.getD_eq_getElem?_getD, h0]
    have hb : (List.ofFn x).getD 1 false = x ⟨1, h1⟩ := by
      simp [List.getD_eq_getElem?_getD, h1]
    have hrun : ioRun (simpleTh2Step n 0) (List.ofFn x) =
        List.ofFn x ++ [x ⟨0, h0⟩ || x ⟨1, h1⟩, x ⟨0, h0⟩ && x ⟨1, h1⟩] := by
      have ha' : (List.ofFn x ++ [x ⟨0, h0⟩ || x ⟨1, h1⟩]).getD 0 false = x ⟨0, h0⟩ := by
        rw [ioGet _ _ 0 (by simpa using h0), ha]
      have hb' : (List.ofFn x ++ [x ⟨0, h0⟩ || x ⟨1, h1⟩]).getD 1 false = x ⟨1, h1⟩ := by
        rw [ioGet _ _ 1 (by simpa using h1), hb]
      change ((List.ofFn x ++ [GateOp.or.eval ([0, 1].map fun i => (List.ofFn x).getD i false)]) ++
        [GateOp.and.eval ([0, 1].map fun i => (List.ofFn x ++ [GateOp.or.eval ([0, 1].map fun i => (List.ofFn x).getD i false)]).getD i false)]) = _
      have hg1 : GateOp.or.eval ([0, 1].map fun i => (List.ofFn x).getD i false) = (x ⟨0, h0⟩ || x ⟨1, h1⟩) := by
        simp only [List.map_cons, List.map_nil, ha, hb]
        simp [GateOp.eval]
      rw [hg1]
      have hg2 : GateOp.and.eval ([0, 1].map fun i => (List.ofFn x ++ [x ⟨0, h0⟩ || x ⟨1, h1⟩]).getD i false) = (x ⟨0, h0⟩ && x ⟨1, h1⟩) := by
        simp only [List.map_cons, List.map_nil, ha', hb']
        simp [GateOp.eval]
      rw [hg2]
      simp [List.append_assoc]
    have hlen : (simpleTh2Step n 0).length = 2 := rfl
    rw [hlen, hrun]
    constructor
    · have hp : (List.ofFn x ++ [x ⟨0, h0⟩ || x ⟨1, h1⟩, x ⟨0, h0⟩ && x ⟨1, h1⟩]).getD (n + 2 - 2) false =
          (x ⟨0, h0⟩ || x ⟨1, h1⟩) := by
        have hidx : n + 2 - 2 = (List.ofFn x).length := by simp
        rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
        simp
      rw [hp]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h | h)
        · exact ⟨⟨0, h0⟩, by simp, h⟩
        · exact ⟨⟨1, h1⟩, by simp, h⟩
      · rintro ⟨i, hi, hxi⟩
        have hcases : i = ⟨0, h0⟩ ∨ i = ⟨1, h1⟩ := by
          rcases Nat.lt_or_eq_of_le hi with hlt | heq
          · left; apply Fin.ext; simp; omega
          · right; apply Fin.ext; simp; omega
        rcases hcases with rfl | rfl
        · exact Or.inl hxi
        · exact Or.inr hxi
    · have hp : (List.ofFn x ++ [x ⟨0, h0⟩ || x ⟨1, h1⟩, x ⟨0, h0⟩ && x ⟨1, h1⟩]).getD (n + 2 - 1) false =
          (x ⟨0, h0⟩ && x ⟨1, h1⟩) := by
        have hidx : n + 2 - 1 = (List.ofFn x).length + 1 := by simp
        rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp
      rw [hp]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hx0, hx1⟩
        exact ⟨⟨0, h0⟩, ⟨1, h1⟩, by simp, by simp, hx0, hx1⟩
      · rintro ⟨i, j, hij, hj, hxi, hxj⟩
        have hi0 : i = ⟨0, h0⟩ := by apply Fin.ext; simp; omega
        have hj1 : j = ⟨1, h1⟩ := by apply Fin.ext; simp; omega
        exact ⟨hi0 ▸ hxi, hj1 ▸ hxj⟩
  | succ k ih =>
    intro hk
    obtain ⟨hs1, hs2⟩ := ih (by omega)
    let prev := simpleTh2Step n k
    let w0 := ioRun prev (List.ofFn x)
    have hplen : prev.length = 3 * k + 2 := simpleTh2Step_len n k
    have hw0len : w0.length = n + prev.length := by simp [w0, ioLen]
    have hkw : k + 2 < n := by omega
    have hw_val : w0.getD (k + 2) false = x ⟨k + 2, hkw⟩ := by
      rw [ioInput prev (List.ofFn x) (k + 2) (by simpa using hkw)]
      simp [List.getD_eq_getElem?_getD, hkw]
    let b1 := w0.getD (n + prev.length - 2) false
    let b2 := w0.getD (n + prev.length - 1) false
    let bw := x ⟨k + 2, hkw⟩
    have hrun : ioRun (simpleTh2Step n (k + 1)) (List.ofFn x) =
        w0 ++ [b1 && bw, b1 || bw, b2 || (b1 && bw)] := by
      have h1 : n + prev.length - 2 < w0.length := by omega
      have h2 : n + prev.length - 1 < w0.length := by omega
      have h3 : k + 2 < w0.length := by omega
      have heq : simpleTh2Step n (k + 1) =
          prev ++ [⟨GateOp.and, [n + prev.length - 2, k + 2]⟩,
                   ⟨GateOp.or, [n + prev.length - 2, k + 2]⟩,
                   ⟨GateOp.or, [n + prev.length - 1, n + prev.length]⟩] := rfl
      rw [heq, ioRun, List.foldl_append]
      change (((w0 ++ [(GateOp.and.eval ([n + prev.length - 2, k + 2].map fun i => w0.getD i false))]) ++
        [(GateOp.or.eval ([n + prev.length - 2, k + 2].map fun i => (w0 ++ [GateOp.and.eval ([n + prev.length - 2, k + 2].map fun i => w0.getD i false)]).getD i false))]) ++
        [(GateOp.or.eval ([n + prev.length - 1, n + prev.length].map fun i => ((w0 ++ [GateOp.and.eval ([n + prev.length - 2, k + 2].map fun i => w0.getD i false)]) ++ [GateOp.or.eval ([n + prev.length - 2, k + 2].map fun i => (w0 ++ [GateOp.and.eval ([n + prev.length - 2, k + 2].map fun i => w0.getD i false)]).getD i false)]).getD i false))]) = _
      have ha1 : (GateOp.and.eval ([n + prev.length - 2, k + 2].map fun i => w0.getD i false)) = (b1 && bw) := by
        simp only [List.map_cons, List.map_nil, hw_val]
        simp [GateOp.eval, b1, bw]
      rw [ha1]
      have ha2 : (GateOp.or.eval ([n + prev.length - 2, k + 2].map fun i => (w0 ++ [b1 && bw]).getD i false)) = (b1 || bw) := by
        simp only [List.map_cons, List.map_nil, ioGet _ _ _ h1, ioGet _ _ _ h3, hw_val]
        simp [GateOp.eval, b1, bw]
      rw [ha2]
      have ha3 : (GateOp.or.eval ([n + prev.length - 1, n + prev.length].map fun i => ((w0 ++ [b1 && bw]) ++ [b1 || bw]).getD i false)) = (b2 || (b1 && bw)) := by
        have hget1 : ((w0 ++ [b1 && bw]) ++ [b1 || bw]).getD (n + prev.length - 1) false = b2 := by
          rw [ioGet _ _ _ (by simp; omega), ioGet _ _ _ h2]
        have hget2 : ((w0 ++ [b1 && bw]) ++ [b1 || bw]).getD (n + prev.length) false = (b1 && bw) := by
          rw [ioGet _ _ _ (by simp; omega), ← hw0len, ioLast]
        simp only [List.map_cons, List.map_nil, hget1, hget2]
        simp [GateOp.eval]
      rw [ha3]
      simp [List.append_assoc]
    have hlen2 : (simpleTh2Step n (k + 1)).length = prev.length + 3 := by
      simp [simpleTh2Step_len, hplen]; omega
    rw [hlen2, hrun]
    have hidx1 : n + (prev.length + 3) - 2 = w0.length + 1 := by omega
    have hidx2 : n + (prev.length + 3) - 1 = w0.length + 2 := by omega
    constructor
    · rw [hidx1, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      have hb1 : b1 = decide (∃ i : Fin n, i.val ≤ k + 1 ∧ x i = true) := hs1
      rw [hb1]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq, bw]
      constructor
      · rintro (⟨i, hi, hxi⟩ | hxk)
        · exact ⟨i, by omega, hxi⟩
        · exact ⟨⟨k + 2, hkw⟩, by simp, hxk⟩
      · rintro ⟨i, hi, hxi⟩
        by_cases hle : i.val ≤ k + 1
        · exact Or.inl ⟨i, hle, hxi⟩
        · have heq : i = ⟨k + 2, hkw⟩ := by apply Fin.ext; simp; omega
          exact Or.inr (heq ▸ hxi)
    · rw [hidx2, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      have hb1 : b1 = decide (∃ i : Fin n, i.val ≤ k + 1 ∧ x i = true) := hs1
      have hb2 : b2 = decide (∃ i j : Fin n, i.val < j.val ∧ j.val ≤ k + 1 ∧ x i = true ∧ x j = true) := hs2
      rw [hb1, hb2]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bw]
      constructor
      · rintro (⟨i, j, hij, hj, hxi, hxj⟩ | ⟨⟨i, hi, hxi⟩, hxk⟩)
        · exact ⟨i, j, hij, by omega, hxi, hxj⟩
        · exact ⟨i, ⟨k + 2, hkw⟩, by simp; omega, by simp, hxi, hxk⟩
      · rintro ⟨i, j, hij, hj, hxi, hxj⟩
        by_cases hle : j.val ≤ k + 1
        · exact Or.inl ⟨i, j, hij, hle, hxi, hxj⟩
        · have heq : j = ⟨k + 2, hkw⟩ := by apply Fin.ext; simp; omega
          exact Or.inr ⟨⟨i, by omega, hxi⟩, heq ▸ hxj⟩

theorem crown_exists (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : ℕ, RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s := by
  let gsD := simpleTh2Step n (n - 2)
  let outD := n + gsD.length - 1
  let gsC := pairOrGates n ++ shiftGates (2 * n) gsD
  let C : Circuit := ⟨gsC, 2 * n + outD⟩
  refine ⟨C.size, C, ?_, le_rfl, ?_⟩
  · intro q hq
    simp only [C, gsC, List.mem_append] at hq
    rcases hq with h1 | h2
    · exact pairOrGates_mon n q h1
    · simp only [shiftGates, List.mem_map] at h2
      rcases h2 with ⟨q', hq', rfl⟩
      have hm := simpleTh2Step_mon n (n - 2) q' hq'
      exact ⟨hm.1, by simpa using hm.2⟩
  · intro u v
    have hrun : C.wires (oneEach u v) = oneEach u v ++ ioRun gsD (List.ofFn fun a : Fin n => decide (a = u ∨ a = v)) := by
      change ioRun (pairOrGates n ++ shiftGates (2 * n) gsD) (oneEach u v) = _
      rw [ioRun, List.foldl_append]
      change ioRun (shiftGates (2 * n) gsD) (ioRun (pairOrGates n) (oneEach u v)) = _
      rw [pairOrGates_eval, ioRun_shift (2 * n) gsD (oneEach u v) _ (by simp [oneEach]; omega)]
    change (C.wires (oneEach u v)).getD (2 * n + outD) false = decide (u ≠ v)
    rw [hrun]
    have hlen1 : (oneEach u v).length = 2 * n := by simp [oneEach]; omega
    have hget : (oneEach u v ++ ioRun gsD (List.ofFn fun a : Fin n => decide (a = u ∨ a = v))).getD (2 * n + outD) false =
        (ioRun gsD (List.ofFn fun a : Fin n => decide (a = u ∨ a = v))).getD outD false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : (oneEach u v).length ≤ 2 * n + outD), hlen1]
    rw [hget]
    have hspec := (simpleTh2Step_spec n (fun a : Fin n => decide (a = u ∨ a = v)) (n - 2) (by omega)).2
    rw [hspec]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨i, j, hij, _, hi, hj⟩
      intro huv; subst huv
      have : i = u := by tauto
      have : j = u := by tauto
      omega
    · intro huv
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne huv) with h | h
      · exact ⟨u, v, h, by omega, Or.inl rfl, Or.inr rfl⟩
      · exact ⟨v, u, h, by omega, Or.inr rfl, Or.inl rfl⟩

end PEqualNP.Outside.L_meta_18677_aux

theorem PEqualNP.Outside.L_meta_18677 : ∀ n : ℕ, 2 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide (u ≠ v)) C ∧ (∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' → PEqualNP.Represents.Represents (fun u v : Fin n => decide (u ≠ v)) C' → C.size ≤ C'.size) ∧ ∀ a < n, ∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.toFinset = {a, n + a} := by
  classical
  intro n hn
  have hex := PEqualNP.Outside.L_meta_18677_aux.crown_exists n hn
  let sMin := Nat.find hex
  have hrepMin : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) sMin := Nat.find_spec hex
  obtain ⟨D, hDmon, hDsz, hDpos, hDneg⟩ := PEqualNP.Outside.L_meta_18677_aux.crown_discount_18508 n sMin hn hrepMin
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨PEqualNP.Outside.L_meta_18677_aux.pairOrGates n ++ PEqualNP.Outside.L_meta_18677_aux.shiftGates (2 * n) D.gates,
     2 * n + D.output⟩
  have hCmon : PEqualNP.MetaComplexity.Monotone2 C := by
    intro q hq
    simp only [C, List.mem_append] at hq
    rcases hq with h1 | h2
    · exact PEqualNP.Outside.L_meta_18677_aux.pairOrGates_mon n q h1
    · simp only [PEqualNP.Outside.L_meta_18677_aux.shiftGates, List.mem_map] at h2
      rcases h2 with ⟨q', hq', rfl⟩
      have hm := hDmon q' hq'
      exact ⟨hm.1, by simpa using hm.2⟩
  have hCsz : C.size ≤ sMin := by
    have : C.size = n + D.size := by
      simp [C, PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_18677_aux.pairOrGates,
        PEqualNP.Outside.L_meta_18677_aux.shiftGates]
    omega
  have hCrep : PEqualNP.Represents.Represents (fun u v : Fin n => decide (u ≠ v)) C := by
    intro u v
    let z : Fin n → Bool := fun a => decide (a = u ∨ a = v)
    have hrun : C.wires (PEqualNP.Represents.oneEach u v) =
        PEqualNP.Represents.oneEach u v ++ PEqualNP.Outside.L_meta_18677_aux.ioRun D.gates (List.ofFn z) := by
      change PEqualNP.Outside.L_meta_18677_aux.ioRun
        (PEqualNP.Outside.L_meta_18677_aux.pairOrGates n ++ PEqualNP.Outside.L_meta_18677_aux.shiftGates (2 * n) D.gates)
        (PEqualNP.Represents.oneEach u v) = _
      rw [PEqualNP.Outside.L_meta_18677_aux.ioRun, List.foldl_append]
      change PEqualNP.Outside.L_meta_18677_aux.ioRun (PEqualNP.Outside.L_meta_18677_aux.shiftGates (2 * n) D.gates)
        (PEqualNP.Outside.L_meta_18677_aux.ioRun (PEqualNP.Outside.L_meta_18677_aux.pairOrGates n) (PEqualNP.Represents.oneEach u v)) = _
      rw [PEqualNP.Outside.L_meta_18677_aux.pairOrGates_eval,
        PEqualNP.Outside.L_meta_18677_aux.ioRun_shift (2 * n) D.gates (PEqualNP.Represents.oneEach u v) _
          (by simp [PEqualNP.Represents.oneEach]; omega)]
    change (C.wires (PEqualNP.Represents.oneEach u v)).getD (2 * n + D.output) false = decide (u ≠ v)
    rw [hrun]
    have hlen1 : (PEqualNP.Represents.oneEach u v).length = 2 * n := by simp [PEqualNP.Represents.oneEach]; omega
    have hget : (PEqualNP.Represents.oneEach u v ++ PEqualNP.Outside.L_meta_18677_aux.ioRun D.gates (List.ofFn z)).getD (2 * n + D.output) false =
        D.eval (List.ofFn z) := by
      change _ = (PEqualNP.Outside.L_meta_18677_aux.ioRun D.gates (List.ofFn z)).getD D.output false
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : (PEqualNP.Represents.oneEach u v).length ≤ 2 * n + D.output), hlen1]
    rw [hget]
    by_cases huv : u = v
    · subst huv
      have hcnt : (List.ofFn z).count true ≤ 1 := by
        rw [List.count_ofFn]
        have hsub : (Finset.univ.filter fun a : Fin n => z a = true) = {u} := by
          ext a; simp [z]
        rw [hsub]; simp
      simpa using hDneg z hcnt
    · have hcnt : (List.ofFn z).count true = 2 := by
        rw [List.count_ofFn]
        have hsub : (Finset.univ.filter fun a : Fin n => z a = true) = {u, v} := by
          ext a; simp [z]
        rw [hsub, Finset.card_pair huv]
      simpa [huv] using hDpos z hcnt
  refine ⟨C, hCmon, hCrep, ?_, ?_⟩
  · intro C' hC'mon hC'rep
    have hle : sMin ≤ C'.size := Nat.find_min' hex ⟨C', hC'mon, le_rfl, hC'rep⟩
    omega
  · intro a ha
    have hlt : a < (PEqualNP.Outside.L_meta_18677_aux.pairOrGates n).length := by
      simp [PEqualNP.Outside.L_meta_18677_aux.pairOrGates, ha]
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C a = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, n + a]⟩ := by
      rw [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD]
      change (PEqualNP.Outside.L_meta_18677_aux.pairOrGates n ++ PEqualNP.Outside.L_meta_18677_aux.shiftGates (2 * n) D.gates)[a]?.getD _ = _
      rw [List.getElem?_append_left hlt]
      simp [PEqualNP.Outside.L_meta_18677_aux.pairOrGates, ha]
    refine ⟨a, ?_, ?_, ?_⟩
    · simp [C, PEqualNP.Outside.L_meta_18677_aux.pairOrGates]; omega
    · rw [hgate]
    · rw [hgate]; simp
