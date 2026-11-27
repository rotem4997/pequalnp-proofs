import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8309_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

abbrev Wire (n : ℕ) := Finset (Fin n) → Bool
abbrev Paint (n : ℕ) := Fin n → Fin n → ℕ

def zeroW {n : ℕ} : Wire n := fun _ => false
def oneW {n : ℕ} : Wire n := fun _ => true
def meetW {n : ℕ} (s t : Wire n) : Wire n := fun X => s X && t X
def joinW {n : ℕ} (s t : Wire n) : Wire n := fun X => s X || t X

def negSet {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (c : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun p => ¬ R c p)

def monoW {n : ℕ} (s : Wire n) : Prop :=
  ∀ X Y : Finset (Fin n), X ⊆ Y → s X = true → s Y = true

def uniform {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (f : Paint n) (s : Wire n) : Prop :=
  ∀ c : Fin n, s (negSet R c) = false → ∀ p q : Fin n,
    s {p} = true → s {q} = true → f c p = f c q

def mergePaint {n : ℕ} (f : Paint n) (c : Fin n) (a b : ℕ) : Paint n :=
  fun d p => if d = c ∧ f d p = a then b else f d p

def palette {n : ℕ} (U : Finset (Fin n × Fin n)) (f : Paint n) : Finset (Fin n × ℕ) :=
  U.image (fun z => (z.1, f z.1 z.2))

def coarser {n : ℕ} (f g : Paint n) : Prop :=
  ∀ c p q, f c p = f c q → g c p = g c q

theorem and_true_iff {a b : Bool} : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem or_true_iff {a b : Bool} : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem valid_rel {n : ℕ} {R : Fin n → Fin n → Prop} [DecidableRel R] {s : Wire n}
    (ms : monoW s) {c p : Fin n} (hoff : s (negSet R c) = false) (hon : s {p} = true) :
    R c p := by
  by_contra hnr
  have hsub : ({p} : Finset (Fin n)) ⊆ negSet R c := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnr⟩
  have hup := ms {p} (negSet R c) hsub hon
  rw [hoff] at hup
  cases hup

theorem after_merge {n : ℕ} (f : Paint n) (c : Fin n) (a b : ℕ) :
    coarser f (mergePaint f c a b) := by
  intro d p q heq
  simp [mergePaint, heq]

theorem palette_bound {n : ℕ} (U : Finset (Fin n × Fin n)) (f : Paint n) (c : Fin n) (a b : ℕ) :
    (palette U f).card ≤ (palette U (mergePaint f c a b)).card + 1 := by
  classical
  have hsub : palette U f ⊆ insert (c, a) (palette U (mergePaint f c a b)) := by
    intro z hz
    obtain ⟨⟨d, p⟩, hdp, rfl⟩ := Finset.mem_image.mp hz
    by_cases hmov : d = c ∧ f d p = a
    · exact Finset.mem_insert.mpr (Or.inl (Prod.ext hmov.1 hmov.2))
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨(d, p), hdp, by simp [mergePaint, hmov]⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

theorem mono_meet {n : ℕ} {s t : Wire n} (ms : monoW s) (mt : monoW t) :
    monoW (meetW s t) := by
  intro X Y hXY hon
  obtain ⟨hs, ht⟩ := and_true_iff.mp hon
  exact and_true_iff.mpr ⟨ms X Y hXY hs, mt X Y hXY ht⟩

theorem mono_join {n : ℕ} {s t : Wire n} (ms : monoW s) (mt : monoW t) :
    monoW (joinW s t) := by
  intro X Y hXY hon
  exact or_true_iff.mpr ((or_true_iff.mp hon).imp (ms X Y hXY) (mt X Y hXY))

theorem kept_uniform {n : ℕ} {R : Fin n → Fin n → Prop} [DecidableRel R] {f h : Paint n}
    {s : Wire n} (us : uniform R f s) (hc : coarser f h) : uniform R h s := by
  intro c hoff p q hp hq
  exact hc c p q (us c hoff p q hp hq)

theorem meet_uniform {n : ℕ} {R : Fin n → Fin n → Prop} [DecidableRel R] {f : Paint n}
    {s t : Wire n} (us : uniform R f s) (ut : uniform R f t) :
    uniform R f (meetW s t) := by
  intro c hoff p q hp hq
  obtain ⟨p1, p2⟩ := and_true_iff.mp hp
  obtain ⟨q1, q2⟩ := and_true_iff.mp hq
  cases hs : s (negSet R c) with
  | false => exact us c hs p q p1 q1
  | true =>
    have ht : t (negSet R c) = false := by simpa [meetW, hs] using hoff
    exact ut c ht p q p2 q2

theorem two_labels {n : ℕ} {s t : Wire n} {c : Fin n} {f : Paint n}
    (asame : ∀ p q, s {p} = true → s {q} = true → f c p = f c q)
    (bsame : ∀ p q, t {p} = true → t {q} = true → f c p = f c q)
    {p q : Fin n} (pon : joinW s t {p} = true) (qon : joinW s t {q} = true)
    (hne : f c p ≠ f c q) :
    ∀ r, joinW s t {r} = true → f c r = f c p ∨ f c r = f c q := by
  intro r hron
  rcases or_true_iff.mp pon with p1 | p2 <;> rcases or_true_iff.mp qon with q1 | q2
  · exact False.elim (hne (asame p q p1 q1))
  · exact (or_true_iff.mp hron).elim (fun h => Or.inl (asame r p h p1))
      (fun h => Or.inr (bsame r q h q2))
  · exact (or_true_iff.mp hron).elim (fun h => Or.inr (asame r q h q1))
      (fun h => Or.inl (bsame r p h p2))
  · exact False.elim (hne (bsame p q p2 q2))

theorem join_uniform {n : ℕ} {R : Fin n → Fin n → Prop} [DecidableRel R]
    (hK22 : ∀ c d p q : Fin n, p ≠ q → R c p → R c q → R d p → R d q → c = d)
    (U : Finset (Fin n × Fin n)) {f : Paint n} {s t : Wire n}
    (ms : monoW s) (mt : monoW t) (us : uniform R f s) (ut : uniform R f t) :
    ∃ h : Paint n, coarser f h ∧ uniform R h (joinW s t) ∧
      (palette U f).card ≤ (palette U h).card + 1 := by
  classical
  by_cases hgood : uniform R f (joinW s t)
  · exact ⟨f, fun _ _ _ e => e, hgood, Nat.le_succ _⟩
  · have hex : ∃ c : Fin n, joinW s t (negSet R c) = false ∧
        ∃ p q : Fin n, joinW s t {p} = true ∧ joinW s t {q} = true ∧ f c p ≠ f c q := by
      by_contra hall
      apply hgood
      intro c hc p q hp hq
      by_contra hne
      exact hall ⟨c, hc, p, q, hp, hq, hne⟩
    obtain ⟨c, hoff, p, q, pon, qon, hne⟩ := hex
    have hboth : s (negSet R c) = false ∧ t (negSet R c) = false := by
      simpa [joinW] using hoff
    let paint := mergePaint f c (f c p) (f c q)
    refine ⟨paint, after_merge f c (f c p) (f c q), ?_, palette_bound U f c (f c p) (f c q)⟩
    have mj := mono_join ms mt
    have hpq : p ≠ q := fun e => hne (congrArg (f c) e)
    have hcols := two_labels (us c hboth.1) (ut c hboth.2) pon qon hne
    have huniq (d : Fin n) (hd0 : joinW s t (negSet R d) = false) : c = d :=
      hK22 c d p q hpq (valid_rel mj hoff pon) (valid_rel mj hoff qon)
        (valid_rel mj hd0 pon) (valid_rel mj hd0 qon)
    have hpeq (r : Fin n) (hr : joinW s t {r} = true) : paint c r = f c q := by
      rcases hcols r hr with hl | hr'
      · simp [paint, mergePaint, hl]
      · simp [paint, mergePaint, hr', Ne.symm hne]
    intro d hd r k hr hk
    obtain rfl := huniq d hd
    exact (hpeq r hr).trans (hpeq k hk).symm

def nextW {n : ℕ} (xs : List (Wire n)) (g : Gate) : Wire n :=
  fun X => g.op.eval (g.inputs.map (fun i => (xs.getD i zeroW) X))

def snocW {n : ℕ} (xs : List (Wire n)) (g : Gate) : List (Wire n) :=
  xs ++ [nextW xs g]

theorem lookup_wire {n : ℕ} (xs : List (Wire n)) (X : Finset (Fin n)) (i : ℕ) :
    (xs.map (fun s => s X)).getD i false = (xs.getD i zeroW) X := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i]? <;> rfl

theorem eval_foldl {n : ℕ} (gs : List Gate) (xs : List (Wire n)) (X : Finset (Fin n)) :
    (gs.foldl snocW xs).map (fun s => s X) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (xs.map (fun s => s X)) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    simp only [snocW, nextW, List.map_append, List.map_singleton, lookup_wire]

theorem zeroW_ok {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (f : Paint n) :
    monoW (zeroW : Wire n) ∧ uniform R f zeroW := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ h
    cases h
  · intro _ _ _ _ hp _
    cases hp

theorem good_lookup {n : ℕ} {R : Fin n → Fin n → Prop} [DecidableRel R] {f : Paint n}
    {xs : List (Wire n)} (hok : ∀ s ∈ xs, monoW s ∧ uniform R f s) (i : ℕ) :
    monoW (xs.getD i zeroW) ∧ uniform R f (xs.getD i zeroW) := by
  rw [List.getD_eq_getElem?_getD]
  cases heq : xs[i]? with
  | some s => exact hok s (List.mem_of_getElem? heq)
  | none => exact zeroW_ok R f

theorem one_gate {n : ℕ} {R : Fin n → Fin n → Prop} [DecidableRel R]
    (hK22 : ∀ c d p q : Fin n, p ≠ q → R c p → R c q → R d p → R d q → c = d)
    (U : Finset (Fin n × Fin n)) {f : Paint n} {xs : List (Wire n)}
    (hok : ∀ s ∈ xs, monoW s ∧ uniform R f s) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    ∃ h : Paint n, coarser f h ∧ (monoW (nextW xs g) ∧ uniform R h (nextW xs g)) ∧
      (palette U f).card ≤ (palette U h).card + 1 := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, ds⟩⟩⟩
  · rcases hop with rfl | rfl
    · have hm : nextW xs ⟨GateOp.and, []⟩ = oneW := by funext X; rfl
      refine ⟨f, fun _ _ _ e => e, ?_, Nat.le_succ _⟩
      rw [hm]
      exact ⟨fun _ _ _ h => h, fun _ hoff _ _ _ _ => by cases hoff⟩
    · have hm : nextW xs ⟨GateOp.or, []⟩ = zeroW := by funext X; rfl
      refine ⟨f, fun _ _ _ e => e, ?_, Nat.le_succ _⟩
      rw [hm]
      exact ⟨fun _ _ _ h => h, fun _ _ _ _ hp _ => by cases hp⟩
  · obtain ⟨ma, ua⟩ := good_lookup hok a
    rcases hop with rfl | rfl
    · have hm : nextW xs ⟨GateOp.and, [a]⟩ = xs.getD a zeroW := by
        funext X; simp [nextW, GateOp.eval]
      exact ⟨f, fun _ _ _ e => e, hm ▸ ⟨ma, ua⟩, Nat.le_succ _⟩
    · have hm : nextW xs ⟨GateOp.or, [a]⟩ = xs.getD a zeroW := by
        funext X; simp [nextW, GateOp.eval]
      exact ⟨f, fun _ _ _ e => e, hm ▸ ⟨ma, ua⟩, Nat.le_succ _⟩
  · obtain ⟨ma, ua⟩ := good_lookup hok a
    obtain ⟨mb, ub⟩ := good_lookup hok b
    rcases hop with rfl | rfl
    · have hm : nextW xs ⟨GateOp.and, [a, b]⟩ = meetW (xs.getD a zeroW) (xs.getD b zeroW) := by
        funext X; simp [nextW, meetW, GateOp.eval]
      exact ⟨f, fun _ _ _ e => e, hm ▸ ⟨mono_meet ma mb, meet_uniform ua ub⟩, Nat.le_succ _⟩
    · have hm : nextW xs ⟨GateOp.or, [a, b]⟩ = joinW (xs.getD a zeroW) (xs.getD b zeroW) := by
        funext X; simp [nextW, joinW, GateOp.eval]
      obtain ⟨h, hc, hu, hbnd⟩ := join_uniform hK22 U ma mb ua ub
      exact ⟨h, hc, hm ▸ ⟨mono_join ma mb, hu⟩, hbnd⟩
  · simp at hlen

theorem run_program {n : ℕ} {R : Fin n → Fin n → Prop} [DecidableRel R]
    (hK22 : ∀ c d p q : Fin n, p ≠ q → R c p → R c q → R d p → R d q → c = d)
    (U : Finset (Fin n × Fin n)) (gs : List Gate) (xs : List (Wire n)) (f : Paint n)
    (hmon : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hok : ∀ s ∈ xs, monoW s ∧ uniform R f s) :
    ∃ h : Paint n, (∀ s ∈ gs.foldl snocW xs, monoW s ∧ uniform R h s) ∧
      (palette U f).card ≤ (palette U h).card + gs.length := by
  induction gs generalizing xs f with
  | nil => exact ⟨f, hok, by simp⟩
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hmon g List.mem_cons_self
    obtain ⟨h1, hc1, hg1, hb1⟩ := one_gate hK22 U hok g hop hlen
    have hnext : ∀ s ∈ snocW xs g, monoW s ∧ uniform R h1 s := by
      intro s hs
      rcases List.mem_append.mp hs with hprev | hfresh
      · exact ⟨(hok s hprev).1, kept_uniform (hok s hprev).2 hc1⟩
      · have hs' : s = nextW xs g := by simpa using hfresh
        exact hs' ▸ hg1
    obtain ⟨hf, hokf, hbf⟩ := ih (snocW xs g) h1
      (fun a ha => hmon a (List.mem_cons_of_mem _ ha)) hnext
    exact ⟨hf, hokf, by simp only [List.length_cons]; omega⟩

def initPaint {n : ℕ} : Paint n := fun _ p => p.val

theorem initPaint_card {n : ℕ} (U : Finset (Fin n × Fin n)) :
    (palette U initPaint).card = U.card := by
  apply Finset.card_image_of_injective
  intro a b heq
  apply Prod.ext
  · exact congrArg (fun z : Fin n × ℕ => z.1) heq
  · exact Fin.ext (congrArg (fun z : Fin n × ℕ => z.2) heq)

def startP (n : ℕ) : List (Wire n) :=
  List.ofFn (fun p : Fin n => fun X => decide (p ∈ X)) ++ List.ofFn (fun _ : Fin n => zeroW)

def startL (n : ℕ) : List (Wire n) :=
  List.ofFn (fun _ : Fin n => zeroW) ++ List.ofFn (fun l : Fin n => fun Y => decide (l ∈ Y))

theorem single_wire_ok {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (i : Fin n) :
    monoW (fun X : Finset (Fin n) => decide (i ∈ X)) ∧
      uniform R initPaint (fun X : Finset (Fin n) => decide (i ∈ X)) := by
  constructor
  · intro X Y hXY hon
    exact decide_eq_true (hXY (of_decide_eq_true hon))
  · intro c _ p q hp hq
    have hip : i = p := Finset.mem_singleton.mp (of_decide_eq_true hp)
    have hiq : i = q := Finset.mem_singleton.mp (of_decide_eq_true hq)
    rw [← hip, ← hiq]

theorem startP_ok {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] :
    ∀ s ∈ startP n, monoW s ∧ uniform R initPaint s := by
  intro s hs
  rcases List.mem_append.mp hs with hl | hr
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact single_wire_ok R i
  · obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hr
    exact zeroW_ok R initPaint

theorem startL_ok {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] :
    ∀ s ∈ startL n, monoW s ∧ uniform R initPaint s := by
  intro s hs
  rcases List.mem_append.mp hs with hl | hr
  · obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hl
    exact zeroW_ok R initPaint
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact single_wire_ok R i

theorem valP_eq {n : ℕ} (D : Circuit) (X : Finset (Fin n)) (i : ℕ) :
    ((D.gates.foldl snocW (startP n)).getD i zeroW) X =
      (D.wires (incidenceInput X (∅ : Finset (Fin n)))).getD i false := by
  rw [← lookup_wire, eval_foldl]
  have hmap : (startP n).map (fun s => s X) = incidenceInput X (∅ : Finset (Fin n)) := by
    simp [startP, incidenceInput, zeroW, List.map_append, List.map_ofFn, Function.comp_def]
  rw [hmap]
  rfl

theorem valL_eq {n : ℕ} (D : Circuit) (Y : Finset (Fin n)) (i : ℕ) :
    ((D.gates.foldl snocW (startL n)).getD i zeroW) Y =
      (D.wires (incidenceInput (∅ : Finset (Fin n)) Y)).getD i false := by
  rw [← lookup_wire, eval_foldl]
  have hmap : (startL n).map (fun s => s Y) = incidenceInput (∅ : Finset (Fin n)) Y := by
    simp [startL, incidenceInput, zeroW, List.map_append, List.map_ofFn, Function.comp_def]
  rw [hmap]
  rfl

theorem color_cap {n K : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (f : Paint n) (B : Finset (Fin K)) (vg : Fin K → Prop)
    (sMain sOther : Fin K → Wire n) (U : Finset (Fin n × Fin n))
    (huni : ∀ t : Fin K, uniform R f (sMain t))
    (hcard1 : ∀ t ∈ B, ∀ c1 c2 : Fin n, vg t → sOther t {c1} = true → sOther t {c2} = true → c1 = c2)
    (hsafe : ∀ t : Fin K, ∀ c : Fin n, vg t → sOther t {c} = true → sMain t (negSet R c) = false)
    (hcov : ∀ z ∈ U, ∃ t ∈ B, vg t ∧ sMain t {z.2} = true ∧ sOther t {z.1} = true) :
    (palette U f).card ≤ B.card := by
  classical
  by_cases hUne : U.Nonempty
  · obtain ⟨z0, _⟩ := hUne
    let witness (t : Fin K) : Prop := ∃ z ∈ U, vg t ∧ sMain t {z.2} = true ∧ sOther t {z.1} = true
    let repr (t : Fin K) : Fin n × ℕ :=
      if hex : witness t then
        let w := Classical.choose hex
        (w.1, f w.1 w.2)
      else (z0.1, 0)
    have hsub : palette U f ⊆ B.image repr := by
      intro y hy
      obtain ⟨⟨c, p⟩, hcp, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨t, htB, hvgt, hmp, hsc⟩ := hcov (c, p) hcp
      have hex : witness t := ⟨(c, p), hcp, hvgt, hmp, hsc⟩
      obtain ⟨_, hvgw, hmw, hsw⟩ := Classical.choose_spec hex
      let w := Classical.choose hex
      have hwc : w.1 = c := hcard1 t htB w.1 c hvgt hsw hsc
      have hoff : sMain t (negSet R c) = false := hsafe t c hvgt hsc
      have hmw' : sMain t {w.2} = true := hmw
      have hcol : f c w.2 = f c p := huni t c hoff w.2 p hmw' hmp
      apply Finset.mem_image.mpr
      refine ⟨t, htB, ?_⟩
      simp only [repr, dite_eq_left hex]
      change (w.1, f w.1 w.2) = (c, f c p)
      rw [hwc, hcol]
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  · have hemp : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUne
    simp [hemp, palette]

end PEqualNP.Outside.L_meta_8309_aux

open PEqualNP.Outside.L_meta_8309_aux in
theorem PEqualNP.Outside.L_meta_8309 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Finset (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ → ℕ),   (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ∃! x9 : Fin x1, x6 ∈ x3 x9 ∧ x7 ∈ x3 x9) →     PEqualNP.MetaComplexity.Monotone2 x4 →       have x8 : Finset (Fin x1) → Finset (Fin x1) → ℕ → Bool := fun (x8 x9 : Finset (Fin x1)) (x10 : ℕ) => (x4.wires (PEqualNP.GenericRejection.incidenceInput x8 x9)).getD x10 Bool.false;       have x9 : Finset (Fin x1) → Finset (Fin x1) → Prop := fun (x9 x10 : Finset (Fin x1)) => ∃ x11 < x2, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x11).inputs.length = (2 : ℕ) ∧ ∃ (x12 : Fin (2 : ℕ)), (x8 x9 ∅ (PEqualNP.TopForm.opnd x4 x11 x12) && x8 ∅ x10 (PEqualNP.TopForm.opnd x4 x11 ((1 : Fin (2 : ℕ)) - x12)) && (x8 x9 ∅ (x5 x11) || x8 ∅ x10 (x5 x11))) = Bool.true;       (∀ (x10 x11 : Finset (Fin x1)), x9 x10 x11 → PEqualNP.GenericRejection.incidenceFun x3 x10 x11 = Bool.true) → ∀ (x11 : Finset (Fin x1 × Fin x1)), (∀ x12 ∈ x11, x9 {x12.1} {x12.2}) → x11.card ≤ (2 : ℕ) * x4.size + (4 : ℕ) * x2 := by
  classical
  intro n m S D k hUnique hMon W h hSound E hE
  let R1 : Fin n → Fin n → Prop := fun l p => p ∈ S l
  let R2 : Fin n → Fin n → Prop := fun p l => p ∈ S l
  have hK1 : ∀ l1 l2 p q : Fin n, p ≠ q → R1 l1 p → R1 l1 q → R1 l2 p → R1 l2 q → l1 = l2 := by
    intro l1 l2 p q hpq h1p h1q h2p h2q
    exact (hUnique p q hpq).unique ⟨h1p, h1q⟩ ⟨h2p, h2q⟩
  have hK2 : ∀ p1 p2 l1 l2 : Fin n, l1 ≠ l2 → R2 p1 l1 → R2 p1 l2 → R2 p2 l1 → R2 p2 l2 → p1 = p2 := by
    intro p1 p2 l1 l2 hl h11 h12 h21 h22
    by_contra hpne
    exact hl ((hUnique p1 p2 hpne).unique ⟨h11, h21⟩ ⟨h12, h22⟩)
  let listP := D.gates.foldl snocW (startP n)
  let listL := D.gates.foldl snocW (startL n)
  let wP (i : ℕ) : Wire n := listP.getD i zeroW
  let wL (i : ℕ) : Wire n := listL.getD i zeroW
  have hwP (X : Finset (Fin n)) (i : ℕ) : wP i X = W X ∅ i := valP_eq D X i
  have hwL (Y : Finset (Fin n)) (i : ℕ) : wL i Y = W ∅ Y i := valL_eq D Y i
  let jOf (t : Fin (4 * m)) : ℕ := t.val / 4
  let bOf (t : Fin (4 * m)) : Fin 2 := ⟨(t.val / 2) % 2, by omega⟩
  let cOf (t : Fin (4 * m)) : Bool := decide (t.val % 2 = 0)
  let vg (t : Fin (4 * m)) : Prop :=
    (PEqualNP.MetaComplexity.NestedCover.gateAt D (jOf t)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt D (jOf t)).inputs.length = 2
  let sP (t : Fin (4 * m)) : Wire n :=
    if cOf t = true then
      meetW (wP (PEqualNP.TopForm.opnd D (jOf t) (bOf t))) (wP (k (jOf t)))
    else
      wP (PEqualNP.TopForm.opnd D (jOf t) (bOf t))
  let sL (t : Fin (4 * m)) : Wire n :=
    if cOf t = true then
      wL (PEqualNP.TopForm.opnd D (jOf t) ((1 : Fin 2) - bOf t))
    else
      meetW (wL (PEqualNP.TopForm.opnd D (jOf t) ((1 : Fin 2) - bOf t))) (wL (k (jOf t)))
  have hjlt (t : Fin (4 * m)) : jOf t < m := by
    have ht := t.isLt
    dsimp [jOf]
    omega
  have hHit (t : Fin (4 * m)) (X Y : Finset (Fin n))
      (hvg : vg t) (hX : sP t X = true) (hY : sL t Y = true) :
      PEqualNP.GenericRejection.incidenceFun S X Y = true := by
    apply hSound X Y
    refine ⟨jOf t, hjlt t, hvg.1, hvg.2, bOf t, ?_⟩
    cases hc : cOf t
    · simp only [sP, sL, hc, Bool.false_eq_true, ↓reduceIte, meetW] at hX hY
      obtain ⟨hY1, hY2⟩ := and_true_iff.mp hY
      rw [hwP] at hX
      rw [hwL] at hY1 hY2
      simp [hX, hY1, hY2]
    · simp only [sP, sL, hc, ↓reduceIte, meetW] at hX hY
      obtain ⟨hX1, hX2⟩ := and_true_iff.mp hX
      rw [hwP] at hX1 hX2
      rw [hwL] at hY
      simp [hX1, hX2, hY]
  have hPairInc (t : Fin (4 * m)) (p l : Fin n)
      (hvg : vg t) (hp : sP t {p} = true) (hl : sL t {l} = true) : p ∈ S l := by
    have hinc := hHit t {p} {l} hvg hp hl
    unfold PEqualNP.GenericRejection.incidenceFun at hinc
    obtain ⟨p', hp', l', hl', hmem⟩ := of_decide_eq_true hinc
    rw [Finset.mem_singleton.mp hp', Finset.mem_singleton.mp hl'] at hmem
    exact hmem
  have hSafeP (t : Fin (4 * m)) (l : Fin n) (hvg : vg t) (hl : sL t {l} = true) :
      sP t (negSet R1 l) = false := by
    cases hs : sP t (negSet R1 l) with
    | false => rfl
    | true =>
      have hinc := hHit t (negSet R1 l) {l} hvg hs hl
      unfold PEqualNP.GenericRejection.incidenceFun at hinc
      obtain ⟨p, hp, l', hl', hmem⟩ := of_decide_eq_true hinc
      rw [Finset.mem_singleton.mp hl'] at hmem
      exact False.elim ((Finset.mem_filter.mp hp).2 hmem)
  have hSafeL (t : Fin (4 * m)) (p : Fin n) (hvg : vg t) (hp : sP t {p} = true) :
      sL t (negSet R2 p) = false := by
    cases hs : sL t (negSet R2 p) with
    | false => rfl
    | true =>
      have hinc := hHit t {p} (negSet R2 p) hvg hp hs
      unfold PEqualNP.GenericRejection.incidenceFun at hinc
      obtain ⟨p', hp', l, hl, hmem⟩ := of_decide_eq_true hinc
      rw [Finset.mem_singleton.mp hp'] at hmem
      exact False.elim ((Finset.mem_filter.mp hl).2 hmem)
  let Pset (t : Fin (4 * m)) : Finset (Fin n) :=
    Finset.univ.filter (fun p => vg t ∧ sP t {p} = true)
  let Lset (t : Fin (4 * m)) : Finset (Fin n) :=
    Finset.univ.filter (fun l => vg t ∧ sL t {l} = true)
  let BP : Finset (Fin (4 * m)) := Finset.univ.filter (fun t => (Lset t).card ≤ 1)
  let BL : Finset (Fin (4 * m)) := Finset.univ.filter (fun t => ¬ (Lset t).card ≤ 1)
  have hBP_BL : BP.card + BL.card = 4 * m := by
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (4 * m))))
      (fun t => (Lset t).card ≤ 1)
    simpa [BP, BL] using hsum
  have hBL_Ple1 (t : Fin (4 * m)) (ht : t ∈ BL) : (Pset t).card ≤ 1 := by
    have hgt : 1 < (Lset t).card := by
      have hnle := (Finset.mem_filter.mp ht).2
      omega
    obtain ⟨l1, hl1, l2, hl2, hlne⟩ := Finset.one_lt_card.mp hgt
    obtain ⟨hvg1, hsl1⟩ := (Finset.mem_filter.mp hl1).2
    obtain ⟨_, hsl2⟩ := (Finset.mem_filter.mp hl2).2
    refine Finset.card_le_one.mpr ?_
    intro p1 hp1 p2 hp2
    have hsp1 := (Finset.mem_filter.mp hp1).2.2
    have hsp2 := (Finset.mem_filter.mp hp2).2.2
    exact hK2 p1 p2 l1 l2 hlne
      (hPairInc t p1 l1 hvg1 hsp1 hsl1) (hPairInc t p1 l2 hvg1 hsp1 hsl2)
      (hPairInc t p2 l1 hvg1 hsp2 hsl1) (hPairInc t p2 l2 hvg1 hsp2 hsl2)
  let EP : Finset (Fin n × Fin n) :=
    E.filter (fun e => ∃ t ∈ BP, vg t ∧ sP t {e.1} = true ∧ sL t {e.2} = true)
  let EL : Finset (Fin n × Fin n) :=
    E.filter (fun e => ∃ t ∈ BL, vg t ∧ sP t {e.1} = true ∧ sL t {e.2} = true)
  have hE_cov : E ⊆ EP ∪ EL := by
    intro e he
    obtain ⟨j, hj, hop, hlen, b, hval⟩ := hE e he
    obtain ⟨h12, hkval⟩ := and_true_iff.mp hval
    obtain ⟨hu, hv⟩ := and_true_iff.mp h12
    let c : Bool := W {e.1} ∅ (k j)
    let idxVal : ℕ := 4 * j + 2 * b.val + (if c = true then 0 else 1)
    have hidxLt : idxVal < 4 * m := by
      have hb := b.isLt
      dsimp [idxVal]
      split <;> omega
    let t : Fin (4 * m) := ⟨idxVal, hidxLt⟩
    have hj_eq : jOf t = j := by
      have hb := b.isLt
      dsimp [jOf, t, idxVal]
      split <;> omega
    have hb_eq : bOf t = b := by
      apply Fin.ext
      have hb := b.isLt
      dsimp [bOf, t, idxVal]
      split <;> omega
    have hc_eq : cOf t = c := by
      have hb := b.isLt
      dsimp [cOf, t, idxVal]
      by_cases hc' : c = true
      · simp [hc']; omega
      · have hcf : c = false := Bool.eq_false_iff.mpr hc'
        simp [hcf]; omega
    have hvgt : vg t := by
      dsimp [vg]
      rw [hj_eq]
      exact ⟨hop, hlen⟩
    have hsPt : sP t {e.1} = true := by
      dsimp [sP]
      rw [hj_eq, hb_eq, hc_eq]
      by_cases hc' : c = true
      · simp only [hc', ↓reduceIte, meetW, hwP]
        have hkeq : W {e.1} ∅ (k j) = true := hc'
        exact and_true_iff.mpr ⟨hu, hkeq⟩
      · have hcf : c = false := Bool.eq_false_iff.mpr hc'
        simp only [hcf, Bool.false_eq_true, ↓reduceIte, hwP]
        exact hu
    have hsLt : sL t {e.2} = true := by
      dsimp [sL]
      rw [hj_eq, hb_eq, hc_eq]
      by_cases hc' : c = true
      · simp only [hc', ↓reduceIte, hwL]
        exact hv
      · have hcf : c = false := Bool.eq_false_iff.mpr hc'
        simp only [hcf, Bool.false_eq_true, ↓reduceIte, meetW, hwL]
        have hkeq : W {e.1} ∅ (k j) = false := hcf
        have hk2 : W ∅ {e.2} (k j) = true := by
          rcases or_true_iff.mp hkval with hleft | hright
          · rw [hkeq] at hleft; cases hleft
          · exact hright
        exact and_true_iff.mpr ⟨hv, hk2⟩
    by_cases htBP : (Lset t).card ≤ 1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, t,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, htBP⟩, hvgt, hsPt, hsLt⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, t,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, htBP⟩, hvgt, hsPt, hsLt⟩)
  let UP : Finset (Fin n × Fin n) := EP.image Prod.swap
  have hUP_card : UP.card = EP.card :=
    Finset.card_image_of_injective EP Prod.swap_injective
  obtain ⟨fP, hokP, hbillP⟩ := run_program hK1 UP D.gates (startP n) initPaint hMon (startP_ok R1)
  obtain ⟨fL, hokL, hbillL⟩ := run_program hK2 EL D.gates (startL n) initPaint hMon (startL_ok R2)
  rw [initPaint_card] at hbillP hbillL
  have huniP (t : Fin (4 * m)) : uniform R1 fP (sP t) := by
    dsimp [sP]
    split
    · exact meet_uniform (good_lookup hokP _).2 (good_lookup hokP _).2
    · exact (good_lookup hokP _).2
  have huniL (t : Fin (4 * m)) : uniform R2 fL (sL t) := by
    dsimp [sL]
    split
    · exact (good_lookup hokL _).2
    · exact meet_uniform (good_lookup hokL _).2 (good_lookup hokL _).2
  have hcapP : (palette UP fP).card ≤ BP.card := by
    refine color_cap R1 fP BP vg sP sL UP huniP ?_ hSafeP ?_
    · intro t ht l1 l2 hvgt hl1 hl2
      have hle1 : (Lset t).card ≤ 1 := (Finset.mem_filter.mp ht).2
      exact Finset.card_le_one.mp hle1
        l1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvgt, hl1⟩)
        l2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvgt, hl2⟩)
    · intro z hz
      obtain ⟨⟨p, l⟩, hpl, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hpl).2
  have hcapL : (palette EL fL).card ≤ BL.card := by
    refine color_cap R2 fL BL vg sL sP EL huniL ?_ hSafeL ?_
    · intro t ht p1 p2 hvgt hp1 hp2
      have hle1 : (Pset t).card ≤ 1 := hBL_Ple1 t ht
      exact Finset.card_le_one.mp hle1
        p1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvgt, hp1⟩)
        p2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvgt, hp2⟩)
    · intro z hz
      obtain ⟨t, htBL, hvgt, hsPt, hsLt⟩ := (Finset.mem_filter.mp hz).2
      exact ⟨t, htBL, hvgt, hsLt, hsPt⟩
  have hE_le : E.card ≤ EP.card + EL.card :=
    (Finset.card_le_card hE_cov).trans (Finset.card_union_le EP EL)
  have hsize : D.gates.length = D.size := rfl
  omega
