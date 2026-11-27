import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3669

-- The counterexample adapts the Boolean sums of Tarjan (1978), as presented by Wegener (The Complexity of Boolean Functions).

open Classical

def Ckt (V : Type) : Type :=
  Finset ℕ × (ℕ → Bool) × (ℕ → V ⊕ ℕ) × (ℕ → V ⊕ ℕ) × (V ⊕ ℕ)

def Ckt.mk {V : Type} (G : Finset ℕ) (op : ℕ → Bool) (l r : ℕ → V ⊕ ℕ) (o : V ⊕ ℕ) : Ckt V :=
  (G, op, l, r, o)

def Ckt.G {V : Type} (C : Ckt V) : Finset ℕ := C.1
def Ckt.op {V : Type} (C : Ckt V) : ℕ → Bool := C.2.1
def Ckt.l {V : Type} (C : Ckt V) : ℕ → V ⊕ ℕ := C.2.2.1
def Ckt.r {V : Type} (C : Ckt V) : ℕ → V ⊕ ℕ := C.2.2.2.1
def Ckt.out {V : Type} (C : Ckt V) : V ⊕ ℕ := C.2.2.2.2

def rk {V : Type} : V ⊕ ℕ → ℕ := Sum.elim (fun _ => 0) (fun g => g + 1)

def Vl {V : Type} (C : Ckt V) (w : V ⊕ ℕ) : Prop := ∀ k, w = Sum.inr k → k ∈ C.G

def Wf {V : Type} (C : Ckt V) : Prop :=
  (∀ g ∈ C.G, (Vl C (C.l g) ∧ rk (C.l g) ≤ g) ∧ (Vl C (C.r g) ∧ rk (C.r g) ≤ g)) ∧ Vl C C.out

def Ckt.gv {V : Type} (C : Ckt V) (ρ : Set V) (g : ℕ) : Prop :=
  if C.op g = true then
    (Sum.elim (fun v => v ∈ ρ) (fun k => ∃ _ : k < g, Ckt.gv C ρ k) (C.l g)) ∧
    (Sum.elim (fun v => v ∈ ρ) (fun k => ∃ _ : k < g, Ckt.gv C ρ k) (C.r g))
  else
    (Sum.elim (fun v => v ∈ ρ) (fun k => ∃ _ : k < g, Ckt.gv C ρ k) (C.l g)) ∨
    (Sum.elim (fun v => v ∈ ρ) (fun k => ∃ _ : k < g, Ckt.gv C ρ k) (C.r g))
termination_by g

def Ckt.val {V : Type} (C : Ckt V) (ρ : Set V) : V ⊕ ℕ → Prop :=
  Sum.elim (fun v => v ∈ ρ) (fun g => C.gv ρ g)

def Rd {V : Type} (C : Ckt V) (g : ℕ) (w : V ⊕ ℕ) : Prop := g ∈ C.G ∧ (C.l g = w ∨ C.r g = w)

def fo {V : Type} [DecidableEq V] (C : Ckt V) (w : V ⊕ ℕ) : ℕ :=
  ∑ g ∈ C.G, ((if C.l g = w then 1 else 0) + (if C.r g = w then 1 else 0))

def nAnd {V : Type} (C : Ckt V) : ℕ := (C.G.filter (fun g => C.op g = true)).card

def Clean {V : Type} (C : Ckt V) : Prop :=
  ∀ g ∈ C.G, C.op g = true → ∀ v, ¬ C.val {v} (Sum.inr g)

def Useful {V : Type} [DecidableEq V] (C : Ckt V) : Prop :=
  Wf C ∧ fo C C.out = 0 ∧ ∀ g ∈ C.G, Sum.inr g ≠ C.out → 1 ≤ fo C (Sum.inr g)

def Gr {V : Type} (E : V → V → Prop) : Prop := (∀ u v, E u v → E v u) ∧ ∀ u, ¬ E u u

def Fn {V : Type} (E : V → V → Prop) (X ρ : Set V) : Prop :=
  ∃ u v, E u v ∧ u ∈ X ∧ v ∈ X ∧ u ∈ ρ ∧ v ∈ ρ

def HasEdge {V : Type} (E : V → V → Prop) (X : Set V) : Prop := ∃ u ∈ X, ∃ v ∈ X, E u v

def Comp {V : Type} (E : V → V → Prop) (X : Set V) (C : Ckt V) : Prop :=
  ∀ ρ, C.val ρ C.out ↔ Fn E X ρ

def Rigid {V : Type} [DecidableEq V] (Y : Set V) (C : Ckt V) : Prop :=
  ∀ y ∈ Y, fo C (Sum.inl y) ≤ 1 ∧ ∀ g, Rd C g (Sum.inl y) → C.op g = true

def Good {V : Type} [DecidableEq V] (E : V → V → Prop) (X Y : Set V) (C : Ckt V) : Prop :=
  Wf C ∧ Clean C ∧ Comp E X C ∧ Rigid Y C

def Opt {V : Type} [DecidableEq V] (E : V → V → Prop) (X Y : Set V) (C : Ckt V) : Prop :=
  Good E X Y C ∧ ∀ C', Good E X Y C' → C.G.card ≤ C'.G.card

noncomputable def sz {V : Type} [DecidableEq V] (E : V → V → Prop) (X : Set V) : ℕ :=
  sInf {n | ∃ C : Ckt V, Good E X ∅ C ∧ C.G.card = n}

def Pend {V : Type} (E : V → V → Prop) (X : Set V) (y z : V) : Prop :=
  y ∈ X ∧ z ∈ X ∧ E y z ∧ ∀ u ∈ X, E z u → u = y

def Nmd {V : Type} [DecidableEq V] (E : V → V → Prop) (X : Set V) (C : Ckt V) : Prop :=
  ∀ y z, Pend E X y z → ∀ g, Rd C g (Sum.inl y) → C.op g = false → 2 ≤ fo C (Sum.inl y)

def Dd {V : Type} (C : Ckt V) (P : Finset V) (w : V ⊕ ℕ) : Prop := ¬ C.val ((↑P : Set V)ᶜ) w

noncomputable def al {V : Type} (C : Ckt V) (P : Finset V) : Finset ℕ :=
  C.G.filter (fun g => Dd C P (C.l g) ∧ Dd C P (C.r g))
noncomputable def be {V : Type} (C : Ckt V) (P : Finset V) : Finset ℕ :=
  C.G.filter (fun g => C.op g = true ∧ (Dd C P (C.l g) ↔ ¬ Dd C P (C.r g)))
noncomputable def ga {V : Type} (C : Ckt V) (P : Finset V) : Finset ℕ :=
  C.G.filter (fun g => C.op g = false ∧ (Dd C P (C.l g) ↔ ¬ Dd C P (C.r g)))
noncomputable def su {V : Type} (C : Ckt V) (P : Finset V) : Finset ℕ :=
  C.G.filter (fun g => ¬ Dd C P (C.l g) ∧ ¬ Dd C P (C.r g))

noncomputable def dw {V : Type} (C : Ckt V) (P : Finset V) : Finset (V ⊕ ℕ) :=
  P.disjSum (C.G.filter (fun g => Dd C P (Sum.inr g)))

noncomputable def exc {V : Type} [DecidableEq V] (C : Ckt V) (P : Finset V) : ℕ :=
  ∑ w ∈ (dw C P).erase C.out, (fo C w - 1)

noncomputable def kl {V : Type} (C : Ckt V) (P : Finset V) : ℕ :=
  (al C P).card + (be C P).card + (ga C P).card

def red {V : Type} [DecidableEq V] (C : Ckt V) (g : ℕ) (w : V ⊕ ℕ) : Ckt V :=
  Ckt.mk (C.G.erase g) C.op (fun k => if C.l k = Sum.inr g then w else C.l k)
    (fun k => if C.r k = Sum.inr g then w else C.r k) (if C.out = Sum.inr g then w else C.out)

def Gad {V : Type} (E : V → V → Prop) (X : Set V) (z0 z1 z2 y1 y2 : V) : Prop :=
  Pend E X y1 z1 ∧ Pend E X y2 z2 ∧ z0 ∈ X ∧ E z0 y1 ∧ E z0 y2 ∧
  (∀ u ∈ X, E z0 u → u = y1 ∨ u = y2) ∧ [z0, z1, z2, y1, y2].Nodup ∧ ¬ E y1 y2 ∧
  ∃ x ∈ X, x ∉ [z0, z1, z2, y1, y2] ∧ E y1 x ∧ E y2 x

def Loc {V : Type} [DecidableEq V] (E : V → V → Prop) (X : Set V) (C : Ckt V)
    (z0 z1 z2 y1 y2 : V) : Prop :=
  Gr E ∧ Opt E X ∅ C ∧ Nmd E X C ∧ Gad E X z0 z1 z2 y1 y2 ∧
  ¬ Dd C {z0, z1, z2, y1, y2} C.out ∧ kl C {z0} ≤ 1 ∧ kl C {z1, z2, y2} ≤ 4 ∧
  kl C {z1, z2, y1} ≤ 4 ∧ kl C {z0, z1, z2, y1, y2} ≤ 7

def CStep {V : Type} (C : Ckt V) (P : Finset V) (w w' : V ⊕ ℕ) : Prop :=
  ∃ g ∈ al C P, w' = Sum.inr g ∧ C.op g = false ∧ (C.l g = w ∨ C.r g = w)
def Cn {V : Type} (C : Ckt V) (P : Finset V) : V ⊕ ℕ → V ⊕ ℕ → Prop :=
  Relation.ReflTransGen (CStep C P)

abbrev Cp : Type := Fin 14 × ℕ
abbrev V0 : Type := Fin 11 ⊕ (Cp × Fin 5)

def Osum : Fin 14 → Finset (Fin 11) :=
  ![{0, 9}, {1, 10}, {2, 9}, {3, 10}, {6, 9}, {6, 7, 9}, {6, 7, 8, 9}, {6, 10}, {6, 7, 10},
    {6, 7, 8, 10}, {0, 4, 6, 7, 8, 9}, {1, 4, 6, 7, 8, 10}, {2, 5, 6, 7, 8, 9}, {3, 5, 6, 7, 8, 10}]

def PL : V0 → V0 → Prop
  | Sum.inl a, Sum.inr (c, k) => (k = 3 ∨ k = 4) ∧ a ∈ Osum c.1
  | Sum.inr (c, k), Sum.inr (d, m) =>
      c = d ∧ ((k = 0 ∧ (m = 3 ∨ m = 4)) ∨ (k = 1 ∧ m = 3) ∨ (k = 2 ∧ m = 4))
  | _, Sum.inl _ => False

def E0 (u v : V0) : Prop := PL u v ∨ PL v u

def XS (S : Finset Cp) : Set V0 := {v | ∀ c k, v = Sum.inr (c, k) → c ∈ S}

def cv (c : Cp) (k : Fin 5) : V0 := Sum.inr (c, k)

def cnt (S : Finset Cp) (l : Fin 14) : ℕ := (S.filter (fun c => c.1 = l)).card
def rich (t : ℕ) (S : Finset Cp) : Prop := ∀ l, t ≤ cnt S l
def box (T : ℕ) : Finset Cp := Finset.univ ×ˢ Finset.range T

def HypH : Prop :=
  ∀ T, 1 ≤ T → ∃ C : Ckt V0, Good E0 (XS (box T)) ∅ C ∧ C.G.card ≤ 7 * (14 * T) + 16

def PP {V ι : Type} [DecidableEq V] (J : Finset ι) (y z : ι → V) : Finset V :=
  J.image y ∪ J.image z

def H6 {V ι : Type} [DecidableEq V] (C : Ckt V) (J : Finset ι) (y z : ι → V) (O : ι → Set V) :
    Prop :=
  Clean C ∧ Useful C ∧ Set.InjOn y ↑J ∧ Set.InjOn z ↑J ∧ (∀ i ∈ J, ∀ j ∈ J, y i ≠ z j) ∧
  (∀ ρ : Set V, (∀ p ∈ PP J y z, p ∉ ρ) → ¬ C.val ρ C.out) ∧ (∀ v, ¬ C.val {v} C.out) ∧
  (∀ j ∈ J, C.val {y j, z j} C.out) ∧
  (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ C.val {y j, z i} C.out) ∧
  (∀ j ∈ J, ∀ x, x ∉ PP J y z → (C.val {y j, x} C.out ↔ x ∈ O j)) ∧
  (∀ j ∈ J, ∃ x, x ∉ PP J y z ∧ x ∈ O j) ∧
  (∀ j ∈ J, fo C (Sum.inl (y j)) ≤ 1 ∧ ∀ g, Rd C g (Sum.inl (y j)) → C.op g = true) ∧
  C.G.card ≤ 3 * J.card + 16

def CL {V ι : Type} [DecidableEq V] (C : Ckt V) (J : Finset ι) (y z : ι → V) (O : ι → Set V)
    (c : ι → ℕ) (L : ι → V ⊕ ℕ) : Prop :=
  Set.InjOn c ↑J ∧
  (∀ j ∈ J, c j ∈ be C (PP J y z) ∧
    ((C.l (c j) = Sum.inl (y j) ∧ C.r (c j) = L j) ∨
      (C.r (c j) = Sum.inl (y j) ∧ C.l (c j) = L j)) ∧
    (∀ g, Rd C g (Sum.inl (y j)) → g = c j) ∧ fo C (Sum.inl (y j)) = 1 ∧ Vl C (L j) ∧
    ¬ Dd C (PP J y z) (L j) ∧ C.val {z j} (L j) ∧
    (∀ ρ : Set V, C.val (ρ ∪ {y j}) (L j) → C.val ρ (L j)) ∧
    (∀ x, x ∉ PP J y z → x ∈ O j → C.val {x} (L j))) ∧
  exc C (PP J y z) + (be C (PP J y z) \ J.image c).card + (su C (PP J y z)).card ≤ 17

def ChainOK {V : Type} (C : Ckt V) (P : Finset V) (zj : V) (K : Set (V ⊕ ℕ)) (g : ℕ) : Prop :=
  Sum.inl zj ∈ K ∧ g ∈ ga C P ∧ Sum.inr g ∉ K ∧ (∀ v, Sum.inl v ∈ K → v = zj) ∧
  (∀ k, Sum.inr k ∈ K → k ∈ al C P ∧ C.op k = false) ∧
  (∀ w ∈ K, ∀ k, Rd C k w → Sum.inr k ∈ K ∨ k = g) ∧
  (∀ ρ : Set V, zj ∈ ρ → C.val ρ (Sum.inr g) ∧ ∀ w ∈ K, Vl C w ∧ C.val ρ w) ∧
  ∃ w ∈ K, Rd C g w

noncomputable def LLs {V : Type} [DecidableEq V] (C : Ckt V) (P : Finset V) (B : Finset ℕ) :
    Finset (V ⊕ ℕ) :=
  ((B ∪ su C P).image C.l ∪ (B ∪ su C P).image C.r).filter (fun w => ¬ Dd C P w)

def GStep {V : Type} (C : Ckt V) (P : Finset V) (w u : V ⊕ ℕ) : Prop :=
  ∃ g ∈ ga C P, w = Sum.inr g ∧ (C.l g = u ∨ C.r g = u) ∧ ¬ Dd C P u
def GP {V : Type} (C : Ckt V) (P : Finset V) : V ⊕ ℕ → V ⊕ ℕ → Prop :=
  Relation.ReflTransGen (GStep C P)

variable {V : Type}

lemma val_inl (C : Ckt V) (ρ : Set V) (v : V) : C.val ρ (Sum.inl v) ↔ v ∈ ρ := Iff.rfl

lemma gv_arg {C : Ckt V} {ρ : Set V} {g : ℕ} {w : V ⊕ ℕ} (h : rk w ≤ g) :
    Sum.elim (fun v => v ∈ ρ) (fun k => ∃ _ : k < g, Ckt.gv C ρ k) w ↔ C.val ρ w := by
  rcases w with v | k
  · exact Iff.rfl
  · have hk : k < g := by simpa [rk] using h
    simp [Ckt.val, hk]

lemma val_gate {C : Ckt V} (hW : Wf C) {g : ℕ} (hg : g ∈ C.G) (ρ : Set V) :
    C.val ρ (Sum.inr g) ↔
      if C.op g = true then C.val ρ (C.l g) ∧ C.val ρ (C.r g)
      else C.val ρ (C.l g) ∨ C.val ρ (C.r g) := by
  have h1 := gv_arg (C := C) (ρ := ρ) (hW.1 g hg).1.2
  have h2 := gv_arg (C := C) (ρ := ρ) (hW.1 g hg).2.2
  show C.gv ρ g ↔ _
  rw [Ckt.gv]
  split_ifs
  · exact and_congr h1 h2
  · exact or_congr h1 h2

lemma val_and {C : Ckt V} (hW : Wf C) {g : ℕ} (hg : g ∈ C.G) (ho : C.op g = true) (ρ : Set V) :
    C.val ρ (Sum.inr g) ↔ C.val ρ (C.l g) ∧ C.val ρ (C.r g) := by
  rw [val_gate hW hg, if_pos ho]

lemma val_or {C : Ckt V} (hW : Wf C) {g : ℕ} (hg : g ∈ C.G) (ho : C.op g = false) (ρ : Set V) :
    C.val ρ (Sum.inr g) ↔ C.val ρ (C.l g) ∨ C.val ρ (C.r g) := by
  rw [val_gate hW hg, if_neg (by simp [ho])]

lemma wire_ind {C : Ckt V} (hW : Wf C) {p : V ⊕ ℕ → Prop} (hv : ∀ v, p (Sum.inl v))
    (hg : ∀ g ∈ C.G, (∀ w, Vl C w → rk w ≤ g → p w) → p (Sum.inr g)) : ∀ w, Vl C w → p w := by
  have key : ∀ n, ∀ w, Vl C w → rk w ≤ n → p w := by
    intro n
    induction n with
    | zero =>
      intro w _ hr
      rcases w with v | k
      · exact hv v
      · simp [rk] at hr
    | succ n ih =>
      intro w hw hr
      rcases w with v | k
      · exact hv v
      · refine hg k (hw k rfl) (fun w hw' hr' => ih w hw' (le_trans hr' ?_))
        simpa [rk] using hr
  exact fun w hw => key (rk w) w hw le_rfl

lemma wire_ind' {C : Ckt V} (hW : Wf C) {p : V ⊕ ℕ → Prop} (hv : ∀ v, p (Sum.inl v))
    (hg : ∀ g ∈ C.G, p (C.l g) → p (C.r g) → p (Sum.inr g)) : ∀ w, Vl C w → p w :=
  wire_ind hW hv fun g hgG ih =>
    hg g hgG (ih _ (hW.1 g hgG).1.1 (hW.1 g hgG).1.2) (ih _ (hW.1 g hgG).2.1 (hW.1 g hgG).2.2)

lemma vl_inl (C : Ckt V) (v : V) : Vl C (Sum.inl v) := fun k h => by cases h

lemma vl_inr {C : Ckt V} {g : ℕ} (hg : g ∈ C.G) : Vl C (Sum.inr g) := fun k h => by
  cases h; exact hg

lemma rd_vl {C : Ckt V} (hW : Wf C) {g : ℕ} {w : V ⊕ ℕ} (h : Rd C g w) : Vl C w ∧ rk w ≤ g := by
  obtain ⟨hg, h | h⟩ := h
  · exact h ▸ (hW.1 g hg).1
  · exact h ▸ (hW.1 g hg).2

lemma val_mono {C : Ckt V} (hW : Wf C) {ρ σ : Set V} (h : ρ ⊆ σ) :
    ∀ w, Vl C w → C.val ρ w → C.val σ w := by
  refine wire_ind' hW (fun v hv => h hv) (fun g hg hl hr => ?_)
  rw [val_gate hW hg, val_gate hW hg]
  split_ifs
  · exact And.imp hl hr
  · exact Or.imp hl hr

lemma val_empty {C : Ckt V} (hW : Wf C) : ∀ w, Vl C w → ¬ C.val ∅ w := by
  refine wire_ind' hW (fun v hv => hv) (fun g hg hl hr => ?_)
  rw [val_gate hW hg]
  split_ifs
  · exact fun h => hl h.1
  · exact fun h => h.elim hl hr

lemma val_univ {C : Ckt V} (hW : Wf C) : ∀ w, Vl C w → C.val Set.univ w := by
  refine wire_ind' hW (fun v => Set.mem_univ v) (fun g hg hl hr => ?_)
  rw [val_gate hW hg]
  split_ifs
  · exact ⟨hl, hr⟩
  · exact Or.inl hl

lemma escape {C : Ckt V} (hW : Wf C) (K : Set (V ⊕ ℕ)) {ρ σ : Set V}
    (hv : ∀ v, Sum.inl v ∉ K → v ∈ ρ → v ∈ σ)
    (hK : ∀ g ∈ C.G, Sum.inr g ∉ K → (C.l g ∈ K ∨ C.r g ∈ K) →
      C.val ρ (Sum.inr g) → C.val σ (Sum.inr g)) :
    ∀ w, Vl C w → w ∉ K → C.val ρ w → C.val σ w := by
  refine wire_ind' hW (fun v hvK h => hv v hvK h) (fun g hg hl hr hgK => ?_)
  by_cases hb : C.l g ∈ K ∨ C.r g ∈ K
  · exact hK g hg hgK hb
  · push Not at hb
    rw [val_gate hW hg, val_gate hW hg]
    split_ifs
    · exact And.imp (hl hb.1) (hr hb.2)
    · exact Or.imp (hl hb.1) (hr hb.2)

lemma ignore {C : Ckt V} (hW : Wf C) {v : V} {n : ℕ} (hn : ∀ k, Rd C k (Sum.inl v) → n ≤ k)
    {ρ σ : Set V} (h : ∀ u, u ≠ v → u ∈ ρ → u ∈ σ) :
    ∀ w, Vl C w → rk w ≤ n → w ≠ Sum.inl v → C.val ρ w → C.val σ w := by
  refine wire_ind' hW (fun u _ hu => h u (fun e => hu (e ▸ rfl))) (fun g hg hl hr hrk _ => ?_)
  have hgn : g < n := by simpa [rk] using hrk
  have h1 : C.l g ≠ Sum.inl v := fun e => by have := hn g ⟨hg, Or.inl e⟩; omega
  have h2 : C.r g ≠ Sum.inl v := fun e => by have := hn g ⟨hg, Or.inr e⟩; omega
  have hl' := hl (le_trans (hW.1 g hg).1.2 hgn.le) h1
  have hr' := hr (le_trans (hW.1 g hg).2.2 hgn.le) h2
  rw [val_gate hW hg, val_gate hW hg]
  split_ifs
  · exact And.imp hl' hr'
  · exact Or.imp hl' hr'

lemma val_unique {C : Ckt V} (hW : Wf C) {ρ : Set V} {p : V ⊕ ℕ → Prop}
    (hv : ∀ v, p (Sum.inl v) ↔ v ∈ ρ)
    (hg : ∀ g ∈ C.G, p (Sum.inr g) ↔
      if C.op g = true then p (C.l g) ∧ p (C.r g) else p (C.l g) ∨ p (C.r g)) :
    ∀ w, Vl C w → (p w ↔ C.val ρ w) := by
  refine wire_ind' hW (fun v => hv v) (fun g hgG hl hr => ?_)
  rw [hg g hgG, val_gate hW hgG]
  split_ifs
  · exact and_congr hl hr
  · exact or_congr hl hr

section fanout
variable [DecidableEq V]

lemma fo_pos {C : Ckt V} {w : V ⊕ ℕ} : 1 ≤ fo C w ↔ ∃ g, Rd C g w := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    have : fo C w = 0 := by
      refine Finset.sum_eq_zero fun g hg => ?_
      have := hno g
      simp only [Rd, not_and, not_or] at this
      simp [(this hg).1, (this hg).2]
    omega
  · rintro ⟨g, hg, h⟩
    have : ((if C.l g = w then 1 else 0) + (if C.r g = w then 1 else 0)) ≤ fo C w :=
      Finset.single_le_sum (f := fun g => ((if C.l g = w then 1 else 0) +
        (if C.r g = w then 1 else 0))) (fun _ _ => Nat.zero_le _) hg
    rcases h with h | h <;> simp only [h, if_true] at this <;> omega

lemma fo_two_of_ne {C : Ckt V} {w : V ⊕ ℕ} {g k : ℕ} (hg : Rd C g w) (hk : Rd C k w)
    (hne : g ≠ k) : 2 ≤ fo C w := by
  have hsub : ({g, k} : Finset ℕ) ⊆ C.G := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    exacts [hg.1, hk.1]
  have := Finset.sum_le_sum_of_subset (f := fun g => ((if C.l g = w then 1 else 0) +
    (if C.r g = w then 1 else 0))) hsub
  rw [Finset.sum_pair hne] at this
  change _ ≤ fo C w at this
  have a1 : 1 ≤ ((if C.l g = w then 1 else 0) + (if C.r g = w then 1 else 0)) := by
    rcases hg.2 with h | h <;> simp [h]
  have a2 : 1 ≤ ((if C.l k = w then 1 else 0) + (if C.r k = w then 1 else 0)) := by
    rcases hk.2 with h | h <;> simp [h]
  omega

lemma rd_unique {C : Ckt V} {w : V ⊕ ℕ} (h : fo C w ≤ 1) {g k : ℕ} (hg : Rd C g w)
    (hk : Rd C k w) : g = k := by
  by_contra hne
  have := fo_two_of_ne hg hk hne
  omega

lemma fo_two_of_both {C : Ckt V} {w : V ⊕ ℕ} {g : ℕ} (hg : g ∈ C.G) (hl : C.l g = w)
    (hr : C.r g = w) : 2 ≤ fo C w := by
  have : ((if C.l g = w then 1 else 0) + (if C.r g = w then 1 else 0)) ≤ fo C w :=
    Finset.single_le_sum (f := fun g => ((if C.l g = w then 1 else 0) +
      (if C.r g = w then 1 else 0))) (fun _ _ => Nat.zero_le _) hg
  simpa [hl, hr] using this

end fanout

lemma dd_inl (C : Ckt V) (P : Finset V) (v : V) : Dd C P (Sum.inl v) ↔ v ∈ P := by
  simp [Dd, val_inl]

lemma dd_gate {C : Ckt V} (hW : Wf C) (P : Finset V) {g : ℕ} (hg : g ∈ C.G) :
    Dd C P (Sum.inr g) ↔
      if C.op g = true then Dd C P (C.l g) ∨ Dd C P (C.r g)
      else Dd C P (C.l g) ∧ Dd C P (C.r g) := by
  unfold Dd
  rw [val_gate hW hg]
  split_ifs <;> tauto

lemma dd_mono {C : Ckt V} (hW : Wf C) {P Q : Finset V} (h : P ⊆ Q) {w : V ⊕ ℕ} (hw : Vl C w) :
    Dd C P w → Dd C Q w :=
  mt (val_mono hW (Set.compl_subset_compl.mpr (Finset.coe_subset.mpr h)) w hw)

lemma dd_off {C : Ckt V} (hW : Wf C) {P : Finset V} {w : V ⊕ ℕ} (hw : Vl C w) (h : Dd C P w)
    {ρ : Set V} (hρ : ∀ p ∈ P, p ∉ ρ) : ¬ C.val ρ w :=
  fun hv => h (val_mono (σ := (↑P : Set V)ᶜ) hW
    (fun u hu hp => hρ u (Finset.mem_coe.mp hp) hu) w hw hv)

lemma mem_dw_inl (C : Ckt V) (P : Finset V) (v : V) : Sum.inl v ∈ dw C P ↔ v ∈ P := by
  simp [dw]

lemma mem_dw_inr (C : Ckt V) (P : Finset V) (g : ℕ) :
    Sum.inr g ∈ dw C P ↔ g ∈ C.G ∧ Dd C P (Sum.inr g) := by
  simp [dw]

lemma mem_dw {C : Ckt V} {P : Finset V} {w : V ⊕ ℕ} : w ∈ dw C P ↔ Vl C w ∧ Dd C P w := by
  rcases w with v | g
  · rw [mem_dw_inl, dd_inl]; exact (and_iff_right (vl_inl C v)).symm
  · rw [mem_dw_inr]
    exact and_congr_left fun _ => ⟨fun h => vl_inr h, fun h => h g rfl⟩

lemma kinds_dead {C : Ckt V} (hW : Wf C) (P : Finset V) {g : ℕ} (hg : g ∈ C.G) :
    Dd C P (Sum.inr g) ↔ g ∈ al C P ∨ g ∈ be C P := by
  rw [dd_gate hW P hg]
  simp only [al, be, Finset.mem_filter, hg, true_and]
  cases C.op g <;> simp <;> tauto

lemma kinds_cover {C : Ckt V} (P : Finset V) {g : ℕ} (hg : g ∈ C.G) :
    g ∈ al C P ∨ g ∈ be C P ∨ g ∈ ga C P ∨ g ∈ su C P := by
  simp only [al, be, ga, su, Finset.mem_filter, hg, true_and]
  cases C.op g <;> simp <;> tauto

section opt
variable [DecidableEq V] {E : V → V → Prop} {X Y : Set V}

lemma opt_exists (h : ∃ C : Ckt V, Good E X Y C) : ∃ C : Ckt V, Opt E X Y C := by
  obtain ⟨C0, h0⟩ := h
  have hne : ∃ n, ∃ C : Ckt V, Good E X Y C ∧ C.G.card = n := ⟨_, C0, h0, rfl⟩
  obtain ⟨C, hC, hn⟩ := Nat.find_spec hne
  refine ⟨C, hC, fun C' h' => ?_⟩
  rw [hn]
  exact Nat.find_min' hne ⟨C', h', rfl⟩

lemma sz_le {C : Ckt V} (h : Good E X ∅ C) : sz E X ≤ C.G.card := Nat.sInf_le ⟨C, h, rfl⟩

lemma opt_sz {C : Ckt V} (h : Opt E X ∅ C) : C.G.card = sz E X := by
  apply le_antisymm
  · refine le_csInf ⟨_, C, h.1, rfl⟩ ?_
    rintro n ⟨C', h', rfl⟩
    exact h.2 C' h'
  · exact sz_le h.1

lemma opt_of_sz {C : Ckt V} (h : Good E X ∅ C) (hs : C.G.card ≤ sz E X) : Opt E X ∅ C :=
  ⟨h, fun _ h' => le_trans hs (sz_le h')⟩

lemma fn_single (hE : Gr E) (v : V) : ¬ Fn E X {v} := by
  rintro ⟨a, b, hab, _, _, ha, hb⟩
  rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb] at hab
  exact hE.2 _ hab

lemma fn_pair (hE : Gr E) {u v : V} : Fn E X {u, v} ↔ E u v ∧ u ∈ X ∧ v ∈ X := by
  constructor
  · rintro ⟨a, b, hab, ha, hb, ha', hb'⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha' hb'
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd hab (hE.2 _)
    · exact ⟨hab, ha, hb⟩
    · exact ⟨hE.1 _ _ hab, hb, ha⟩
    · exact absurd hab (hE.2 _)
  · rintro ⟨h, hu, hv⟩
    exact ⟨u, v, h, hu, hv, by simp, by simp⟩

lemma fn_mono {ρ σ : Set V} (h : ρ ⊆ σ) : Fn E X ρ → Fn E X σ := by
  rintro ⟨a, b, h1, h2, h3, h4, h5⟩
  exact ⟨a, b, h1, h2, h3, h h4, h h5⟩

lemma fn_diff (P ρ : Set V) : Fn E (X \ P) ρ ↔ Fn E X (ρ \ P) := by
  constructor
  · rintro ⟨a, b, h1, h2, h3, h4, h5⟩
    exact ⟨a, b, h1, h2.1, h3.1, ⟨h4, h2.2⟩, ⟨h5, h3.2⟩⟩
  · rintro ⟨a, b, h1, h2, h3, h4, h5⟩
    exact ⟨a, b, h1, ⟨h2, h4.2⟩, ⟨h3, h5.2⟩, h4.1, h5.1⟩

lemma out_live {C : Ckt V} {P : Finset V} (hC : Comp E X C) (h : HasEdge E (X \ ↑P)) :
    ¬ Dd C P C.out := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  refine not_not.mpr ((hC _).mpr ⟨u, v, huv, hu.1, hv.1, ?_, ?_⟩)
  · simpa using hu.2
  · simpa using hv.2

end opt

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

theorem vl_red {g : ℕ} {w u : V ⊕ ℕ} (hu : Vl C u) (hne : u ≠ Sum.inr g) : Vl (red C g w) u :=
  fun k hk => Finset.mem_erase.mpr ⟨fun e => hne (e ▸ hk), hu k hk⟩

theorem rk_ne {g : ℕ} {w : V ⊕ ℕ} (hr : rk w ≤ g) : w ≠ Sum.inr g := by
  rintro rfl
  simp [rk] at hr

theorem red_arg (hW : Wf C) {g : ℕ} {w u : V ⊕ ℕ} (hg : g ∈ C.G) (hw : Vl C w) (hr : rk w ≤ g)
    (hu : Vl C u) : Vl (red C g w) (if u = Sum.inr g then w else u) ∧
      rk (if u = Sum.inr g then w else u) ≤ rk u := by
  split_ifs with h
  · subst h
    refine ⟨vl_red hw (rk_ne hr), ?_⟩
    simp only [rk, Sum.elim_inr] at hr ⊢
    omega
  · exact ⟨vl_red hu h, le_rfl⟩

theorem red_wf (hW : Wf C) {g : ℕ} {w : V ⊕ ℕ} (hg : g ∈ C.G) (hw : Vl C w) (hr : rk w ≤ g) :
    Wf (red C g w) := by
  refine ⟨fun k hk => ?_, (red_arg hW hg hw hr hW.2).1⟩
  have hkG := (Finset.mem_erase.mp hk).2
  have h1 := red_arg hW hg hw hr (hW.1 k hkG).1.1
  have h2 := red_arg hW hg hw hr (hW.1 k hkG).2.1
  exact ⟨⟨h1.1, h1.2.trans (hW.1 k hkG).1.2⟩, ⟨h2.1, h2.2.trans (hW.1 k hkG).2.2⟩⟩

theorem red_val_eq (hW : Wf C) {g : ℕ} {w : V ⊕ ℕ} (hg : g ∈ C.G) (hw : Vl C w) (hr : rk w ≤ g)
    {ρ : Set V} (h : C.val ρ (Sum.inr g) ↔ C.val ρ w) :
    ∀ u, Vl C u → u ≠ Sum.inr g → ((red C g w).val ρ u ↔ C.val ρ u) := by
  intro u hu hne
  refine wire_ind' (red_wf hW hg hw hr) (p := fun u => (red C g w).val ρ u ↔ C.val ρ u)
    (fun v => Iff.rfl) (fun k hk hl hr' => ?_) u (vl_red hu hne)
  have hkG := (Finset.mem_erase.mp hk).2
  have e : ∀ a : V ⊕ ℕ, C.val ρ (if a = Sum.inr g then w else a) ↔ C.val ρ a := by
    intro a
    split_ifs with ha
    · rw [ha]; exact h.symm
    · exact Iff.rfl
  have hl2 := hl.trans (e (C.l k))
  have hr2 := hr'.trans (e (C.r k))
  rw [val_gate (red_wf hW hg hw hr) hk, val_gate hW hkG]
  change (if C.op k = true then _ else _) ↔ _
  split_ifs
  · exact and_congr hl2 hr2
  · exact or_congr hl2 hr2

theorem red_val_le (hW : Wf C) {g : ℕ} {w : V ⊕ ℕ} (hg : g ∈ C.G) (hw : Vl C w) (hr : rk w ≤ g)
    {ρ : Set V} (h : C.val ρ w → C.val ρ (Sum.inr g)) :
    ∀ u, Vl C u → u ≠ Sum.inr g → (red C g w).val ρ u → C.val ρ u := by
  intro u hu hne
  refine wire_ind' (red_wf hW hg hw hr) (p := fun u => (red C g w).val ρ u → C.val ρ u)
    (fun v => id) (fun k hk hl hr' => ?_) u (vl_red hu hne)
  have hkG := (Finset.mem_erase.mp hk).2
  have e : ∀ a : V ⊕ ℕ, C.val ρ (if a = Sum.inr g then w else a) → C.val ρ a := by
    intro a
    split_ifs with ha
    · rw [ha]; exact h
    · exact id
  have hl2 := fun x => e (C.l k) (hl x)
  have hr2 := fun x => e (C.r k) (hr' x)
  rw [val_gate (red_wf hW hg hw hr) hk, val_gate hW hkG]
  change (if C.op k = true then _ else _) → _
  split_ifs
  · exact And.imp hl2 hr2
  · exact Or.imp hl2 hr2

theorem opt_no_dup (hC : Opt E X ∅ C) {g : ℕ} {w : V ⊕ ℕ} (hg : g ∈ C.G) (hw : Vl C w)
    (hr : rk w ≤ g) (h : ∀ ρ, C.val ρ (Sum.inr g) ↔ C.val ρ w) : False := by
  obtain ⟨⟨hW, hcl, hcomp, _⟩, hmin⟩ := hC
  have hgood : Good E X ∅ (red C g w) := by
    refine ⟨red_wf hW hg hw hr, ?_, ?_, fun y hy => hy.elim⟩
    · intro k hk ho v hv
      have hk' := Finset.mem_erase.mp hk
      exact hcl k hk'.2 ho v ((red_val_eq hW hg hw hr (h {v}) _ (vl_inr hk'.2)
        (fun e => hk'.1 (Sum.inr.inj e))).mp hv)
    · intro ρ
      rw [← hcomp ρ]
      show (red C g w).val ρ (if C.out = Sum.inr g then w else C.out) ↔ _
      split_ifs with ho
      · rw [ho]
        exact (red_val_eq hW hg hw hr (h ρ) w hw (rk_ne hr)).trans (h ρ).symm
      · exact red_val_eq hW hg hw hr (h ρ) _ hW.2 ho
  have h1 := hmin _ hgood
  have h2 : (red C g w).G.card < C.G.card := Finset.card_erase_lt_of_mem hg
  omega

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

theorem zero (hC : Good E X Y C) (P : Finset V) (hout : ¬ Dd C P C.out) :
    ∃ C' : Ckt V, Good E (X \ ↑P) Y C' ∧ C'.G = su C P ∧ C'.op = C.op := by
  obtain ⟨hW, hcl, hcomp, hrig⟩ := hC
  have hrep : ∀ w, Vl C w → (¬ Dd C P w → ∃ w', Vl C w' ∧ ¬ Dd C P w' ∧ rk w' ≤ rk w ∧
      (∀ k, w' = Sum.inr k → k ∈ su C P) ∧
      (∀ ρ : Set V, (∀ p ∈ P, p ∉ ρ) → (C.val ρ w ↔ C.val ρ w')) ∧
      ∀ v, w' = Sum.inl v → w = Sum.inl v ∨ ∃ g, Rd C g (Sum.inl v) ∧ C.op g = false) := by
    refine wire_ind' hW (fun v hv => ⟨Sum.inl v, vl_inl C v, hv, le_rfl, (fun k hk => by cases hk),
      (fun _ _ => Iff.rfl), (fun u hu => Or.inl hu)⟩) (fun g hg hl hr hlive => ?_)
    have hk := kinds_cover P hg
    have hnd := mt (kinds_dead hW P hg).mpr hlive
    push Not at hnd
    rcases hk with hk | hk | hk | hk
    · exact absurd hk hnd.1
    · exact absurd hk hnd.2
    · obtain ⟨_, ho, hd⟩ := Finset.mem_filter.mp hk
      by_cases hdl : Dd C P (C.l g)
      · obtain ⟨w', h1, h2, h3, h4, h5, h6⟩ := hr (hd.mp hdl)
        refine ⟨w', h1, h2, ?_, h4, ?_, ?_⟩
        · refine h3.trans ((hW.1 g hg).2.2.trans ?_); simp [rk]
        · intro ρ hρ
          rw [val_or hW hg ho, ← h5 ρ hρ]
          exact or_iff_right (dd_off hW (hW.1 g hg).1.1 hdl hρ)
        · intro v hv
          rcases h6 v hv with h | h
          · exact Or.inr ⟨g, ⟨hg, Or.inr h⟩, ho⟩
          · exact Or.inr h
      · have hdr : Dd C P (C.r g) := by tauto
        obtain ⟨w', h1, h2, h3, h4, h5, h6⟩ := hl hdl
        refine ⟨w', h1, h2, ?_, h4, ?_, ?_⟩
        · refine h3.trans ((hW.1 g hg).1.2.trans ?_); simp [rk]
        · intro ρ hρ
          rw [val_or hW hg ho, ← h5 ρ hρ]
          exact or_iff_left (dd_off hW (hW.1 g hg).2.1 hdr hρ)
        · intro v hv
          rcases h6 v hv with h | h
          · exact Or.inr ⟨g, ⟨hg, Or.inl h⟩, ho⟩
          · exact Or.inr h
    · exact ⟨Sum.inr g, vl_inr hg, hlive, le_rfl, (fun k e => by cases e; exact hk),
        (fun _ _ => Iff.rfl), (fun v hv => by cases hv)⟩
  have hrep' : ∀ w, ∃ w', Vl C w → ¬ Dd C P w → Vl C w' ∧ ¬ Dd C P w' ∧ rk w' ≤ rk w ∧
      (∀ k, w' = Sum.inr k → k ∈ su C P) ∧
      (∀ ρ : Set V, (∀ p ∈ P, p ∉ ρ) → (C.val ρ w ↔ C.val ρ w')) ∧
      ∀ v, w' = Sum.inl v → w = Sum.inl v ∨ ∃ g, Rd C g (Sum.inl v) ∧ C.op g = false := by
    intro w
    by_cases h : Vl C w ∧ ¬ Dd C P w
    · obtain ⟨w', hw'⟩ := hrep w h.1 h.2
      exact ⟨w', fun _ _ => hw'⟩
    · exact ⟨w, fun a b => absurd ⟨a, b⟩ h⟩
  choose r hr using hrep'
  set D : Ckt V := Ckt.mk (su C P) C.op (fun g => r (C.l g)) (fun g => r (C.r g)) (r C.out) with hD
  have hsu : ∀ g ∈ su C P, g ∈ C.G ∧ ¬ Dd C P (C.l g) ∧ ¬ Dd C P (C.r g) := fun g hg =>
    Finset.mem_filter.mp hg
  have hDW : Wf D := by
    refine ⟨fun g hg => ?_, fun k hk => (hr _ hW.2 hout).2.2.2.1 k hk⟩
    obtain ⟨hgG, hl, hr'⟩ := hsu g hg
    have a := hr _ (hW.1 g hgG).1.1 hl
    have b := hr _ (hW.1 g hgG).2.1 hr'
    exact ⟨⟨fun k hk => a.2.2.2.1 k hk, a.2.2.1.trans (hW.1 g hgG).1.2⟩,
      ⟨fun k hk => b.2.2.2.1 k hk, b.2.2.1.trans (hW.1 g hgG).2.2⟩⟩
  have havoid : ∀ ρ : Set V, ∀ p ∈ P, p ∉ ρ \ (↑P : Set V) := fun ρ p hp h => h.2 hp
  have hval : ∀ ρ, ∀ u, Vl D u → ¬ Dd C P u → (D.val ρ u ↔ C.val (ρ \ ↑P) u) := by
    intro ρ
    refine wire_ind' hDW (fun v hv => ?_) (fun g hg ihl ihr _ => ?_)
    · rw [dd_inl] at hv
      show v ∈ ρ ↔ v ∈ ρ \ ↑P
      simp [hv]
    · obtain ⟨hgG, hl, hr'⟩ := hsu g hg
      have a := hr _ (hW.1 g hgG).1.1 hl
      have b := hr _ (hW.1 g hgG).2.1 hr'
      have ihl' := (ihl a.2.1).trans (a.2.2.2.2.1 _ (havoid ρ)).symm
      have ihr' := (ihr b.2.1).trans (b.2.2.2.2.1 _ (havoid ρ)).symm
      rw [val_gate hDW hg, val_gate hW hgG]
      change (if C.op g = true then _ else _) ↔ _
      split_ifs
      · exact and_congr ihl' ihr'
      · exact or_congr ihl' ihr'
  have hlive : ∀ g ∈ su C P, ¬ Dd C P (Sum.inr g) := by
    intro g hg
    obtain ⟨hgG, hl, hr'⟩ := hsu g hg
    rw [dd_gate hW P hgG]
    split_ifs <;> tauto
  have hrd : ∀ y ∈ Y, ∀ w, Vl C w → ¬ Dd C P w → r w = Sum.inl y → w = Sum.inl y := by
    intro y hy w hw hd he
    rcases (hr w hw hd).2.2.2.2.2 y he with h | ⟨g, hg, ho⟩
    · exact h
    · rw [(hrig y hy).2 g hg] at ho; cases ho
  refine ⟨D, ⟨hDW, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro g hg ho v hv
    have h1 := (hval {v} _ (vl_inr hg) (hlive g hg)).mp hv
    exact hcl g (hsu g hg).1 ho v (val_mono hW Set.sdiff_subset _ (vl_inr (hsu g hg).1) h1)
  · intro ρ
    have a := hr _ hW.2 hout
    rw [fn_diff, ← hcomp]
    exact (hval ρ _ hDW.2 a.2.1).trans (a.2.2.2.2.1 _ (havoid ρ)).symm
  · intro y hy
    constructor
    · refine le_trans ?_ (hrig y hy).1
      unfold fo
      refine le_trans (Finset.sum_le_sum (fun g hg => ?_))
        (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _ : su C P ⊆ C.G))
      obtain ⟨hgG, hl, hr'⟩ := hsu g hg
      refine Nat.add_le_add ?_ ?_
      · show (if r (C.l g) = Sum.inl y then 1 else 0) ≤ _
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd (hrd y hy _ (hW.1 g hgG).1.1 hl h1) h2
        · exact Nat.zero_le _
        · exact le_rfl
      · show (if r (C.r g) = Sum.inl y then 1 else 0) ≤ _
        split_ifs with h1 h2
        · exact le_rfl
        · exact absurd (hrd y hy _ (hW.1 g hgG).2.1 hr' h1) h2
        · exact Nat.zero_le _
        · exact le_rfl
    · intro g hg
      obtain ⟨hgG, hl, hr'⟩ := hsu g hg.1
      refine (hrig y hy).2 g ⟨hgG, ?_⟩
      rcases hg.2 with h | h
      · exact Or.inl (hrd y hy _ (hW.1 g hgG).1.1 hl h)
      · exact Or.inr (hrd y hy _ (hW.1 g hgG).2.1 hr' h)

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

theorem count_part (C : Ckt V) (P : Finset V) : kl C P + (su C P).card = C.G.card := by
  unfold kl
  have hd1 : Disjoint (al C P) (be C P) := by
    rw [Finset.disjoint_left]; intro g h1 h2
    simp only [al, be, Finset.mem_filter] at h1 h2; tauto
  have hd2 : Disjoint (al C P ∪ be C P) (ga C P) := by
    rw [Finset.disjoint_left]; intro g h1 h2
    simp only [al, be, ga, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1
    · tauto
    · have := h1.2.1.symm.trans h2.2.1
      simp at this
  have hd3 : Disjoint (al C P ∪ be C P ∪ ga C P) (su C P) := by
    rw [Finset.disjoint_left]; intro g h1 h2
    simp only [al, be, ga, su, Finset.mem_union, Finset.mem_filter] at h1 h2; tauto
  rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2,
    ← Finset.card_union_of_disjoint hd3]
  congr 1
  ext g
  constructor
  · simp only [Finset.mem_union]
    rintro (((h | h) | h) | h)
    all_goals exact (Finset.mem_filter.mp h).1
  · intro hg
    simp only [Finset.mem_union]
    have := kinds_cover P hg
    tauto

theorem count_core (hU : Useful C) {P : Finset V} (hP : ∀ p ∈ P, 1 ≤ fo C (Sum.inl p)) :
    (al C P).card + (ga C P).card + (if Dd C P C.out then 1 else 0) = P.card + exc C P := by
  have hW := hU.1
  have hslots : ∑ w ∈ dw C P, fo C w = 2 * (al C P).card + (be C P).card + (ga C P).card := by
    unfold fo
    rw [Finset.sum_comm]
    have h1 : ∀ g ∈ C.G, ∑ w ∈ dw C P, ((if C.l g = w then 1 else 0) +
        (if C.r g = w then 1 else 0)) =
        (if g ∈ al C P then 2 else 0) + (if g ∈ be C P then 1 else 0) +
          (if g ∈ ga C P then 1 else 0) := by
      intro g hg
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
      have e1 : C.l g ∈ dw C P ↔ Dd C P (C.l g) := by
        rw [mem_dw]; exact and_iff_right (hW.1 g hg).1.1
      have e2 : C.r g ∈ dw C P ↔ Dd C P (C.r g) := by
        rw [mem_dw]; exact and_iff_right (hW.1 g hg).2.1
      simp only [e1, e2, al, be, ga, Finset.mem_filter, hg, true_and]
      by_cases a : Dd C P (C.l g) <;> by_cases b : Dd C P (C.r g) <;> cases C.op g <;> simp [a, b]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have e : ∀ (A : Finset ℕ) (n : ℕ), A ⊆ C.G →
        ∑ g ∈ C.G, (if g ∈ A then n else 0) = n * A.card := by
      intro A n hA
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [e (al C P) 2 (Finset.filter_subset _ _), e (be C P) 1 (Finset.filter_subset _ _),
      e (ga C P) 1 (Finset.filter_subset _ _)]
    omega
  have hcard : (dw C P).card = P.card + (al C P).card + (be C P).card := by
    unfold dw
    rw [Finset.card_disjSum, add_assoc]
    congr 1
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext g
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hg, hd⟩; exact (kinds_dead hW P hg).mp hd
      · intro h
        have hg : g ∈ C.G := by
          rcases h with h | h <;> exact (Finset.mem_filter.mp h).1
        exact ⟨hg, (kinds_dead hW P hg).mpr h⟩
    · rw [Finset.disjoint_left]; intro g h1 h2
      simp only [al, be, Finset.mem_filter] at h1 h2; tauto
  have hpos : ∀ w ∈ (dw C P).erase C.out, 1 ≤ fo C w := by
    intro w hw
    rw [Finset.mem_erase] at hw
    rcases w with v | g
    · exact hP v ((mem_dw_inl C P v).mp hw.2)
    · exact hU.2.2 g ((mem_dw_inr C P g).mp hw.2).1 hw.1
  have hexc : exc C P + ((dw C P).erase C.out).card = ∑ w ∈ (dw C P).erase C.out, fo C w := by
    unfold exc
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w hw => Nat.sub_add_cancel (hpos w hw)
  by_cases ho : Dd C P C.out
  · have hm : C.out ∈ dw C P := mem_dw.mpr ⟨hW.2, ho⟩
    have h2 := Finset.sum_erase_add (dw C P) (fo C) hm
    have h3 := Finset.card_erase_add_one hm
    have h4 := hU.2.1
    rw [if_pos ho]
    omega
  · have hm : C.out ∉ dw C P := fun h => ho (mem_dw.mp h).2
    rw [Finset.erase_eq_of_notMem hm] at hexc
    rw [if_neg ho]
    omega

theorem count_live (hU : Useful C) {P : Finset V} (hP : ∀ p ∈ P, 1 ≤ fo C (Sum.inl p))
    (ho : ¬ Dd C P C.out) : (al C P).card + (ga C P).card = P.card + exc C P := by
  have := count_core hU hP
  rw [if_neg ho] at this
  simpa using this

theorem count_dead (hU : Useful C) {P : Finset V} (hP : ∀ p ∈ P, 1 ≤ fo C (Sum.inl p))
    (ho : Dd C P C.out) : (al C P).card + (ga C P).card + 1 = P.card + exc C P := by
  have := count_core hU hP
  rwa [if_pos ho] at this

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

theorem opt_useful (hC : Opt E X Y C) : Useful C := by
  obtain ⟨⟨hW, hcl, hcomp, hrig⟩, hmin⟩ := hC
  have hdel : ∀ g ∈ C.G, (∀ k, ¬ Rd C k (Sum.inr g)) → C.out = Sum.inr g := by
    intro g hg hun
    by_contra hout
    set D : Ckt V := Ckt.mk (C.G.erase g) C.op C.l C.r C.out with hD
    have hvl : ∀ u, Vl C u → u ≠ Sum.inr g → Vl D u := fun u hu hne k hk =>
      Finset.mem_erase.mpr ⟨fun e => hne (e ▸ hk), hu k hk⟩
    have hDW : Wf D := by
      refine ⟨fun k hk => ?_, hvl _ hW.2 hout⟩
      have hkG := (Finset.mem_erase.mp hk).2
      exact ⟨⟨hvl _ (hW.1 k hkG).1.1 (fun e => hun k ⟨hkG, Or.inl e⟩), (hW.1 k hkG).1.2⟩,
        ⟨hvl _ (hW.1 k hkG).2.1 (fun e => hun k ⟨hkG, Or.inr e⟩), (hW.1 k hkG).2.2⟩⟩
    have hval : ∀ ρ, ∀ u, Vl D u → (D.val ρ u ↔ C.val ρ u) := by
      intro ρ
      refine wire_ind' hDW (fun v => Iff.rfl) (fun k hk hl hr => ?_)
      have hkG := (Finset.mem_erase.mp hk).2
      rw [val_gate hDW hk, val_gate hW hkG]
      change (if C.op k = true then _ else _) ↔ _
      split_ifs
      · exact and_congr hl hr
      · exact or_congr hl hr
    have hfo : ∀ w, fo D w ≤ fo C w := fun w =>
      Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    have hgood : Good E X Y D := by
      refine ⟨hDW, ?_, fun ρ => (hval ρ _ hDW.2).trans (hcomp ρ), ?_⟩
      · intro k hk ho v hv
        exact hcl k (Finset.mem_erase.mp hk).2 ho v ((hval _ _ (vl_inr hk)).mp hv)
      · intro y hy
        refine ⟨(hfo _).trans (hrig y hy).1, fun k hk => (hrig y hy).2 k ?_⟩
        exact ⟨(Finset.mem_erase.mp hk.1).2, hk.2⟩
    have h1 := hmin _ hgood
    have h2 : D.G.card < C.G.card := Finset.card_erase_lt_of_mem hg
    omega
  have hun : fo C C.out = 0 := by
    by_contra h0
    obtain ⟨k, hk⟩ := fo_pos.mp (Nat.one_le_iff_ne_zero.mpr h0)
    have hne : C.G.Nonempty := ⟨k, hk.1⟩
    have hm := hdel (C.G.max' hne) (C.G.max'_mem hne) (by
      intro k' hk'
      have h1 := (rd_vl hW hk').2
      have h2 := C.G.le_max' k' hk'.1
      simp only [rk, Sum.elim_inr] at h1
      omega)
    rw [hm] at hk
    have h1 := (rd_vl hW hk).2
    have h2 := C.G.le_max' k hk.1
    simp only [rk, Sum.elim_inr] at h1
    omega
  refine ⟨hW, hun, fun g hg hne => ?_⟩
  rw [fo_pos]
  by_contra hno
  push Not at hno
  exact hne (hdel g hg hno).symm

theorem read_pos (hE : Gr E) (hC : Good E X Y C) {u v : V} (hv : v ∈ X) (hu : u ∈ X)
    (h : E v u) : 1 ≤ fo C (Sum.inl v) := by
  obtain ⟨hW, _, hcomp, _⟩ := hC
  rw [fo_pos]
  by_contra hno
  push Not at hno
  have hne : C.out ≠ Sum.inl v := by
    intro e
    refine fn_single (X := X) hE v ((hcomp {v}).mp ?_)
    rw [e]; exact Set.mem_singleton v
  have h1 : C.val {v, u} C.out := (hcomp _).mpr ((fn_pair hE).mpr ⟨h, hv, hu⟩)
  have h2 := ignore hW (v := v) (n := rk C.out) (σ := {u}) (fun k hk => absurd hk (hno k))
    (by
      intro a ha hm
      rcases hm with rfl | hm
      · exact absurd rfl ha
      · exact hm) _ hW.2 le_rfl hne h1
  exact fn_single (X := X) hE u ((hcomp _).mp h2)

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

def addOr (D : Ckt V) (a b : V ⊕ ℕ) : Ckt V :=
  Ckt.mk (insert (D.G.sup id + 1) D.G) (fun i => if i = D.G.sup id + 1 then false else D.op i)
    (fun i => if i = D.G.sup id + 1 then a else D.l i)
    (fun i => if i = D.G.sup id + 1 then b else D.r i) (Sum.inr (D.G.sup id + 1))

omit [DecidableEq V] in
theorem addOr_fresh (D : Ckt V) : D.G.sup id + 1 ∉ D.G := fun h => by
  have := Finset.le_sup (f := id) h
  simp only [id] at this
  omega

omit [DecidableEq V] in
theorem addOr_rk {D : Ckt V} {a : V ⊕ ℕ} (ha : Vl D a) : rk a ≤ D.G.sup id + 1 := by
  rcases a with v | k
  · simp [rk]
  · have := Finset.le_sup (f := id) (ha k rfl)
    simp only [id] at this
    simpa [rk] using this

omit [DecidableEq V] in
theorem addOr_vl {D : Ckt V} {a b u : V ⊕ ℕ} (hu : Vl D u) : Vl (addOr D a b) u :=
  fun k hk => Finset.mem_insert_of_mem (hu k hk)

omit [DecidableEq V] in
theorem addOr_wf {D : Ckt V} (hW : Wf D) {a b : V ⊕ ℕ} (ha : Vl D a) (hb : Vl D b) :
    Wf (addOr D a b) := by
  refine ⟨fun g hg => ?_, fun k hk => by cases hk; exact Finset.mem_insert_self _ _⟩
  show (Vl _ (if g = _ then a else D.l g) ∧ rk (if g = _ then a else D.l g) ≤ g) ∧
    (Vl _ (if g = _ then b else D.r g) ∧ rk (if g = _ then b else D.r g) ≤ g)
  by_cases h : g = D.G.sup id + 1
  · rw [if_pos h, if_pos h, h]
    exact ⟨⟨addOr_vl ha, addOr_rk ha⟩, ⟨addOr_vl hb, addOr_rk hb⟩⟩
  · rw [if_neg h, if_neg h]
    have hgG := Finset.mem_of_mem_insert_of_ne hg h
    have := hW.1 g hgG
    exact ⟨⟨addOr_vl this.1.1, this.1.2⟩, ⟨addOr_vl this.2.1, this.2.2⟩⟩

omit [DecidableEq V] in
theorem addOr_val {D : Ckt V} (hW : Wf D) {a b : V ⊕ ℕ} (ha : Vl D a) (hb : Vl D b)
    (ρ : Set V) : ∀ u, Vl D u → ((addOr D a b).val ρ u ↔ D.val ρ u) := by
  refine wire_ind' hW (fun v => Iff.rfl) (fun g hg hl hr => ?_)
  have hne : g ≠ D.G.sup id + 1 := fun e => addOr_fresh D (e ▸ hg)
  rw [val_gate (addOr_wf hW ha hb) (Finset.mem_insert_of_mem hg), val_gate hW hg]
  show (if (if g = D.G.sup id + 1 then false else D.op g) = true then
    (addOr D a b).val ρ (if g = D.G.sup id + 1 then a else D.l g) ∧
      (addOr D a b).val ρ (if g = D.G.sup id + 1 then b else D.r g) else
    (addOr D a b).val ρ (if g = D.G.sup id + 1 then a else D.l g) ∨
      (addOr D a b).val ρ (if g = D.G.sup id + 1 then b else D.r g)) ↔ _
  simp only [if_neg hne]
  split_ifs
  · exact and_congr hl hr
  · exact or_congr hl hr

omit [DecidableEq V] in
theorem addOr_out {D : Ckt V} (hW : Wf D) {a b : V ⊕ ℕ} (ha : Vl D a) (hb : Vl D b)
    (ρ : Set V) : (addOr D a b).val ρ (addOr D a b).out ↔ D.val ρ a ∨ D.val ρ b := by
  have hm : D.G.sup id + 1 ∈ (addOr D a b).G := Finset.mem_insert_self _ _
  rw [← addOr_val hW ha hb ρ a ha, ← addOr_val hW ha hb ρ b hb]
  have := val_or (addOr_wf hW ha hb) hm (show (if _ = _ then false else _) = false from if_pos rfl) ρ
  have e1 : (addOr D a b).l (D.G.sup id + 1) = a := if_pos rfl
  have e2 : (addOr D a b).r (D.G.sup id + 1) = b := if_pos rfl
  rw [e1, e2] at this
  exact this

noncomputable def nOff (E : V → V → Prop) (X : Set V) (C : Ckt V) : ℕ :=
  (C.G.filter (fun g => ¬ ∀ ρ, C.val ρ (Sum.inr g) → Fn E X ρ)).card

theorem side_le (hE : Gr E) (hC : Good E X ∅ C) {y z : V} (hp : Pend E X y z)
    (hf : fo C (Sum.inl y) ≤ 1) {g : ℕ} (hg : g ∈ C.G) (ho : C.op g = false) {k : V ⊕ ℕ}
    (hk : (C.l g = Sum.inl y ∧ C.r g = k) ∨ (C.r g = Sum.inl y ∧ C.l g = k)) :
    ∀ ρ, C.val ρ k → Fn E X ρ := by
  obtain ⟨hW, _, hcomp, _⟩ := hC
  have hgy : Rd C g (Sum.inl y) := ⟨hg, by rcases hk with h | h <;> simp [h.1]⟩
  have hgk : Rd C g k := ⟨hg, by rcases hk with h | h <;> simp [h.2]⟩
  have hky : k ≠ Sum.inl y := by
    rintro rfl
    have : 2 ≤ fo C (Sum.inl y) := by
      rcases hk with h | h
      · exact fo_two_of_both hg h.1 h.2
      · exact fo_two_of_both hg h.2 h.1
    omega
  have hout : C.out ≠ Sum.inl y := by
    intro e
    refine fn_single (X := X) hE y ((hcomp {y}).mp ?_)
    rw [e]; exact Set.mem_singleton y
  have hyz : y ≠ z := by
    rintro rfl
    exact hE.2 _ hp.2.2.1
  intro ρ hρ
  have h1 : C.val ((ρ \ {y}) ∪ {z}) k := by
    refine ignore hW (v := y) (n := g) (fun i hi => (rd_unique hf hgy hi).le) ?_ k
      (rd_vl hW hgk).1 (rd_vl hW hgk).2 hky hρ
    intro u hu hm
    exact Or.inl ⟨hm, hu⟩
  have h2 : C.val ((ρ \ {y}) ∪ {z}) (Sum.inr g) := by
    rw [val_or hW hg ho]
    rcases hk with h | h
    · exact Or.inr (h.2 ▸ h1)
    · exact Or.inl (h.2 ▸ h1)
  have h3 : C.val (((ρ \ {y}) ∪ {z}) ∪ {y}) C.out :=
    (hcomp _).mpr ⟨y, z, hp.2.2.1, hp.1, hp.2.1, Or.inr rfl, Or.inl (Or.inr rfl)⟩
  have h4 : C.val ((ρ \ {y}) ∪ {z}) C.out := by
    refine escape hW {Sum.inl y} (ρ := ((ρ \ {y}) ∪ {z}) ∪ {y}) ?_ ?_ _ hW.2 hout h3
    · intro v hv hm
      rcases hm with hm | hm
      · exact hm
      · exact absurd (congrArg Sum.inl hm) hv
    · intro i hi _ hb _
      have : i = g := rd_unique hf ⟨hi, hb⟩ hgy
      rw [this]; exact h2
  obtain ⟨a, b, hab, ha, hb, ha', hb'⟩ := (hcomp _).mp h4
  have hin : ∀ c d, E c d → d ∈ X → c ∈ (ρ \ {y}) ∪ {z} → d ∈ (ρ \ {y}) ∪ {z} → c ∈ ρ := by
    intro c d hcd hd hc hdm
    rcases hc with hc | hc
    · exact hc.1
    · rw [Set.mem_singleton_iff] at hc
      rw [hc] at hcd
      rw [hp.2.2.2 d hd hcd] at hdm
      rcases hdm with h | h
      · exact absurd rfl h.2
      · exact absurd h hyz
  exact ⟨a, b, hab, ha, hb, hin a b hab hb ha' hb', hin b a (hE.1 _ _ hab) ha hb' ha'⟩

theorem norm_step (hE : Gr E) (hC : Good E X ∅ C) {y z : V} (hp : Pend E X y z)
    (hf : fo C (Sum.inl y) ≤ 1) {g : ℕ} (hg : Rd C g (Sum.inl y)) (ho : C.op g = false) :
    ∃ C' : Ckt V, Good E X ∅ C' ∧ C'.G.card = C.G.card ∧ nAnd C' = nAnd C ∧
      nOff E X C' < nOff E X C := by
  have hgG := hg.1
  obtain ⟨k, hk⟩ : ∃ k, (C.l g = Sum.inl y ∧ C.r g = k) ∨ (C.r g = Sum.inl y ∧ C.l g = k) := by
    rcases hg.2 with h | h
    · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨h, rfl⟩⟩
  have hle := side_le hE hC hp hf hgG ho hk
  obtain ⟨hW, hcl, hcomp, _⟩ := hC
  have hgk : Rd C g k := ⟨hgG, by rcases hk with h | h <;> simp [h.2]⟩
  have hkv := rd_vl hW hgk
  have hyv : Vl C (Sum.inl y) := vl_inl C y
  have hyr : rk (Sum.inl y : V ⊕ ℕ) ≤ g := by simp [rk]
  have hgval : ∀ ρ, C.val ρ (Sum.inr g) ↔ y ∈ ρ ∨ C.val ρ k := by
    intro ρ
    rw [val_or hW hgG ho]
    rcases hk with h | h
    · rw [h.1, h.2]; exact Iff.rfl
    · rw [h.1, h.2]; exact or_comm
  have hout : C.out ≠ Sum.inr g := by
    intro e
    refine fn_single (X := X) hE y ((hcomp {y}).mp ?_)
    rw [e, hgval]; exact Or.inl rfl
  set R := red C g (Sum.inl y) with hR
  have hRW : Wf R := red_wf hW hgG hyv hyr
  have hRout : R.out = C.out := if_neg hout
  have hkR : Vl R k := vl_red hkv.1 (rk_ne hkv.2)
  have hoR : Vl R C.out := vl_red hW.2 hout
  have hRle : ∀ ρ, ∀ u, Vl C u → u ≠ Sum.inr g → R.val ρ u → C.val ρ u := fun ρ =>
    red_val_le hW hgG hyv hyr (fun h => (hgval ρ).mpr (Or.inl h))
  have hReq : ∀ ρ, ¬ C.val ρ k → ∀ u, Vl C u → u ≠ Sum.inr g → (R.val ρ u ↔ C.val ρ u) := by
    intro ρ hρ
    refine red_val_eq hW hgG hyv hyr ?_
    rw [hgval]
    exact or_iff_left hρ
  have hkeq : ∀ ρ, R.val ρ k ↔ C.val ρ k := by
    intro ρ
    have : ∀ u, Vl C u → rk u ≤ g → (R.val ρ u ↔ C.val ρ u) := by
      refine wire_ind' hW (fun v _ => Iff.rfl) (fun i hi hl hr hrk => ?_)
      have hig : i < g := by simpa [rk] using hrk
      have hiR : i ∈ R.G := Finset.mem_erase.mpr ⟨by omega, hi⟩
      have e1 : R.l i = C.l i := if_neg (rk_ne ((hW.1 i hi).1.2.trans hig.le))
      have e2 : R.r i = C.r i := if_neg (rk_ne ((hW.1 i hi).2.2.trans hig.le))
      have e3 : R.op i = C.op i := rfl
      rw [val_gate hRW hiR, val_gate hW hi, e1, e2, e3]
      have hl' := hl ((hW.1 i hi).1.2.trans hig.le)
      have hr' := hr ((hW.1 i hi).2.2.trans hig.le)
      split_ifs
      · exact and_congr hl' hr'
      · exact or_congr hl' hr'
    exact this k hkv.1 hkv.2
  set D := addOr R C.out k with hD
  have hDW : Wf D := addOr_wf hRW hoR hkR
  have hDval : ∀ ρ, ∀ u, Vl R u → (D.val ρ u ↔ R.val ρ u) := addOr_val hRW hoR hkR
  have hDout : ∀ ρ, D.val ρ D.out ↔ Fn E X ρ := by
    intro ρ
    rw [hD, addOr_out hRW hoR hkR, hkeq]
    constructor
    · rintro (h | h)
      · exact (hcomp ρ).mp (hRle ρ _ hW.2 hout h)
      · exact hle ρ h
    · intro h
      by_cases hρ : C.val ρ k
      · exact Or.inr hρ
      · exact Or.inl ((hReq ρ hρ _ hW.2 hout).mpr ((hcomp ρ).mpr h))
  set m := R.G.sup id + 1 with hm
  have hmR : m ∉ R.G := addOr_fresh R
  have hDG : D.G = insert m R.G := rfl
  have hRG : R.G = C.G.erase g := rfl
  have hop : ∀ i ∈ R.G, D.op i = C.op i := by
    intro i hi
    have hne : i ≠ m := by rintro rfl; exact hmR hi
    exact if_neg hne
  have hopm : D.op m = false := if_pos rfl
  have hcard : C.G.card = R.G.card + 1 := by
    rw [hRG, Finset.card_erase_add_one hgG]
  refine ⟨D, ⟨hDW, ?_, hDout, fun y hy => hy.elim⟩, ?_, ?_, ?_⟩
  · intro i hi hio v hv
    rcases Finset.mem_insert.mp (hDG ▸ hi) with h | h
    · rw [h, hopm] at hio; cases hio
    · have hi' := Finset.mem_erase.mp (hRG ▸ h)
      rw [hop i h] at hio
      refine hcl i hi'.2 hio v (hRle _ _ (vl_inr hi'.2) (fun e => hi'.1 (Sum.inr.inj e)) ?_)
      exact (hDval _ _ (vl_inr h)).mp hv
  · rw [hDG, Finset.card_insert_of_notMem hmR, hcard]
  · unfold nAnd
    congr 1
    ext i
    simp only [Finset.mem_filter, hDG, Finset.mem_insert]
    constructor
    · rintro ⟨h | h, hio⟩
      · rw [h, hopm] at hio; cases hio
      · exact ⟨(Finset.mem_erase.mp (hRG ▸ h)).2, hop i h ▸ hio⟩
    · rintro ⟨hi, hio⟩
      have hiR : i ∈ R.G := by
        rw [hRG]
        refine Finset.mem_erase.mpr ⟨?_, hi⟩
        rintro rfl
        rw [ho] at hio; cases hio
      exact ⟨Or.inr hiR, (hop i hiR).trans hio⟩
  · unfold nOff
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨g, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨hgG, fun h => fn_single (X := X) hE y (h {y} ?_)⟩
        rw [hgval]; exact Or.inl rfl
      · rw [Finset.mem_filter]
        rintro ⟨h, h2⟩
        rcases Finset.mem_insert.mp (hDG ▸ h) with h | h
        · refine h2 fun ρ hρ => (hDout ρ).mp ?_
          rw [h] at hρ
          exact hρ
        · exact (Finset.mem_erase.mp (hRG ▸ h)).1 rfl
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      obtain ⟨hi, hoff⟩ := hi
      rcases Finset.mem_insert.mp (hDG ▸ hi) with h | h
      · exfalso
        refine hoff fun ρ hρ => (hDout ρ).mp ?_
        rw [h] at hρ
        exact hρ
      · have hi' := Finset.mem_erase.mp (hRG ▸ h)
        refine ⟨hi'.2, fun hall => hoff fun ρ hρ => hall ρ ?_⟩
        refine hRle _ _ (vl_inr hi'.2) (fun e => hi'.1 (Sum.inr.inj e)) ?_
        exact (hDval _ _ (vl_inr h)).mp hρ

theorem normalize (hE : Gr E) (hC : Opt E X ∅ C) :
    ∃ C' : Ckt V, Opt E X ∅ C' ∧ Nmd E X C' ∧ nAnd C' = nAnd C := by
  have key : ∀ n, ∀ C : Ckt V, Opt E X ∅ C → nOff E X C ≤ n →
      ∃ C' : Ckt V, Opt E X ∅ C' ∧ Nmd E X C' ∧ nAnd C' = nAnd C := by
    intro n
    induction n with
    | zero =>
      intro C hC hn
      refine ⟨C, hC, ?_, rfl⟩
      intro y z hp g hg ho
      by_contra hf
      obtain ⟨C', _, _, _, h⟩ := norm_step hE hC.1 hp (by omega) hg ho
      omega
    | succ n ih =>
      intro C hC hn
      by_cases hN : Nmd E X C
      · exact ⟨C, hC, hN, rfl⟩
      · unfold Nmd at hN
        push Not at hN
        obtain ⟨y, z, hp, g, hg, ho, hf⟩ := hN
        obtain ⟨C', h1, h2, h3, h4⟩ := norm_step hE hC.1 hp (by omega) hg ho
        obtain ⟨C2, a, b, c⟩ := ih C' ⟨h1, fun D hD => h2.le.trans (hC.2 D hD)⟩ (by omega)
        exact ⟨C2, a, b, c.trans h3⟩
  exact key _ C hC le_rfl

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

theorem good_diff (hC : Good E X Y C) (P : Finset V) (h : HasEdge E (X \ ↑P)) :
    ∃ C' : Ckt V, Good E (X \ ↑P) Y C' := by
  obtain ⟨C', h', _⟩ := zero hC P (out_live hC.2.2.1 h)
  exact ⟨C', h'⟩

theorem kl_le (hC : Opt E X ∅ C) (P : Finset V) (h : HasEdge E (X \ ↑P)) :
    sz E (X \ ↑P) + kl C P ≤ sz E X := by
  obtain ⟨C', h1, h2, _⟩ := zero hC.1 P (out_live hC.1.2.2.1 h)
  have h3 := sz_le h1
  have h4 := count_part C P
  have h5 := opt_sz hC
  rw [h2] at h3
  omega

theorem sz_one (hE : Gr E) (hex : ∃ C : Ckt V, Good E X ∅ C) {v u : V} (hv : v ∈ X) (hu : u ∈ X)
    (h : E v u) (he : HasEdge E (X \ ({v} : Set V))) :
    sz E (X \ ({v} : Set V)) + 1 ≤ sz E X := by
  obtain ⟨C, hC⟩ := opt_exists hex
  have he' : HasEdge E (X \ ↑({v} : Finset V)) := by simpa using he
  have h1 := kl_le hC {v} he'
  have h2 := count_live (opt_useful hC) (P := {v})
    (fun p hp => by rw [Finset.mem_singleton.mp hp]; exact read_pos hE hC.1 hv hu h)
    (out_live hC.1.2.2.1 he')
  simp only [Finset.card_singleton, Finset.coe_singleton] at h1 h2
  unfold kl at h1
  omega

theorem sz_pair (hE : Gr E) (hex : ∃ C : Ckt V, Good E X ∅ C) {y z x : V} (hp : Pend E X y z)
    (hx : x ∈ X) (hxz : x ≠ z) (h : E y x) (he : HasEdge E (X \ ({y, z} : Set V))) :
    sz E (X \ ({y, z} : Set V)) + 3 ≤ sz E X := by
  obtain ⟨C0, hC0⟩ := opt_exists hex
  obtain ⟨C, hC, hN, _⟩ := normalize hE hC0
  have hW := hC.1.1
  have hcomp := hC.1.2.2.1
  have hyz : y ≠ z := by
    rintro rfl
    exact hE.2 _ hp.2.2.1
  have hxy : x ≠ y := by
    rintro rfl
    exact hE.2 _ h
  have he' : HasEdge E (X \ ↑({y, z} : Finset V)) := by simpa using he
  have h1 := kl_le hC {y, z} he'
  have hlive := out_live hcomp he'
  have hry := read_pos hE hC.1 hp.1 hp.2.1 hp.2.2.1
  have hrz := read_pos hE hC.1 hp.2.1 hp.1 (hE.1 _ _ hp.2.2.1)
  have h2 := count_live (opt_useful hC) (P := {y, z}) (by
    intro p hpm
    rcases Finset.mem_insert.mp hpm with rfl | hpm
    · exact hry
    · rw [Finset.mem_singleton.mp hpm]; exact hrz) hlive
  rw [Finset.card_pair hyz] at h2
  have hkey : 1 ≤ exc C {y, z} + (be C {y, z}).card := by
    by_cases hf : 2 ≤ fo C (Sum.inl y)
    · have hm : Sum.inl y ∈ (dw C {y, z}).erase C.out := by
        refine Finset.mem_erase.mpr ⟨?_, (mem_dw_inl _ _ _).mpr (by simp)⟩
        intro e
        refine fn_single (X := X) hE y ((hcomp {y}).mp ?_)
        rw [← e]; exact Set.mem_singleton y
      have := Finset.single_le_sum (f := fun w => fo C w - 1) (fun _ _ => Nat.zero_le _) hm
      change fo C (Sum.inl y) - 1 ≤ exc C {y, z} at this
      omega
    · have hf1 : fo C (Sum.inl y) ≤ 1 := by omega
      obtain ⟨g, hg⟩ := fo_pos.mp hry
      have hop : C.op g = true := by
        by_contra ho
        exact hf (hN y z hp g hg (by simpa using ho))
      obtain ⟨k, hk⟩ : ∃ k, (C.l g = Sum.inl y ∧ C.r g = k) ∨ (C.r g = Sum.inl y ∧ C.l g = k) := by
        rcases hg.2 with h | h
        · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
        · exact ⟨_, Or.inr ⟨h, rfl⟩⟩
      have hgk : Rd C g k := ⟨hg.1, by rcases hk with h | h <;> simp [h.2]⟩
      have hky : k ≠ Sum.inl y := by
        rintro rfl
        have : 2 ≤ fo C (Sum.inl y) := by
          rcases hk with h | h
          · exact fo_two_of_both hg.1 h.1 h.2
          · exact fo_two_of_both hg.1 h.2 h.1
        omega
      have hkl : ¬ Dd C {y, z} k := by
        intro hkd
        have hoff : ¬ C.val {y, x} k := by
          intro hv
          have : C.val {x} k := ignore hW (v := y) (n := g)
            (fun i hi => (rd_unique hf1 hg hi).le) (by
              intro u hu hm
              rcases hm with hm | hm
              · exact absurd hm hu
              · exact hm) k (rd_vl hW hgk).1 (rd_vl hW hgk).2 hky hv
          refine dd_off hW (rd_vl hW hgk).1 hkd (ρ := {x}) ?_ this
          intro p hpm hpx
          rw [Set.mem_singleton_iff] at hpx
          rw [hpx] at hpm
          simp [hxy, hxz] at hpm
        have hgoff : ¬ C.val {y, x} (Sum.inr g) := by
          rw [val_and hW hg.1 hop]
          rcases hk with h | h
          · rw [h.1, h.2]; exact fun a => hoff a.2
          · rw [h.1, h.2]; exact fun a => hoff a.1
        have hout : C.out ≠ Sum.inl y := by
          intro e
          refine fn_single (X := X) hE y ((hcomp {y}).mp ?_)
          rw [e]; exact Set.mem_singleton y
        have hon : C.val {y, x} C.out := (hcomp _).mpr ((fn_pair hE).mpr ⟨h, hp.1, hx⟩)
        refine fn_single (X := X) hE x ((hcomp {x}).mp ?_)
        refine escape hW {Sum.inl y} ?_ ?_ _ hW.2 hout hon
        · intro v hv hm
          rcases hm with hm | hm
          · exact absurd (congrArg Sum.inl hm) hv
          · exact hm
        · intro i hi _ hb hon
          rw [rd_unique hf1 ⟨hi, hb⟩ hg] at hon
          exact absurd hon hgoff
      have hbe : g ∈ be C {y, z} := by
        have hyd : Dd C {y, z} (Sum.inl y) := (dd_inl _ _ _).mpr (by simp)
        refine Finset.mem_filter.mpr ⟨hg.1, hop, ?_⟩
        rcases hk with h | h
        · rw [h.1, h.2]; tauto
        · rw [h.1, h.2]; tauto
      have := Finset.card_pos.mpr ⟨g, hbe⟩
      omega
  have h3 : (↑({y, z} : Finset V) : Set V) = {y, z} := by simp
  rw [h3] at h1
  unfold kl at h1
  omega

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

theorem other_operand {g : ℕ} {w : V ⊕ ℕ} (h : Rd C g w) :
    ∃ k, ((C.l g = w ∧ C.r g = k) ∨ (C.r g = w ∧ C.l g = k)) ∧ Rd C g k := by
  rcases h.2 with e | e
  · exact ⟨_, Or.inl ⟨e, rfl⟩, h.1, Or.inr rfl⟩
  · exact ⟨_, Or.inr ⟨e, rfl⟩, h.1, Or.inl rfl⟩

theorem other_ne {g : ℕ} {w k : V ⊕ ℕ} (hg : g ∈ C.G) (hf : fo C w ≤ 1)
    (hk : (C.l g = w ∧ C.r g = k) ∨ (C.r g = w ∧ C.l g = k)) : k ≠ w := by
  rintro rfl
  have : 2 ≤ fo C k := by
    rcases hk with h | h
    · exact fo_two_of_both hg h.1 h.2
    · exact fo_two_of_both hg h.2 h.1
  omega

theorem and_off (hW : Wf C) {y : V} {g : ℕ} {k : V ⊕ ℕ} (hf : fo C (Sum.inl y) ≤ 1)
    (hg : g ∈ C.G) (ho : C.op g = true)
    (hk : (C.l g = Sum.inl y ∧ C.r g = k) ∨ (C.r g = Sum.inl y ∧ C.l g = k))
    (hout : C.out ≠ Sum.inl y) {σ : Set V} (hoff : ¬ C.val σ k) :
    C.val (insert y σ) C.out → C.val σ C.out := by
  have hgy : Rd C g (Sum.inl y) := ⟨hg, by rcases hk with h | h <;> simp [h.1]⟩
  have hgk : Rd C g k := ⟨hg, by rcases hk with h | h <;> simp [h.2]⟩
  have hky := other_ne hg hf hk
  have hoff' : ¬ C.val (insert y σ) k := fun hv => hoff
    (ignore hW (v := y) (n := g) (fun i hi => (rd_unique hf hgy hi).le) (by
      intro u hu hm
      rcases hm with hm | hm
      · exact absurd hm hu
      · exact hm) k (rd_vl hW hgk).1 (rd_vl hW hgk).2 hky hv)
  refine escape hW {Sum.inl y} ?_ ?_ _ hW.2 hout
  · intro v hv hm
    rcases hm with hm | hm
    · exact absurd (congrArg Sum.inl hm) hv
    · exact hm
  · intro i hi _ hb hon
    rw [rd_unique hf ⟨hi, hb⟩ hgy, val_and hW hg ho] at hon
    rcases hk with h | h
    · exact absurd (h.2 ▸ hon.2) hoff'
    · exact absurd (h.2 ▸ hon.1) hoff'

theorem out_ne_var (hE : Gr E) (hC : Comp E X C) (v : V) : C.out ≠ Sum.inl v := by
  intro e
  refine fn_single (X := X) hE v ((hC {v}).mp ?_)
  rw [e]; exact Set.mem_singleton v

theorem exc_ge {P : Finset V} (A : Finset (V ⊕ ℕ)) (hA : A ⊆ (dw C P).erase C.out) :
    ∑ w ∈ A, (fo C w - 1) ≤ exc C P :=
  Finset.sum_le_sum_of_subset (f := fun w => fo C w - 1) hA

theorem y_unit (hE : Gr E) (hC : Good E X Y C) {P : Finset V} {y x : V} (hy : y ∈ X)
    (hx : x ∈ X) (h : E y x) (hyP : y ∈ P) (hxP : x ∉ P)
    (hN : ∀ g, Rd C g (Sum.inl y) → C.op g = false → 2 ≤ fo C (Sum.inl y)) :
    2 ≤ fo C (Sum.inl y) ∨ (fo C (Sum.inl y) = 1 ∧
      ∀ g, Rd C g (Sum.inl y) → g ∈ be C P ∧ C.op g = true) := by
  by_cases hf : 2 ≤ fo C (Sum.inl y)
  · exact Or.inl hf
  have hr := read_pos hE hC hy hx h
  refine Or.inr ⟨by omega, fun g hg => ?_⟩
  have ho : C.op g = true := by
    by_contra ho
    exact hf (hN g hg (by simpa using ho))
  obtain ⟨k, hk, hgk⟩ := other_operand hg
  have hW := hC.1
  have hkl : ¬ Dd C P k := by
    intro hkd
    have hoff : ¬ C.val {x} k := dd_off hW (rd_vl hW hgk).1 hkd (by
      rintro p hp rfl
      exact hxP hp)
    have := and_off hW (by omega) hg.1 ho hk (out_ne_var hE hC.2.2.1 y) hoff
      ((hC.2.2.1 _).mpr ((fn_pair hE).mpr ⟨h, hy, hx⟩))
    exact fn_single (X := X) hE x ((hC.2.2.1 _).mp this)
  refine ⟨Finset.mem_filter.mpr ⟨hg.1, ho, ?_⟩, ho⟩
  have hyd : Dd C P (Sum.inl y) := (dd_inl _ _ _).mpr hyP
  rcases hk with h | h
  · rw [h.1, h.2]; tauto
  · rw [h.1, h.2]; tauto

theorem loc_ne {z0 z1 z2 y1 y2 : V} (h : Loc E X C z0 z1 z2 y1 y2) :
    z0 ≠ z1 ∧ z0 ≠ z2 ∧ z0 ≠ y1 ∧ z0 ≠ y2 ∧ z1 ≠ z2 ∧ z1 ≠ y1 ∧ z1 ≠ y2 ∧ z2 ≠ y1 ∧ z2 ≠ y2 ∧
      y1 ≠ y2 := by
  have := h.2.2.2.1.2.2.2.2.2.2.1
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true] at this
  tauto

theorem loc_symm {z0 z1 z2 y1 y2 : V} (h : Loc E X C z0 z1 z2 y1 y2) : Loc E X C z0 z2 z1 y2 y1 := by
  have hne := loc_ne h
  obtain ⟨hE, hO, hN, ⟨hp1, hp2, hz0, e1, e2, hadj, hnd, hyy, x, hx, hxn, ex1, ex2⟩, hl, k1, k2,
    k3, k4⟩ := h
  have hs : ({z0, z2, z1, y2, y1} : Finset V) = {z0, z1, z2, y1, y2} := by
    ext v
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨hE, hO, hN, ⟨hp2, hp1, hz0, e2, e1, fun u hu hz => (hadj u hu hz).symm, ?_,
    fun e => hyy (hE.1 _ _ e), x, hx, ?_, ex2, ex1⟩, ?_, k1, ?_, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    refine ⟨⟨hne.2.1, hne.1, hne.2.2.2.1, hne.2.2.1⟩, ⟨hne.2.2.2.2.1.symm, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    all_goals first | tauto | (intro e; simp_all)
  · simp only [List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, and_true] at hxn ⊢
    tauto
  · rw [hs]; exact hl
  · rw [Finset.insert_comm]; exact k3
  · rw [Finset.insert_comm]; exact k2
  · rw [hs]; exact k4

theorem loc_z0 {z0 z1 z2 y1 y2 : V} (h : Loc E X C z0 z1 z2 y1 y2) :
    fo C (Sum.inl z0) = 1 ∧ ∀ g, Rd C g (Sum.inl z0) → C.op g = false := by
  obtain ⟨hE, hO, hN, ⟨hp1, hp2, hz0, e1, e2, hadj, hnd, hyy, x, hx, hxn, ex1, ex2⟩, hl, k1, k2,
    k3, k4⟩ := h
  have hW := hO.1.1
  have hU := opt_useful hO
  have hr := read_pos hE hO.1 hz0 hp1.1 e1
  have hlive : ¬ Dd C {z0} C.out := fun hd => hl (dd_mono hW (by simp) hW.2 hd)
  have hc := count_live hU (P := {z0}) (by
    intro p hp; rw [Finset.mem_singleton.mp hp]; exact hr) hlive
  rw [Finset.card_singleton] at hc
  unfold kl at k1
  have hex := exc_ge (C := C) (P := {z0}) {Sum.inl z0} (by
    intro w hw
    rw [Finset.mem_singleton] at hw
    rw [hw]
    exact Finset.mem_erase.mpr ⟨(out_ne_var hE hO.1.2.2.1 z0).symm,
      (mem_dw_inl _ _ _).mpr (by simp)⟩)
  rw [Finset.sum_singleton] at hex
  have hf : fo C (Sum.inl z0) = 1 := by omega
  refine ⟨hf, fun g hg => ?_⟩
  by_contra ho
  have ho : C.op g = true := by simpa using ho
  obtain ⟨k, hk, hgk⟩ := other_operand hg
  have hkne := other_ne hg.1 hf.le hk
  have hzd : Dd C {z0} (Sum.inl z0) := (dd_inl _ _ _).mpr (by simp)
  by_cases hkd : Dd C {z0} k
  · have := ignore hW (v := z0) (n := g) (ρ := Set.univ) (σ := {u | u ≠ z0})
      (fun i hi => (rd_unique hf.le hg hi).le) (fun u hu _ => hu) k (rd_vl hW hgk).1
      (rd_vl hW hgk).2 hkne (val_univ hW k (rd_vl hW hgk).1)
    refine dd_off hW (rd_vl hW hgk).1 hkd ?_ this
    intro p hp hm
    exact hm (Finset.mem_singleton.mp hp)
  · have hbe : g ∈ be C {z0} := by
      refine Finset.mem_filter.mpr ⟨hg.1, ho, ?_⟩
      rcases hk with h | h
      · rw [h.1, h.2]; tauto
      · rw [h.1, h.2]; tauto
    have := Finset.card_pos.mpr ⟨g, hbe⟩
    omega

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

theorem loc_budget2 {z0 z1 z2 y1 y2 : V} (h : Loc E X C z0 z1 z2 y1 y2) :
    exc C {z1, z2, y2} + (be C {z1, z2, y2}).card ≤ 1 ∧
    (2 ≤ fo C (Sum.inl y2) ∨ (fo C (Sum.inl y2) = 1 ∧
      ∀ g, Rd C g (Sum.inl y2) → g ∈ be C {z1, z2, y2} ∧ C.op g = true)) := by
  have hne := loc_ne h
  obtain ⟨hE, hO, hN, ⟨hp1, hp2, hz0, e1, e2, hadj, hnd, hyy, x, hx, hxn, ex1, ex2⟩, hl, k1, k2,
    k3, k4⟩ := h
  have hW := hO.1.1
  have hlive : ¬ Dd C {z1, z2, y2} C.out := fun hd => hl (dd_mono hW (by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    tauto) hW.2 hd)
  have hP : (({z1, z2, y2} : Finset V)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_pair hne.2.2.2.2.2.2.2.2.1]
  have hc := count_live (opt_useful hO) (P := {z1, z2, y2}) (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact read_pos hE hO.1 hp1.2.1 hp1.1 (hE.1 _ _ hp1.2.2.1)
    · exact read_pos hE hO.1 hp2.2.1 hp2.1 (hE.1 _ _ hp2.2.2.1)
    · exact read_pos hE hO.1 hp2.1 hp2.2.1 hp2.2.2.1) hlive
  unfold kl at k2
  refine ⟨by omega, y_unit hE hO.1 hp2.1 hx ex2 (by simp) ?_ (hN y2 z2 hp2)⟩
  simp only [List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, and_true] at hxn
  simp [hxn]

theorem loc_be2 {z0 z1 z2 y1 y2 : V} (h : Loc E X C z0 z1 z2 y1 y2) :
    ∀ g ∈ be C {z1, z2, y2}, fo C (Sum.inl y2) = 1 ∧ Rd C g (Sum.inl y2) := by
  intro g hg
  obtain ⟨hb, hu⟩ := loc_budget2 h
  have hpos := Finset.card_pos.mpr ⟨g, hg⟩
  obtain ⟨hE, hO, hN, ⟨hp1, hp2, -⟩, -⟩ := h
  rcases hu with hu | ⟨hu, hr⟩
  · have hex := exc_ge (C := C) (P := {z1, z2, y2}) {Sum.inl y2} (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      rw [hw]
      exact Finset.mem_erase.mpr ⟨(out_ne_var hE hO.1.2.2.1 y2).symm,
        (mem_dw_inl _ _ _).mpr (by simp)⟩)
    rw [Finset.sum_singleton] at hex
    omega
  · obtain ⟨k, hk⟩ := fo_pos.mp hu.ge
    have : g = k := Finset.card_le_one.mp (by omega) g hg k (hr k hk).1
    rw [this]; exact ⟨hu, hk⟩

theorem loc_z1 {z0 z1 z2 y1 y2 : V} (h : Loc E X C z0 z1 z2 y1 y2) :
    fo C (Sum.inl z1) = 1 ∧ ∀ g, Rd C g (Sum.inl z1) → C.op g = false := by
  have hne := loc_ne h
  have hbe := loc_be2 h
  obtain ⟨hb, hu⟩ := loc_budget2 h
  obtain ⟨hE, hO, hN, ⟨hp1, hp2, -⟩, -⟩ := h
  have hW := hO.1.1
  have hcomp := hO.1.2.2.1
  have hr := read_pos hE hO.1 hp1.2.1 hp1.1 (hE.1 _ _ hp1.2.2.1)
  have hex := exc_ge (C := C) (P := {z1, z2, y2}) {Sum.inl z1, Sum.inl y2} (by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨(out_ne_var hE hcomp _).symm, (mem_dw_inl _ _ _).mpr (by simp)⟩
    · exact Finset.mem_erase.mpr ⟨(out_ne_var hE hcomp _).symm, (mem_dw_inl _ _ _).mpr (by simp)⟩)
  rw [Finset.sum_pair (fun e => hne.2.2.2.2.2.2.1 (Sum.inl.inj e))] at hex
  have hf : fo C (Sum.inl z1) = 1 := by
    rcases hu with hu | ⟨hu, hr2⟩
    · omega
    · obtain ⟨k, hk⟩ := fo_pos.mp hu.ge
      have := Finset.card_pos.mpr ⟨k, (hr2 k hk).1⟩
      omega
  refine ⟨hf, fun g hg => ?_⟩
  by_contra ho
  have ho : C.op g = true := by simpa using ho
  obtain ⟨k, hk, hgk⟩ := other_operand hg
  have hzd : Dd C {z1, z2, y2} (Sum.inl z1) := (dd_inl _ _ _).mpr (by simp)
  by_cases hkd : Dd C {z1, z2, y2} k
  · have hoff : ¬ C.val {y1} k := dd_off hW (rd_vl hW hgk).1 hkd (by
      intro p hp hm
      rw [Set.mem_singleton_iff] at hm
      rw [hm] at hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with e | e | e
      · exact hne.2.2.2.2.2.1 e.symm
      · exact hne.2.2.2.2.2.2.2.1 e.symm
      · exact hne.2.2.2.2.2.2.2.2.2 e)
    have := and_off hW hf.le hg.1 ho hk (out_ne_var hE hcomp z1) hoff
      ((hcomp _).mpr ((fn_pair hE).mpr ⟨hE.1 _ _ hp1.2.2.1, hp1.2.1, hp1.1⟩))
    exact fn_single (X := X) hE y1 ((hcomp _).mp this)
  · have hgb : g ∈ be C {z1, z2, y2} := by
      refine Finset.mem_filter.mpr ⟨hg.1, ho, ?_⟩
      rcases hk with h | h
      · rw [h.1, h.2]; tauto
      · rw [h.1, h.2]; tauto
    have hy := (hbe g hgb).2.2
    have hk2 : k = Sum.inl y2 := by
      have hz : (Sum.inl z1 : V ⊕ ℕ) ≠ Sum.inl y2 := fun e => hne.2.2.2.2.2.2.1 (Sum.inl.inj e)
      rcases hk with h | h <;> rcases hy with h' | h'
      · exact absurd (h.1.symm.trans h') hz
      · exact h.2.symm.trans h'
      · exact h.2.symm.trans h'
      · exact absurd (h.1.symm.trans h') hz
    exact hkd (hk2 ▸ (dd_inl _ _ _).mpr (by simp))

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

theorem loc_c {z0 z1 z2 y1 y2 : V} (h : Loc E X C z0 z1 z2 y1 y2) :
    exc C {z0, z1, z2, y1, y2} + (be C {z0, z1, z2, y1, y2}).card = 2 ∧
    (fo C (Sum.inl y1) = 1 ∨ fo C (Sum.inl y1) = 2) ∧
    (fo C (Sum.inl y2) = 1 ∨ fo C (Sum.inl y2) = 2) ∧
    (be C {z0, z1, z2, y1, y2}).card =
      (if fo C (Sum.inl y1) = 1 then 1 else 0) + (if fo C (Sum.inl y2) = 1 then 1 else 0) ∧
    (∀ w ∈ dw C {z0, z1, z2, y1, y2}, w ≠ Sum.inl y1 → w ≠ Sum.inl y2 → fo C w = 1) ∧
    (∀ g ∈ be C {z0, z1, z2, y1, y2},
      (fo C (Sum.inl y1) = 1 ∧ Rd C g (Sum.inl y1)) ∨
      (fo C (Sum.inl y2) = 1 ∧ Rd C g (Sum.inl y2))) ∧
    (∀ g, fo C (Sum.inl y1) = 1 → Rd C g (Sum.inl y1) → g ∈ be C {z0, z1, z2, y1, y2}) ∧
    (∀ g, fo C (Sum.inl y2) = 1 → Rd C g (Sum.inl y2) → g ∈ be C {z0, z1, z2, y1, y2}) := by
  have hne := loc_ne h
  obtain ⟨hE, hO, hN, ⟨hp1, hp2, hz0, e1, e2, hadj, hnd, hyy, x, hx, hxn, ex1, ex2⟩, hl, k1, k2,
    k3, k4⟩ := h
  have hW := hO.1.1
  have hU := opt_useful hO
  have hcomp := hO.1.2.2.1
  have r0 := read_pos hE hO.1 hz0 hp1.1 e1
  have r1 := read_pos hE hO.1 hp1.2.1 hp1.1 (hE.1 _ _ hp1.2.2.1)
  have r2 := read_pos hE hO.1 hp2.2.1 hp2.1 (hE.1 _ _ hp2.2.2.1)
  have r3 := read_pos hE hO.1 hp1.1 hp1.2.1 hp1.2.2.1
  have r4 := read_pos hE hO.1 hp2.1 hp2.2.1 hp2.2.2.1
  simp only [List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, and_true] at hxn
  set P : Finset V := {z0, z1, z2, y1, y2} with hPdef
  have hP5 : P.card = 5 := by
    have : P = [z0, z1, z2, y1, y2].toFinset := by simp [hPdef]
    rw [this, List.toFinset_card_of_nodup hnd]; rfl
  have hPr : ∀ p ∈ P, 1 ≤ fo C (Sum.inl p) := by
    intro p hp
    simp only [hPdef, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hc := count_live hU hPr hl
  unfold kl at k4
  have hy1P : y1 ∈ P := by simp [hPdef]
  have hy2P : y2 ∈ P := by simp [hPdef]
  have hxP : x ∉ P := by simp [hPdef, hxn]
  have u1 := y_unit hE hO.1 hp1.1 hx ex1 hy1P hxP (hN y1 z1 hp1)
  have u2 := y_unit hE hO.1 hp2.1 hx ex2 hy2P hxP (hN y2 z2 hp2)
  have d1 : Dd C P (Sum.inl y1) := (dd_inl _ _ _).mpr hy1P
  have d2 : Dd C P (Sum.inl y2) := (dd_inl _ _ _).mpr hy2P
  have hyne : (Sum.inl y1 : V ⊕ ℕ) ≠ Sum.inl y2 := fun e => hne.2.2.2.2.2.2.2.2.2 (Sum.inl.inj e)
  have m1 : (Sum.inl y1 : V ⊕ ℕ) ∈ (dw C P).erase C.out :=
    Finset.mem_erase.mpr ⟨(out_ne_var hE hcomp _).symm, (mem_dw_inl _ _ _).mpr hy1P⟩
  have m2 : (Sum.inl y2 : V ⊕ ℕ) ∈ (dw C P).erase C.out :=
    Finset.mem_erase.mpr ⟨(out_ne_var hE hcomp _).symm, (mem_dw_inl _ _ _).mpr hy2P⟩
  have hex2 := exc_ge (C := C) (P := P) {Sum.inl y1, Sum.inl y2} (by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> assumption)
  rw [Finset.sum_pair hyne] at hex2
  have hboth : ∀ g, Rd C g (Sum.inl y1) → Rd C g (Sum.inl y2) → g ∉ be C P := by
    intro g h1 h2 hb
    have := (Finset.mem_filter.mp hb).2.2
    rcases h1.2 with a | a <;> rcases h2.2 with b | b
    · exact hyne (a.symm.trans b)
    · rw [a, b] at this; tauto
    · rw [a, b] at this; tauto
    · exact hyne (a.symm.trans b)
  have hexw : ∀ w ∈ dw C P, w ≠ Sum.inl y1 → w ≠ Sum.inl y2 →
      (fo C w - 1) + ((fo C (Sum.inl y1) - 1) + (fo C (Sum.inl y2) - 1)) ≤ exc C P ∧
        1 ≤ fo C w := by
    intro w hw h1 h2
    have hwo : w ≠ C.out := by
      rintro rfl
      exact hl (mem_dw.mp hw).2
    constructor
    · have := exc_ge (C := C) (P := P) {w, Sum.inl y1, Sum.inl y2} (by
        intro w' hw'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
        rcases hw' with rfl | rfl | rfl
        · exact Finset.mem_erase.mpr ⟨hwo, hw⟩
        · assumption
        · assumption)
      rwa [Finset.sum_insert (by simp [h1, h2]), Finset.sum_pair hyne] at this
    · rcases w with v | g
      · exact hPr v ((mem_dw_inl _ _ _).mp hw)
      · exact hU.2.2 g ((mem_dw_inr _ _ _).mp hw).1 hwo
  rcases u1 with u1 | ⟨u1, w1⟩ <;> rcases u2 with u2 | ⟨u2, w2⟩
  · have hb0 : (be C P).card = 0 := by omega
    have hbe : be C P = ∅ := Finset.card_eq_zero.mp hb0
    refine ⟨by omega, Or.inr (by omega), Or.inr (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_neg (by omega), if_neg (by omega)]; omega
    · intro w hw h1 h2
      have := hexw w hw h1 h2
      omega
    · rw [hbe]; simp
    · intro g h; omega
    · intro g h; omega
  · obtain ⟨g2, hg2⟩ := fo_pos.mp u2.ge
    have hg2b := (w2 g2 hg2).1
    have hpos := Finset.card_pos.mpr ⟨g2, hg2b⟩
    refine ⟨by omega, Or.inr (by omega), Or.inl (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_neg (by omega), if_pos (by omega)]; omega
    · intro w hw h1 h2
      have := hexw w hw h1 h2
      omega
    · intro g hg
      have : g = g2 := Finset.card_le_one.mp (by omega) g hg g2 hg2b
      exact Or.inr ⟨u2, this ▸ hg2⟩
    · intro g h; omega
    · intro g _ hg; exact (w2 g hg).1
  · obtain ⟨g1, hg1⟩ := fo_pos.mp u1.ge
    have hg1b := (w1 g1 hg1).1
    have hpos := Finset.card_pos.mpr ⟨g1, hg1b⟩
    refine ⟨by omega, Or.inl (by omega), Or.inr (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_pos (by omega), if_neg (by omega)]; omega
    · intro w hw h1 h2
      have := hexw w hw h1 h2
      omega
    · intro g hg
      have : g = g1 := Finset.card_le_one.mp (by omega) g hg g1 hg1b
      exact Or.inl ⟨u1, this ▸ hg1⟩
    · intro g _ hg; exact (w1 g hg).1
    · intro g h; omega
  · obtain ⟨g1, hg1⟩ := fo_pos.mp u1.ge
    obtain ⟨g2, hg2⟩ := fo_pos.mp u2.ge
    have hg1b := (w1 g1 hg1).1
    have hg2b := (w2 g2 hg2).1
    have hgne : g1 ≠ g2 := by
      rintro rfl
      exact hboth g1 hg1 hg2 hg1b
    have hsub : ({g1, g2} : Finset ℕ) ⊆ be C P := by
      intro g hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl <;> assumption
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hgne] at hcard
    have heq : ({g1, g2} : Finset ℕ) = be C P :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hgne]; omega)
    refine ⟨by omega, Or.inl (by omega), Or.inl (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_pos (by omega), if_pos (by omega)]; omega
    · intro w hw h1 h2
      have := hexw w hw h1 h2
      omega
    · intro g hg
      rw [← heq] at hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact Or.inl ⟨u1, hg1⟩
      · exact Or.inr ⟨u2, hg2⟩
    · intro g _ hg; exact (w1 g hg).1
    · intro g _ hg; exact (w2 g hg).1

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

theorem cone_dead (hW : Wf C) {P : Finset V} {u a : V ⊕ ℕ} (h : Cn C P u a) (ha : Vl C a)
    (hd : Dd C P a) : Vl C u ∧ Dd C P u ∧ rk u ≤ rk a := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨ha, hd, le_rfl⟩
  | head hs _ ih =>
    obtain ⟨g, hg, rfl, ho, hr⟩ := hs
    obtain ⟨hgG, hl1, hl2⟩ := Finset.mem_filter.mp hg
    have hb := rd_vl hW (⟨hgG, hr⟩ : Rd C g _)
    refine ⟨hb.1, ?_, hb.2.trans (le_trans (by simp [rk]) ih.2.2)⟩
    rcases hr with e | e
    · exact e ▸ hl1
    · exact e ▸ hl2

theorem cone_val (hW : Wf C) {P : Finset V} {a : V ⊕ ℕ} (ha : Vl C a) (hd : Dd C P a)
    (hlow : ∀ g ∈ al C P, C.op g = true → rk a < rk (Sum.inr g : V ⊕ ℕ)) (ρ : Set V) :
    C.val ρ a ↔ ∃ u, Cn C P u a ∧ ((∃ v ∈ P, u = Sum.inl v) ∨ ∃ g ∈ be C P, u = Sum.inr g) ∧
      C.val ρ u := by
  constructor
  · revert hd hlow
    refine wire_ind' hW (p := fun a => Dd C P a → (∀ g ∈ al C P, C.op g = true →
      rk a < rk (Sum.inr g : V ⊕ ℕ)) → C.val ρ a → ∃ u, Cn C P u a ∧
      ((∃ v ∈ P, u = Sum.inl v) ∨ ∃ g ∈ be C P, u = Sum.inr g) ∧ C.val ρ u) ?_ ?_ a ha
    · intro v hd _ hv
      exact ⟨_, Relation.ReflTransGen.refl, Or.inl ⟨v, (dd_inl _ _ _).mp hd, rfl⟩, hv⟩
    · intro g hg hl hr hd hlow hv
      rcases (kinds_dead hW P hg).mp hd with hk | hk
      · have ho : C.op g = false := by
          by_contra ho
          exact lt_irrefl _ (hlow g hk (by simpa using ho))
        obtain ⟨_, dl, dr⟩ := Finset.mem_filter.mp hk
        have hlt : ∀ u : V ⊕ ℕ, rk u ≤ g → ∀ k ∈ al C P, C.op k = true →
            rk u < rk (Sum.inr k : V ⊕ ℕ) := by
          intro u hu k hk hok
          refine lt_of_le_of_lt (hu.trans ?_) (hlow k hk hok)
          simp [rk]
        rw [val_or hW hg ho] at hv
        rcases hv with hv | hv
        · obtain ⟨u, h1, h2, h3⟩ := hl dl (hlt _ (hW.1 g hg).1.2) hv
          exact ⟨u, h1.tail ⟨g, hk, rfl, ho, Or.inl rfl⟩, h2, h3⟩
        · obtain ⟨u, h1, h2, h3⟩ := hr dr (hlt _ (hW.1 g hg).2.2) hv
          exact ⟨u, h1.tail ⟨g, hk, rfl, ho, Or.inr rfl⟩, h2, h3⟩
      · exact ⟨_, Relation.ReflTransGen.refl, Or.inr ⟨g, hk, rfl⟩, hv⟩
  · rintro ⟨u, hu, -, hv⟩
    induction hu using Relation.ReflTransGen.head_induction_on with
    | refl => exact hv
    | head hs _ ih =>
      obtain ⟨g, hg, rfl, ho, hr⟩ := hs
      refine ih ?_
      rw [val_or hW (Finset.mem_filter.mp hg).1 ho]
      rcases hr with e | e
      · exact Or.inl (e ▸ hv)
      · exact Or.inr (e ▸ hv)

theorem cone_head {P : Finset V} {u a : V ⊕ ℕ} (h : Cn C P u a) (hne : u ≠ a) :
    ∃ g, Rd C g u ∧ Cn C P (Sum.inr g) a := by
  rcases Relation.ReflTransGen.cases_head h with e | ⟨c, hs, hc⟩
  · exact absurd e hne
  · obtain ⟨g, hg, rfl, ho, hr⟩ := hs
    exact ⟨g, ⟨(Finset.mem_filter.mp hg).1, hr⟩, hc⟩

theorem cone_escape (hW : Wf C) {P : Finset V} {a : V ⊕ ℕ} (ha : Vl C a) (hd : Dd C P a)
    (h1 : ∀ g, Cn C P (Sum.inr g) a → Sum.inr g ≠ a → fo C (Sum.inr g) ≤ 1) {ρ σ : Set V}
    (hval : C.val ρ a → C.val σ a)
    (hv : ∀ v, v ∈ ρ → v ∉ σ → Cn C P (Sum.inl v) a ∧ fo C (Sum.inl v) ≤ 1) :
    ∀ w, Vl C w → ¬ (Cn C P w a ∧ w ≠ a) → C.val ρ w → C.val σ w := by
  refine wire_ind' hW (p := fun w => ¬ (Cn C P w a ∧ w ≠ a) → C.val ρ w → C.val σ w) ?_ ?_
  · intro v hn hm
    by_contra hs
    have h := hv v hm hs
    by_cases he : Sum.inl v = a
    · rw [← he] at hval
      exact hs (hval hm)
    · exact hn ⟨h.1, he⟩
  · intro g hg hl hr hn hval'
    by_cases he : Sum.inr g = a
    · rw [he] at hval' ⊢
      exact hval hval'
    have hng : ¬ Cn C P (Sum.inr g) a := fun h => hn ⟨h, he⟩
    have key : ∀ u, Rd C g u → (¬ (Cn C P u a ∧ u ≠ a) → C.val ρ u → C.val σ u) →
        C.val ρ u → C.val σ u := by
      intro u hu ih hvu
      by_cases hc : Cn C P u a ∧ u ≠ a
      · obtain ⟨k, hk, hck⟩ := cone_head hc.1 hc.2
        rcases u with v | j
        · by_contra hs
          have := rd_unique (hv v hvu hs).2 hk hu
          exact hng (this ▸ hck)
        · have := rd_unique (h1 j hc.1 hc.2) hk hu
          exact absurd (this ▸ hck) hng
      · exact ih hc hvu
    have hl' := key _ ⟨hg, Or.inl rfl⟩ hl
    have hr' := key _ ⟨hg, Or.inr rfl⟩ hr
    rw [val_gate hW hg] at hval' ⊢
    split_ifs at hval' ⊢
    · exact ⟨hl' hval'.1, hr' hval'.2⟩
    · exact hval'.imp hl' hr'

theorem cone_disjoint (hW : Wf C) {P : Finset V} {a b u : V ⊕ ℕ} {h : ℕ} (hg : h ∈ C.G)
    (hl : C.l h = a) (hr : C.r h = b) (hab : a ≠ b) (hda : Dd C P a) (hdb : Dd C P b)
    (h1 : ∀ g, (Cn C P (Sum.inr g) a ∨ Cn C P (Sum.inr g) b) → fo C (Sum.inr g) ≤ 1)
    (ha : Cn C P u a) (hb : Cn C P u b) (hu : fo C u ≤ 1) : False := by
  have hna : ¬ Cn C P (Sum.inr h) a := by
    intro hc
    have := (cone_dead hW hc (hl ▸ (hW.1 h hg).1.1) hda).2.2
    have h2 := (hW.1 h hg).1.2
    rw [hl] at h2
    simp only [rk, Sum.elim_inr] at this h2
    omega
  have hnb : ¬ Cn C P (Sum.inr h) b := by
    intro hc
    have := (cone_dead hW hc (hr ▸ (hW.1 h hg).2.1) hdb).2.2
    have h2 := (hW.1 h hg).2.2
    rw [hr] at h2
    simp only [rk, Sum.elim_inr] at this h2
    omega
  induction ha using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨k, hk, hck⟩ := cone_head hb hab
    have := rd_unique hu hk ⟨hg, Or.inl hl⟩
    exact hnb (this ▸ hck)
  | @head u c hs hca ih =>
    obtain ⟨g, hgal, rfl, ho, hrd⟩ := hs
    have hgu : Rd C g u := ⟨(Finset.mem_filter.mp hgal).1, hrd⟩
    by_cases hub : u = b
    · have := rd_unique hu hgu ⟨hg, Or.inr (hr.trans hub.symm)⟩
      exact hna (this ▸ hca)
    · obtain ⟨k, hk, hck⟩ := cone_head hb hub
      have := rd_unique hu hgu hk
      exact ih (this ▸ hck) (h1 g (Or.inl hca))

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

def Ctx (E : V → V → Prop) (X : Set V) (C : Ckt V) (z0 z1 z2 y1 y2 : V) (P : Finset V) (i : ℕ)
    (a b : V ⊕ ℕ) : Prop :=
  Loc E X C z0 z1 z2 y1 y2 ∧ P = {z0, z1, z2, y1, y2} ∧ i ∈ al C P ∧ C.op i = true ∧
  (∀ g ∈ al C P, C.op g = true → i ≤ g) ∧
  ((C.l i = a ∧ C.r i = b) ∨ (C.r i = a ∧ C.l i = b))

variable {z0 z1 z2 y1 y2 : V} {P : Finset V} {i : ℕ} {a b : V ⊕ ℕ}

theorem ctx_ab (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) : Ctx E X C z0 z1 z2 y1 y2 P i b a :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, 
    h.2.2.2.2.2.elim (fun e => Or.inr ⟨e.2, e.1⟩) (fun e => Or.inl ⟨e.2, e.1⟩)⟩

theorem ctx_symm (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) : Ctx E X C z0 z2 z1 y2 y1 P i a b := by
  refine ⟨loc_symm h.1, ?_, h.2.2⟩
  rw [h.2.1]
  ext v
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem ctx_a (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) :
    Rd C i a ∧ Vl C a ∧ Dd C P a ∧ rk a ≤ i := by
  obtain ⟨hL, -, hi, -, -, hk⟩ := h
  have hW := hL.2.1.1.1
  obtain ⟨hiG, d1, d2⟩ := Finset.mem_filter.mp hi
  have hr : Rd C i a := ⟨hiG, by rcases hk with e | e <;> simp [e.1]⟩
  refine ⟨hr, (rd_vl hW hr).1, ?_, (rd_vl hW hr).2⟩
  rcases hk with e | e
  · exact e.1 ▸ d1
  · exact e.1 ▸ d2

theorem ctx_val (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) (ρ : Set V) :
    C.val ρ (Sum.inr i) ↔ C.val ρ a ∧ C.val ρ b := by
  have hW := h.1.2.1.1.1
  rw [val_and hW (Finset.mem_filter.mp h.2.2.1).1 h.2.2.2.1]
  rcases h.2.2.2.2.2 with e | e
  · rw [e.1, e.2]
  · rw [e.1, e.2, and_comm]

theorem ctx_not_le (h : Ctx E X C z0 z1 z2 y1 y2 P i a b)
    (hle : ∀ ρ, C.val ρ a → C.val ρ b) : False := by
  have ha := ctx_a h
  refine opt_no_dup h.1.2.1 (Finset.mem_filter.mp h.2.2.1).1 ha.2.1 ha.2.2.2 fun ρ => ?_
  rw [ctx_val h]
  exact ⟨fun x => x.1, fun x => ⟨x, hle ρ x⟩⟩

theorem ctx_single (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) {u : V}
    (hu : ∀ g, Rd C g (Sum.inl u) → C.op g = false) (hv : ∀ ρ, C.val ρ a ↔ u ∈ ρ) : False := by
  have ha := ctx_a h
  rcases hae : a with v | g
  · have : v = u := by
      have := (hv {v}).mp (by rw [hae]; exact Set.mem_singleton v)
      exact (Set.mem_singleton_iff.mp this).symm
    have h2 := hu i (by rw [← this, ← hae]; exact ha.1)
    rw [h.2.2.2.1] at h2
    cases h2
  · rw [hae] at hv ha
    exact opt_no_dup h.1.2.1 (w := Sum.inl u) (ha.2.1 g rfl) (vl_inl C u) (by simp [rk])
      fun ρ => hv ρ

theorem ctx_fo (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) {w : V ⊕ ℕ} (hc : Cn C P w a)
    (h1 : w ≠ Sum.inl y1) (h2 : w ≠ Sum.inl y2) : fo C w = 1 := by
  have ha := ctx_a h
  have hW := h.1.2.1.1.1
  have hd := cone_dead hW hc ha.2.1 ha.2.2.1
  have hc := loc_c h.1
  rw [← h.2.1] at hc
  exact hc.2.2.2.2.1 w (mem_dw.mpr ⟨hd.1, hd.2.1⟩) h1 h2

theorem ctx_disj (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) {u : V ⊕ ℕ} (ha : Cn C P u a)
    (hb : Cn C P u b) (h1 : u ≠ Sum.inl y1) (h2 : u ≠ Sum.inl y2) : False := by
  have hW := h.1.2.1.1.1
  have hab : a ≠ b := by
    rintro rfl
    exact ctx_not_le h fun ρ x => x
  have hu := ctx_fo h ha h1 h2
  have hA := ctx_a h
  have hB := ctx_a (ctx_ab h)
  have hga : ∀ g, Cn C P (Sum.inr g) a → fo C (Sum.inr g) ≤ 1 := fun g hg =>
    (ctx_fo h hg (by simp) (by simp)).le
  have hgb : ∀ g, Cn C P (Sum.inr g) b → fo C (Sum.inr g) ≤ 1 := fun g hg =>
    (ctx_fo (ctx_ab h) hg (by simp) (by simp)).le
  rcases h.2.2.2.2.2 with e | e
  · exact cone_disjoint hW hA.1.1 e.1 e.2 hab hA.2.2.1 hB.2.2.1
      (fun g hg => hg.elim (hga g) (hgb g)) ha hb hu.le
  · exact cone_disjoint hW hA.1.1 e.2 e.1 hab.symm hB.2.2.1 hA.2.2.1
      (fun g hg => hg.elim (hgb g) (hga g)) hb ha hu.le

theorem ctx_cross (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) {u t s : V} (hu : Cn C P (Sum.inl u) a)
    (ht : Cn C P (Sum.inl t) a) (h1 : u ≠ y1) (h2 : u ≠ y2) (hf : Fn E X {u, s})
    (hn : ¬ Fn E X {t, s}) : False := by
  have hW := h.1.2.1.1.1
  have hcomp := h.1.2.1.1.2.2.1
  have ha := ctx_a h
  have hfu := ctx_fo h hu (fun e => h1 (Sum.inl.inj e)) (fun e => h2 (Sum.inl.inj e))
  have hta : C.val {t, s} a := by
    have : ∀ w, Cn C P w a → C.val {t, s} w → C.val {t, s} a := by
      intro w hw hv
      induction hw using Relation.ReflTransGen.head_induction_on with
      | refl => exact hv
      | head hs _ ih =>
        obtain ⟨g, hg, rfl, ho, hr⟩ := hs
        refine ih ?_
        rw [val_or hW (Finset.mem_filter.mp hg).1 ho]
        rcases hr with e | e
        · exact Or.inl (e ▸ hv)
        · exact Or.inr (e ▸ hv)
    exact this _ ht (Or.inl rfl)
  refine hn ((hcomp _).mp (cone_escape hW ha.2.1 ha.2.2.1 (ρ := {u, s})
    (fun g hg _ => (ctx_fo h hg (by simp) (by simp)).le) (fun _ => hta) ?_ _ hW.2 ?_
    ((hcomp _).mpr hf)))
  · intro v hv hv'
    rcases hv with rfl | hv
    · exact ⟨hu, hfu.le⟩
    · exact absurd (Or.inr hv) hv'
  · rintro ⟨hc, _⟩
    have := (cone_dead hW hc ha.2.1 ha.2.2.1).2.1
    rw [h.2.1] at this
    exact h.1.2.2.2.2.1 this

theorem ctx_notbe (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) {g : ℕ} (hg : g ∈ al C P) :
    g ∉ be C P := by
  intro hb
  have h1 := (Finset.mem_filter.mp hg).2
  have h2 := (Finset.mem_filter.mp hb).2.2
  tauto

theorem ctx_y1 (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) (hf : fo C (Sum.inl y1) = 1) :
    ¬ Cn C P (Sum.inl y1) a := by
  intro hc
  have hlc := loc_c h.1
  rw [← h.2.1] at hlc
  have hbe := hlc.2.2.2.2.2.2.1
  rcases Relation.ReflTransGen.cases_head hc with e | ⟨c, ⟨g, hg, -, -, hr⟩, -⟩
  · exact ctx_notbe h h.2.2.1 (hbe i hf (e ▸ (ctx_a h).1))
  · exact ctx_notbe h hg (hbe g hf ⟨(Finset.mem_filter.mp hg).1, hr⟩)

theorem ctx_be (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) {g : ℕ} (hg : g ∈ be C P) :
    C.op g = true ∧ ((fo C (Sum.inl y1) = 1 ∧ Rd C g (Sum.inl y1) ∧ ¬ Rd C g (Sum.inl y2)) ∨
      (fo C (Sum.inl y2) = 1 ∧ Rd C g (Sum.inl y2) ∧ ¬ Rd C g (Sum.inl y1))) := by
  have hlc := loc_c h.1
  rw [← h.2.1] at hlc
  have hne := (loc_ne h.1).2.2.2.2.2.2.2.2.2
  have hg' := Finset.mem_filter.mp hg
  have d1 : Dd C P (Sum.inl y1) := (dd_inl _ _ _).mpr (by rw [h.2.1]; simp)
  have d2 : Dd C P (Sum.inl y2) := (dd_inl _ _ _).mpr (by rw [h.2.1]; simp)
  have hboth : ¬ (Rd C g (Sum.inl y1) ∧ Rd C g (Sum.inl y2)) := by
    rintro ⟨h1, h2⟩
    have := hg'.2.2
    rcases h1.2 with e | e <;> rcases h2.2 with e' | e'
    · exact hne (Sum.inl.inj (e.symm.trans e'))
    · rw [e, e'] at this; tauto
    · rw [e, e'] at this; tauto
    · exact hne (Sum.inl.inj (e.symm.trans e'))
  refine ⟨hg'.2.1, ?_⟩
  rcases hlc.2.2.2.2.2.1 g hg with ⟨f, hr⟩ | ⟨f, hr⟩
  · exact Or.inl ⟨f, hr, fun hr' => hboth ⟨hr, hr'⟩⟩
  · exact Or.inr ⟨f, hr, fun hr' => hboth ⟨hr', hr⟩⟩

theorem ctx_be_val (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) {g : ℕ} (hg : g ∈ be C P) {v : V}
    (hr : Rd C g (Sum.inl v)) {ρ : Set V} (hv : C.val ρ (Sum.inr g)) : v ∈ ρ := by
  have hW := h.1.2.1.1.1
  rw [val_and hW hr.1 (ctx_be h hg).1] at hv
  rcases hr.2 with e | e
  · have := hv.1; rw [e] at this; exact this
  · have := hv.2; rw [e] at this; exact this

theorem ctx_src (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) (ρ : Set V) :
    C.val ρ a ↔ (Cn C P (Sum.inl z0) a ∧ z0 ∈ ρ) ∨ (Cn C P (Sum.inl z1) a ∧ z1 ∈ ρ) ∨
      (Cn C P (Sum.inl z2) a ∧ z2 ∈ ρ) ∨ (Cn C P (Sum.inl y1) a ∧ y1 ∈ ρ) ∨
      (Cn C P (Sum.inl y2) a ∧ y2 ∈ ρ) ∨
      ∃ g ∈ be C P, Cn C P (Sum.inr g) a ∧ C.val ρ (Sum.inr g) := by
  have hW := h.1.2.1.1.1
  have ha := ctx_a h
  rw [cone_val hW ha.2.1 ha.2.2.1 (fun g hg ho => by
    have := h.2.2.2.2.1 g hg ho
    simp only [rk, Sum.elim_inr]
    exact Nat.lt_succ_of_le (ha.2.2.2.trans this)) ρ]
  have hP : ∀ v, v ∈ P ↔ v = z0 ∨ v = z1 ∨ v = z2 ∨ v = y1 ∨ v = y2 := by
    intro v; rw [h.2.1]; simp
  constructor
  · rintro ⟨u, hu, ⟨v, hv, rfl⟩ | ⟨g, hg, rfl⟩, hval⟩
    · have hval' : v ∈ ρ := hval
      rcases (hP v).mp hv with rfl | rfl | rfl | rfl | rfl <;> tauto
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g, hg, hu, hval⟩))))
  · rintro (h | h | h | h | h | ⟨g, hg, hc, hv⟩)
    · exact ⟨_, h.1, Or.inl ⟨z0, (hP _).mpr (by simp), rfl⟩, h.2⟩
    · exact ⟨_, h.1, Or.inl ⟨z1, (hP _).mpr (by simp), rfl⟩, h.2⟩
    · exact ⟨_, h.1, Or.inl ⟨z2, (hP _).mpr (by simp), rfl⟩, h.2⟩
    · exact ⟨_, h.1, Or.inl ⟨y1, (hP _).mpr (by simp), rfl⟩, h.2⟩
    · exact ⟨_, h.1, Or.inl ⟨y2, (hP _).mpr (by simp), rfl⟩, h.2⟩
    · exact ⟨_, hc, Or.inr ⟨g, hg, rfl⟩, hv⟩

def S1 (C : Ckt V) (P : Finset V) (y1 : V) (a : V ⊕ ℕ) : Prop :=
  Cn C P (Sum.inl y1) a ∨ ∃ g ∈ be C P, Rd C g (Sum.inl y1) ∧ Cn C P (Sum.inr g) a

theorem ctx_dead2 (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) :
    ¬ Dd C {z1, z2, y2} a ↔ Cn C P (Sum.inl z0) a ∨ S1 C P y1 a := by
  have hW := h.1.2.1.1.1
  have hne := loc_ne h.1
  unfold Dd
  rw [not_not, ctx_src h]
  have m0 : z0 ∈ (↑({z1, z2, y2} : Finset V) : Set V)ᶜ := by simp [hne]
  have m1 : y1 ∈ (↑({z1, z2, y2} : Finset V) : Set V)ᶜ := by
    simp [hne, hne.2.2.2.2.2.1.symm, hne.2.2.2.2.2.2.2.1.symm]
  have n1 : z1 ∉ (↑({z1, z2, y2} : Finset V) : Set V)ᶜ := by simp
  have n2 : z2 ∉ (↑({z1, z2, y2} : Finset V) : Set V)ᶜ := by simp
  have n3 : y2 ∉ (↑({z1, z2, y2} : Finset V) : Set V)ᶜ := by simp
  constructor
  · rintro (x | x | x | x | x | ⟨g, hg, hc, hv⟩)
    · exact Or.inl x.1
    · exact absurd x.2 n1
    · exact absurd x.2 n2
    · exact Or.inr (Or.inl x.1)
    · exact absurd x.2 n3
    · rcases (ctx_be h hg).2 with f | f
      · exact Or.inr (Or.inr ⟨g, hg, f.2.1, hc⟩)
      · exact absurd (ctx_be_val h hg f.2.1 hv) n3
  · rintro (x | x | ⟨g, hg, hr, hc⟩)
    · exact Or.inl ⟨x, m0⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, m1⟩)))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g, hg, hc, ?_⟩))))
      obtain ⟨k, hk, hgk⟩ := other_operand hr
      have hlive : ¬ Dd C P k := by
        have := (Finset.mem_filter.mp hg).2.2
        have d1 : Dd C P (Sum.inl y1) := (dd_inl _ _ _).mpr (by rw [h.2.1]; simp)
        rcases hk with e | e
        · rw [e.1, e.2] at this; tauto
        · rw [e.1, e.2] at this; tauto
      have hkv : C.val (↑({z1, z2, y2} : Finset V) : Set V)ᶜ k := by
        unfold Dd at hlive
        rw [not_not] at hlive
        refine val_mono hW ?_ k (rd_vl hW hgk).1 hlive
        rw [h.2.1]
        intro v hv hm
        refine hv ?_
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hm ⊢
        tauto
      have hyv : C.val (↑({z1, z2, y2} : Finset V) : Set V)ᶜ (Sum.inl y1) := m1
      rw [val_and hW hr.1 (ctx_be h hg).1]
      rcases hk with e | e
      · rw [e.1, e.2]; exact ⟨hyv, hkv⟩
      · rw [e.1, e.2]; exact ⟨hkv, hyv⟩

theorem ctx_match (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) :
    (Cn C P (Sum.inl z0) a ∨ S1 C P y1 a) ↔ (Cn C P (Sum.inl z0) b ∨ S1 C P y1 b) := by
  rw [← ctx_dead2 h, ← ctx_dead2 (ctx_ab h)]
  by_contra hne
  have hi : i ∈ be C {z1, z2, y2} := by
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h.2.2.1).1, h.2.2.2.1, ?_⟩
    rcases h.2.2.2.2.2 with e | e
    · rw [e.1, e.2]; tauto
    · rw [e.1, e.2]; tauto
  have h2 := loc_be2 h.1 i hi
  have hlc := loc_c h.1
  rw [← h.2.1] at hlc
  exact ctx_notbe h h.2.2.1 (hlc.2.2.2.2.2.2.2 i h2.1 h2.2)

theorem ctx_S1 (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) (ha : S1 C P y1 a) (hb : S1 C P y1 b) :
    fo C (Sum.inl y1) = 2 ∧ Cn C P (Sum.inl y1) a ∧ Cn C P (Sum.inl y1) b := by
  have hlc := loc_c h.1
  rcases hlc.2.1 with f | f
  · exfalso
    rcases ha with ha | ⟨g, hg, hr, hc⟩
    · exact ctx_y1 h f ha
    rcases hb with hb | ⟨g', hg', hr', hc'⟩
    · exact ctx_y1 (ctx_ab h) f hb
    have := rd_unique f.le hr hr'
    subst this
    exact ctx_disj h hc hc' (by simp) (by simp)
  · have hnb : ∀ g ∈ be C P, ¬ Rd C g (Sum.inl y1) := by
      intro g hg hr
      rcases (ctx_be h hg).2 with e | e
      · omega
      · exact e.2.2 hr
    refine ⟨f, ?_, ?_⟩
    · rcases ha with ha | ⟨g, hg, hr, -⟩
      · exact ha
      · exact absurd hr (hnb g hg)
    · rcases hb with hb | ⟨g, hg, hr, -⟩
      · exact hb
      · exact absurd hr (hnb g hg)

theorem ctx_fn (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) :
    Fn E X {z0, y1} ∧ Fn E X {z0, y2} ∧ Fn E X {z1, y1} ∧ Fn E X {z2, y2} ∧
    ¬ Fn E X {y1, y2} ∧ ¬ Fn E X {y2, y1} ∧ ¬ Fn E X {z1, y2} ∧ ¬ Fn E X {z2, y1} := by
  have hne := loc_ne h.1
  obtain ⟨hE, hO, hN, ⟨hp1, hp2, hz0, e1, e2, hadj, hnd, hyy, -⟩, -⟩ := h.1
  simp only [fn_pair hE]
  refine ⟨⟨e1, hz0, hp1.1⟩, ⟨e2, hz0, hp2.1⟩, ⟨hE.1 _ _ hp1.2.2.1, hp1.2.1, hp1.1⟩,
    ⟨hE.1 _ _ hp2.2.2.1, hp2.2.1, hp2.1⟩, fun x => hyy x.1, fun x => hyy (hE.1 _ _ x.1), ?_, ?_⟩
  · rintro ⟨x, -, -⟩
    exact hne.2.2.2.2.2.2.2.2.2 (hp1.2.2.2 _ hp2.1 x).symm
  · rintro ⟨x, -, -⟩
    exact hne.2.2.2.2.2.2.2.2.2 (hp2.2.2.2 _ hp1.1 x)

theorem ctx_z0 (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) : ¬ Cn C P (Sum.inl z0) a := by
  intro hz
  have hne := loc_ne h.1
  have hfn := ctx_fn h
  have hE := h.1.1
  have hzb : ¬ Cn C P (Sum.inl z0) b := fun hb => ctx_disj h hz hb
    (fun e => hne.2.2.1 (Sum.inl.inj e)) (fun e => hne.2.2.2.1 (Sum.inl.inj e))
  have s1 : S1 C P y1 b := ((ctx_match h).mp (Or.inl hz)).resolve_left hzb
  have s2 : S1 C P y2 b := ((ctx_match (ctx_symm h)).mp (Or.inl hz)).resolve_left hzb
  have n1 : ¬ Cn C P (Sum.inl y1) a := fun hc => ctx_cross h (s := y1) hz hc hne.2.2.1
    hne.2.2.2.1 hfn.1 (by rw [Set.pair_eq_singleton]; exact fn_single hE _)
  have n2 : ¬ Cn C P (Sum.inl y2) a := fun hc => ctx_cross h (s := y2) hz hc hne.2.2.1
    hne.2.2.2.1 hfn.2.1 (by rw [Set.pair_eq_singleton]; exact fn_single hE _)
  have n3 : ¬ Cn C P (Sum.inl z1) a := fun hc => ctx_cross h (s := y2) hz hc hne.2.2.1
    hne.2.2.2.1 hfn.2.1 hfn.2.2.2.2.2.2.1
  have n4 : ¬ Cn C P (Sum.inl z2) a := fun hc => ctx_cross h (s := y1) hz hc hne.2.2.1
    hne.2.2.2.1 hfn.1 hfn.2.2.2.2.2.2.2
  have n5 : ∀ g ∈ be C P, ¬ Cn C P (Sum.inr g) a := by
    intro g hg hc
    rcases (ctx_be h hg).2 with f | f
    · exact n1 (ctx_S1 h (Or.inr ⟨g, hg, f.2.1, hc⟩) s1).2.1
    · exact n2 (ctx_S1 (ctx_symm h) (Or.inr ⟨g, hg, f.2.1, hc⟩) s2).2.1
  refine ctx_single h (loc_z0 h.1).2 fun ρ => ?_
  rw [ctx_src h]
  constructor
  · rintro (x | x | x | x | x | ⟨g, hg, hc, -⟩)
    · exact x.2
    · exact absurd x.1 n3
    · exact absurd x.1 n4
    · exact absurd x.1 n1
    · exact absurd x.1 n2
    · exact absurd hc (n5 g hg)
  · exact fun x => Or.inl ⟨hz, x⟩

theorem ctx_noz (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) (hc : Cn C P (Sum.inl y1) a) :
    ¬ Cn C P (Sum.inl z1) a ∧ ¬ Cn C P (Sum.inl z2) a := by
  have hne := loc_ne h.1
  have hfn := ctx_fn h
  have hE := h.1.1
  exact ⟨fun hz => ctx_cross h (s := y1) hz hc hne.2.2.2.2.2.1 hne.2.2.2.2.2.2.1 hfn.2.2.1
      (by rw [Set.pair_eq_singleton]; exact fn_single hE _),
    fun hz => ctx_cross h (s := y2) hz hc hne.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.1
      hfn.2.2.2.1 hfn.2.2.2.2.1⟩

theorem ctx_one (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) (s1 : S1 C P y1 a)
    (s2 : ¬ S1 C P y2 a) : False := by
  have hz := ctx_z0 h
  have hzb := ctx_z0 (ctx_ab h)
  have s1b : S1 C P y1 b := ((ctx_match h).mp (Or.inr s1)).resolve_left hzb
  obtain ⟨f, ca, cb⟩ := ctx_S1 h s1 s1b
  have hnz := ctx_noz h ca
  refine ctx_not_le h fun ρ hv => ?_
  rw [ctx_src h] at hv
  rw [ctx_src (ctx_ab h)]
  rcases hv with x | x | x | x | x | ⟨g, hg, hc, -⟩
  · exact absurd x.1 hz
  · exact absurd x.1 hnz.1
  · exact absurd x.1 hnz.2
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨cb, x.2⟩)))
  · exact absurd (Or.inl x.1) s2
  · rcases (ctx_be h hg).2 with e | e
    · omega
    · exact absurd (Or.inr ⟨g, hg, e.2.1, hc⟩) s2

theorem ctx_false (h : Ctx E X C z0 z1 z2 y1 y2 P i a b) : False := by
  have hW := h.1.2.1.1.1
  have hne := loc_ne h.1
  have hz := ctx_z0 h
  have hzb := ctx_z0 (ctx_ab h)
  by_cases s1 : S1 C P y1 a
  · by_cases s2 : S1 C P y2 a
    · have s1b : S1 C P y1 b := ((ctx_match h).mp (Or.inr s1)).resolve_left hzb
      have s2b : S1 C P y2 b := ((ctx_match (ctx_symm h)).mp (Or.inr s2)).resolve_left hzb
      obtain ⟨f1, ca1, cb1⟩ := ctx_S1 h s1 s1b
      obtain ⟨f2, ca2, cb2⟩ := ctx_S1 (ctx_symm h) s2 s2b
      have hnz := ctx_noz h ca1
      refine ctx_not_le h fun ρ hv => ?_
      rw [ctx_src h] at hv
      rw [ctx_src (ctx_ab h)]
      rcases hv with x | x | x | x | x | ⟨g, hg, hc, -⟩
      · exact absurd x.1 hz
      · exact absurd x.1 hnz.1
      · exact absurd x.1 hnz.2
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨cb1, x.2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨cb2, x.2⟩))))
      · rcases (ctx_be h hg).2 with e | e <;> omega
    · exact ctx_one h s1 s2
  · by_cases s2 : S1 C P y2 a
    · exact ctx_one (ctx_symm h) s2 s1
    · -- only z1 and z2 feed a and b
      have s1b : ¬ S1 C P y1 b := fun s => s1 (((ctx_match h).mpr (Or.inr s)).resolve_left hz)
      have s2b : ¬ S1 C P y2 b := fun s =>
        s2 (((ctx_match (ctx_symm h)).mpr (Or.inr s)).resolve_left hz)
      have hsrc : ∀ {a b : V ⊕ ℕ}, Ctx E X C z0 z1 z2 y1 y2 P i a b →
          ¬ Cn C P (Sum.inl z0) a → ¬ S1 C P y1 a → ¬ S1 C P y2 a → ∀ ρ, C.val ρ a ↔
          (Cn C P (Sum.inl z1) a ∧ z1 ∈ ρ) ∨ (Cn C P (Sum.inl z2) a ∧ z2 ∈ ρ) := by
        intro a b h hz s1 s2 ρ
        rw [ctx_src h]
        constructor
        · rintro (x | x | x | x | x | ⟨g, hg, hc, -⟩)
          · exact absurd x.1 hz
          · exact Or.inl x
          · exact Or.inr x
          · exact absurd (Or.inl x.1) s1
          · exact absurd (Or.inl x.1) s2
          · rcases (ctx_be h hg).2 with e | e
            · exact absurd (Or.inr ⟨g, hg, e.2.1, hc⟩) s1
            · exact absurd (Or.inr ⟨g, hg, e.2.1, hc⟩) s2
        · rintro (x | x)
          · exact Or.inr (Or.inl x)
          · exact Or.inr (Or.inr (Or.inl x))
      have hA := hsrc h hz s1 s2
      have hB := hsrc (ctx_ab h) hzb s1b s2b
      by_cases c1 : Cn C P (Sum.inl z1) a <;> by_cases c2 : Cn C P (Sum.inl z2) a
      · have d1 : ¬ Cn C P (Sum.inl z1) b := fun hb => ctx_disj h c1 hb
          (fun e => hne.2.2.2.2.2.1 (Sum.inl.inj e)) (fun e => hne.2.2.2.2.2.2.1 (Sum.inl.inj e))
        have d2 : ¬ Cn C P (Sum.inl z2) b := fun hb => ctx_disj h c2 hb
          (fun e => hne.2.2.2.2.2.2.2.1 (Sum.inl.inj e))
          (fun e => hne.2.2.2.2.2.2.2.2.1 (Sum.inl.inj e))
        have := (hB Set.univ).mp (val_univ hW b (ctx_a (ctx_ab h)).2.1)
        tauto
      · refine ctx_single h (loc_z1 h.1).2 fun ρ => (hA ρ).trans ?_
        tauto
      · refine ctx_single h (loc_z1 (loc_symm h.1)).2 fun ρ => (hA ρ).trans ?_
        tauto
      · have := (hA Set.univ).mp (val_univ hW a (ctx_a h).2.1)
        tauto

theorem loc_noand (h : Loc E X C z0 z1 z2 y1 y2) :
    ∀ g ∈ al C {z0, z1, z2, y1, y2}, C.op g = false := by
  by_contra hex
  push Not at hex
  obtain ⟨g, hg, ho⟩ := hex
  have hne : ((al C {z0, z1, z2, y1, y2}).filter (fun g => C.op g = true)).Nonempty :=
    ⟨g, Finset.mem_filter.mpr ⟨hg, by simpa using ho⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ id hne
  rw [Finset.mem_filter] at hi
  exact ctx_false (E := E) (X := X) (P := {z0, z1, z2, y1, y2}) (i := i)
    ⟨h, rfl, hi.1, hi.2, fun k hk hok => hmin k (Finset.mem_filter.mpr ⟨hk, hok⟩),
      Or.inl ⟨rfl, rfl⟩⟩

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

theorem loc_final {z0 z1 z2 y1 y2 : V} (h : Loc E X C z0 z1 z2 y1 y2) :
    (su C {z0, z1, z2, y1, y2}).card + 7 = C.G.card ∧
    ((su C {z0, z1, z2, y1, y2}).filter (fun g => C.op g = true)).card +
      ((if fo C (Sum.inl y1) = 1 then 1 else 0) + (if fo C (Sum.inl y2) = 1 then 1 else 0)) =
      nAnd C := by
  have hc := loc_c h
  have hno := loc_noand h
  obtain ⟨hE, hO, hN, hG, hlive, -⟩ := h
  obtain ⟨⟨p1y, p1z, p1e, -⟩, ⟨p2y, p2z, p2e, -⟩, hz0, e01, e02, -, hnd, -⟩ := hG
  have hP5 : (({z0, z1, z2, y1, y2} : Finset V)).card = 5 := by
    have : ({z0, z1, z2, y1, y2} : Finset V) = [z0, z1, z2, y1, y2].toFinset := by simp
    rw [this, List.toFinset_card_of_nodup hnd]; rfl
  have hcl := count_live (opt_useful hO) (P := {z0, z1, z2, y1, y2}) (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact read_pos hE hO.1 hz0 p1y e01
    · exact read_pos hE hO.1 p1z p1y (hE.1 _ _ p1e)
    · exact read_pos hE hO.1 p2z p2y (hE.1 _ _ p2e)
    · exact read_pos hE hO.1 p1y p1z p1e
    · exact read_pos hE hO.1 p2y p2z p2e) hlive
  have hpart := count_part C ({z0, z1, z2, y1, y2} : Finset V)
  unfold kl at hpart
  refine ⟨by omega, ?_⟩
  rw [← hc.2.2.2.1]
  unfold nAnd
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext g
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h1, h2⟩ | h1)
      · exact ⟨(Finset.mem_filter.mp h1).1, h2⟩
      · have := Finset.mem_filter.mp h1
        exact ⟨this.1, this.2.1⟩
    · rintro ⟨h1, h2⟩
      rcases kinds_cover ({z0, z1, z2, y1, y2} : Finset V) h1 with h | h | h | h
      · rw [hno g h] at h2; cases h2
      · exact Or.inr h
      · rw [(Finset.mem_filter.mp h).2.1] at h2; cases h2
      · exact Or.inl ⟨h, h2⟩
  · rw [Finset.disjoint_left]
    intro g h1 h2
    have a := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
    have b := (Finset.mem_filter.mp h2).2.2
    tauto

end

section
variable {V : Type} [DecidableEq V] {C : Ckt V}

def Spl {ι : Type} (C : Ckt V) (J U : Finset ι) (y z : ι → V) (R : Set V) (w : V ⊕ ℕ) : Prop :=
  ∀ A B : Set V, (∀ v ∈ A, ∃ i ∈ J, i ∉ U ∧ (v = y i ∨ v = z i)) →
    (∀ v ∈ B, ∃ i ∈ J, i ∉ U ∧ (v = y i ∨ v = z i)) →
    C.val (R ∪ (A ∪ B)) w → C.val (R ∪ A) w ∨ C.val (R ∪ B) w

omit [DecidableEq V] in
theorem spl_single {ι : Type} {J U : Finset ι} {y z : ι → V} {R : Set V} {w : V ⊕ ℕ}
    (h : Spl C J U y z R w) {A : Set V} (hA : ∀ v ∈ A, ∃ i ∈ J, i ∉ U ∧ (v = y i ∨ v = z i))
    (hon : C.val (R ∪ A) w) (hR : ¬ C.val R w) :
    ∃ i ∈ J, i ∉ U ∧ (C.val (R ∪ {y i}) w ∨ C.val (R ∪ {z i}) w) := by
  have hfin : A.Finite := by
    refine Set.Finite.subset ((J.finite_toSet.image y).union (J.finite_toSet.image z)) ?_
    intro v hv
    obtain ⟨i, hi, _, e | e⟩ := hA v hv
    · exact Or.inl ⟨i, hi, e.symm⟩
    · exact Or.inr ⟨i, hi, e.symm⟩
  induction A, hfin using Set.Finite.induction_on with
  | empty => rw [Set.union_empty] at hon; exact absurd hon hR
  | @insert v A _ _ ih =>
    have hA' : ∀ u ∈ A, ∃ i ∈ J, i ∉ U ∧ (u = y i ∨ u = z i) := fun u hu =>
      hA u (Set.mem_insert_of_mem _ hu)
    have hv := hA v (Set.mem_insert _ _)
    have hs := h {v} A (fun u hu => by rw [Set.mem_singleton_iff.mp hu]; exact hv) hA' (by
      rw [Set.singleton_union]; exact hon)
    rcases hs with hs | hs
    · obtain ⟨i, hi, hU, e | e⟩ := hv
      · exact ⟨i, hi, hU, Or.inl (e ▸ hs)⟩
      · exact ⟨i, hi, hU, Or.inr (e ▸ hs)⟩
    · exact ih hA' hs

theorem and_bound {ι : Type} (hW : Wf C) (J : Finset ι) (y z : ι → V) (hy : Set.InjOn y ↑J)
    (hz : Set.InjOn z ↑J) (hyz : ∀ i ∈ J, ∀ j ∈ J, y i ≠ z j)
    (hC : ∀ ρ : Set V, (∀ v ∈ ρ, ∃ i ∈ J, v = y i ∨ v = z i) →
      (C.val ρ C.out ↔ ∃ i ∈ J, y i ∈ ρ ∧ z i ∈ ρ)) : J.card ≤ nAnd C := by
  have key : ∀ n : ℕ, ∃ U ⊆ J, ∃ R : Set V, U.card ≤
      (C.G.filter (fun g => C.op g = true ∧ g < n)).card ∧
      (∀ v ∈ R, ∃ i ∈ U, v = y i ∨ v = z i) ∧ (∀ i ∈ J, ¬ (y i ∈ R ∧ z i ∈ R)) ∧
      ∀ w, Vl C w → rk w ≤ n → Spl C J U y z R w := by
    intro n
    induction n with
    | zero =>
      refine ⟨∅, Finset.empty_subset _, ∅, by simp, fun v hv => hv.elim, fun i _ h => h.1, ?_⟩
      intro w _ hr A B _ _ hv
      rcases w with v | k
      · rcases hv with hv | hv | hv
        · exact hv.elim
        · exact Or.inl (Or.inr hv)
        · exact Or.inr (Or.inr hv)
      · simp [rk] at hr
    | succ n ih =>
      obtain ⟨U, hUJ, R, hcard, hR1, hR2, hspl⟩ := ih
      have hmono : (C.G.filter (fun g => C.op g = true ∧ g < n)).card ≤
          (C.G.filter (fun g => C.op g = true ∧ g < n + 1)).card := by
        refine Finset.card_le_card fun g hg => ?_
        rw [Finset.mem_filter] at hg ⊢
        exact ⟨hg.1, hg.2.1, by omega⟩
      have hred : ∀ U' R', (∀ w, Vl C w → rk w ≤ n → Spl C J U' y z R' w) →
          (n ∈ C.G → Spl C J U' y z R' (Sum.inr n)) →
          ∀ w, Vl C w → rk w ≤ n + 1 → Spl C J U' y z R' w := by
        intro U' R' h1 h2 w hw hr
        rcases Nat.lt_or_ge n (rk w) with h | h
        · rcases w with v | k
          · simp [rk] at h
          · have : k = n := by
              simp only [rk, Sum.elim_inr] at h hr
              omega
            subst this
            exact h2 (hw k rfl)
        · exact h1 w hw h
      by_cases hand : n ∈ C.G ∧ C.op n = true
      · obtain ⟨hn, ho⟩ := hand
        have hvl := hW.1 n hn
        have hone : ∀ U' R', (∀ w, Vl C w → rk w ≤ n → Spl C J U' y z R' w) →
            (C.val R' (C.l n) ∨ C.val R' (C.r n)) → Spl C J U' y z R' (Sum.inr n) := by
          intro U' R' h1 h2 A B hA hB hv
          rw [val_and hW hn ho] at hv ⊢
          rw [val_and hW hn ho]
          have up : ∀ w, Vl C w → ∀ D, C.val R' w → C.val (R' ∪ D) w := fun w hw D =>
            val_mono hW Set.subset_union_left w hw
          rcases h2 with h2 | h2
          · rcases h1 _ hvl.2.1 hvl.2.2 A B hA hB hv.2 with h | h
            · exact Or.inl ⟨up _ hvl.1.1 A h2, h⟩
            · exact Or.inr ⟨up _ hvl.1.1 B h2, h⟩
          · rcases h1 _ hvl.1.1 hvl.1.2 A B hA hB hv.1 with h | h
            · exact Or.inl ⟨h, up _ hvl.2.1 A h2⟩
            · exact Or.inr ⟨h, up _ hvl.2.1 B h2⟩
        by_cases hon : C.val R (C.l n) ∨ C.val R (C.r n)
        · exact ⟨U, hUJ, R, hcard.trans hmono, hR1, hR2,
            hred U R hspl fun _ => hone U R hspl hon⟩
        · push Not at hon
          by_cases hex : ∃ i ∈ J, i ∉ U ∧ (C.val (R ∪ {y i}) (C.l n) ∨ C.val (R ∪ {z i}) (C.l n))
          · obtain ⟨i, hi, hiU, hval⟩ := hex
            obtain ⟨v, hv, hvon⟩ : ∃ v, (v = y i ∨ v = z i) ∧ C.val (R ∪ {v}) (C.l n) := by
              rcases hval with h | h
              · exact ⟨_, Or.inl rfl, h⟩
              · exact ⟨_, Or.inr rfl, h⟩
            have hidx : ∀ j ∈ J, ∀ u, (u = y i ∨ u = z i) → (u = y j ∨ u = z j) → j = i := by
              rintro j hj u (h | h) (h' | h')
              · exact hy hj hi (h'.symm.trans h)
              · exact absurd (h.symm.trans h') (hyz i hi j hj)
              · exact absurd (h'.symm.trans h) (hyz j hj i hi)
              · exact hz hj hi (h'.symm.trans h)
            have hiR : ∀ u, (u = y i ∨ u = z i) → u ∉ R := by
              intro u hu huR
              obtain ⟨j, hj, e⟩ := hR1 u huR
              exact hiU (hidx j (hUJ hj) u hu e ▸ hj)
            have hspl' : ∀ w, Vl C w → rk w ≤ n → Spl C J (insert i U) y z (R ∪ {v}) w := by
              intro w hw hr A B hA hB hval
              have hext : ∀ D : Set V, (∀ u ∈ D, ∃ j ∈ J, j ∉ insert i U ∧ (u = y j ∨ u = z j)) →
                  ∀ u ∈ ({v} ∪ D : Set V), ∃ j ∈ J, j ∉ U ∧ (u = y j ∨ u = z j) := by
                rintro D hD u (hu | hu)
                · exact ⟨i, hi, hiU, by rw [Set.mem_singleton_iff.mp hu]; exact hv⟩
                · obtain ⟨j, hj, hjU, e⟩ := hD u hu
                  exact ⟨j, hj, fun h => hjU (Finset.mem_insert_of_mem h), e⟩
              have := hspl w hw hr ({v} ∪ A) ({v} ∪ B) (hext A hA) (hext B hB) (by
                convert hval using 1
                ext u
                simp only [Set.mem_union]
                tauto)
              rwa [← Set.union_assoc, ← Set.union_assoc] at this
            refine ⟨insert i U, Finset.insert_subset hi hUJ, R ∪ {v}, ?_, ?_, ?_,
              hred _ _ hspl' fun _ => hone _ _ hspl' (Or.inl hvon)⟩
            · rw [Finset.card_insert_of_notMem hiU]
              have hlt : (C.G.filter (fun g => C.op g = true ∧ g < n)).card <
                  (C.G.filter (fun g => C.op g = true ∧ g < n + 1)).card := by
                refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ⟨n, ?_, ?_⟩)
                · intro g hg
                  rw [Finset.mem_filter] at hg ⊢
                  exact ⟨hg.1, hg.2.1, by omega⟩
                · rw [Finset.mem_filter]; exact ⟨hn, ho, by omega⟩
                · rw [Finset.mem_filter]; omega
              omega
            · rintro u (hu | hu)
              · obtain ⟨j, hj, e⟩ := hR1 u hu
                exact ⟨j, Finset.mem_insert_of_mem hj, e⟩
              · exact ⟨i, Finset.mem_insert_self _ _, by rw [Set.mem_singleton_iff.mp hu]; exact hv⟩
            · rintro j hj ⟨h1, h2⟩
              rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
              · exact hR2 j hj ⟨h1, h2⟩
              · have := hidx j hj v hv (Or.inr (Set.mem_singleton_iff.mp h2).symm)
                rw [this] at h1
                exact hiR _ (Or.inl rfl) h1
              · have := hidx j hj v hv (Or.inl (Set.mem_singleton_iff.mp h1).symm)
                rw [this] at h2
                exact hiR _ (Or.inr rfl) h2
              · exact hyz j hj j hj ((Set.mem_singleton_iff.mp h1).trans
                  (Set.mem_singleton_iff.mp h2).symm)
          · refine ⟨U, hUJ, R, hcard.trans hmono, hR1, hR2, hred U R hspl fun _ => ?_⟩
            intro A B hA hB hval
            rw [val_and hW hn ho] at hval
            refine absurd (spl_single (hspl _ hvl.1.1 hvl.1.2) (A := A ∪ B) ?_ hval.1 hon.1) hex
            rintro u (hu | hu)
            · exact hA u hu
            · exact hB u hu
      · refine ⟨U, hUJ, R, hcard.trans hmono, hR1, hR2, hred U R hspl fun hn => ?_⟩
        have ho : C.op n = false := by
          by_contra ho
          exact hand ⟨hn, by simpa using ho⟩
        intro A B hA hB hval
        rw [val_or hW hn ho] at hval
        rw [val_or hW hn ho, val_or hW hn ho]
        have hvl := hW.1 n hn
        rcases hval with h | h
        · rcases hspl _ hvl.1.1 hvl.1.2 A B hA hB h with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)
        · rcases hspl _ hvl.2.1 hvl.2.2 A B hA hB h with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inr h)
  obtain ⟨U, hUJ, R, hcard, hR1, hR2, hspl⟩ := key (rk C.out)
  by_contra hlt
  have hle : (C.G.filter (fun g => C.op g = true ∧ g < rk C.out)).card ≤ nAnd C := by
    refine Finset.card_le_card fun g hg => ?_
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨hg.1, hg.2.1⟩
  obtain ⟨i, hi, hiU⟩ : ∃ i ∈ J, i ∉ U := by
    by_contra hno
    push Not at hno
    have := Finset.card_le_card hno
    omega
  have hRin : ∀ D : Set V, (∀ v ∈ D, v = y i ∨ v = z i) → ∀ v ∈ R ∪ D,
      ∃ j ∈ J, v = y j ∨ v = z j := by
    rintro D hD v (hv | hv)
    · obtain ⟨j, hj, e⟩ := hR1 v hv
      exact ⟨j, hUJ hj, e⟩
    · exact ⟨i, hi, hD v hv⟩
  have hon : C.val (R ∪ ({y i} ∪ {z i})) C.out := by
    refine (hC _ (hRin _ ?_)).mpr ⟨i, hi, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
    rintro v (hv | hv)
    · exact Or.inl hv
    · exact Or.inr hv
  have hiR : y i ∉ R ∧ z i ∉ R := by
    constructor
    · intro h
      obtain ⟨j, hj, e | e⟩ := hR1 _ h
      · exact hiU (hy hi (hUJ hj) e ▸ hj)
      · exact hyz i hi j (hUJ hj) e
    · intro h
      obtain ⟨j, hj, e | e⟩ := hR1 _ h
      · exact hyz j (hUJ hj) i hi e.symm
      · exact hiU (hz hi (hUJ hj) e ▸ hj)
  rcases hspl _ hW.2 le_rfl {y i} {z i}
    (fun v hv => ⟨i, hi, hiU, Or.inl (Set.mem_singleton_iff.mp hv)⟩)
    (fun v hv => ⟨i, hi, hiU, Or.inr (Set.mem_singleton_iff.mp hv)⟩) hon with h | h
  · obtain ⟨j, hj, h1, h2⟩ := (hC _ (hRin _ (fun v hv => Or.inl hv))).mp h
    rcases h2 with h2 | h2
    · rcases h1 with h1 | h1
      · exact hR2 j hj ⟨h1, h2⟩
      · rw [hy hj hi h1] at h2
        exact hiR.2 h2
    · exact hyz i hi j hj (Set.mem_singleton_iff.mp h2).symm
  · obtain ⟨j, hj, h1, h2⟩ := (hC _ (hRin _ (fun v hv => Or.inr hv))).mp h
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact hR2 j hj ⟨h1, h2⟩
      · rw [hz hj hi h2] at h1
        exact hiR.1 h1
    · exact hyz j hj i hi (Set.mem_singleton_iff.mp h1)

end

section
variable {V : Type} [DecidableEq V] {E : V → V → Prop} {X Y : Set V} {C : Ckt V}

theorem opt_reads (hC : Opt E X ∅ C) (he : HasEdge E X) {v : V} (hv : v ∉ X) :
    fo C (Sum.inl v) = 0 := by
  by_contra hf
  obtain ⟨g, hg⟩ := fo_pos.mp (Nat.one_le_iff_ne_zero.mpr hf)
  have hX : X \ ↑({v} : Finset V) = X := by
    ext u
    simp only [Finset.coe_singleton, Set.mem_diff, Set.mem_singleton_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, fun e => hv (e ▸ h)⟩⟩
  have hlive := out_live (P := {v}) hC.1.2.2.1 (by rw [hX]; exact he)
  obtain ⟨C', h1, h2, _⟩ := zero hC.1 {v} hlive
  rw [hX] at h1
  have h3 := hC.2 C' h1
  have h4 := count_part C {v}
  have h5 : 1 ≤ kl C {v} := by
    have hd : Dd C {v} (Sum.inl v) := (dd_inl _ _ _).mpr (by simp)
    unfold kl
    rcases kinds_cover (C := C) {v} hg.1 with h | h | h | h
    · have := Finset.card_pos.mpr ⟨g, h⟩; omega
    · have := Finset.card_pos.mpr ⟨g, h⟩; omega
    · have := Finset.card_pos.mpr ⟨g, h⟩; omega
    · exfalso
      have := (Finset.mem_filter.mp h).2
      rcases hg.2 with e | e
      · exact this.1 (e ▸ hd)
      · exact this.2 (e ▸ hd)
  rw [h2] at h3
  omega

theorem relabel {X2 : Set V} (hE : Gr E) (he : HasEdge E X) (hC : Opt E X ∅ C) (τ : V → V)
    (hinj : Set.InjOn τ X) (him : τ '' X = X2)
    (hadj : ∀ u ∈ X, ∀ v ∈ X, (E u v ↔ E (τ u) (τ v))) :
    ∃ C2 : Ckt V, Good E X2 ∅ C2 ∧ C2.G.card = C.G.card := by
  obtain ⟨⟨hW, hcl, hcomp, _⟩, hmin⟩ := hC
  have hrd : ∀ v, v ∉ X → ∀ k, ¬ Rd C k (Sum.inl v) := by
    intro v hv k hk
    have := fo_pos.mpr ⟨k, hk⟩
    rw [opt_reads ⟨⟨hW, hcl, hcomp, fun y hy => hy.elim⟩, hmin⟩ he hv] at this
    omega
  let m : V ⊕ ℕ → V ⊕ ℕ := Sum.map τ id
  let D : Ckt V := Ckt.mk C.G C.op (fun g => m (C.l g)) (fun g => m (C.r g)) (m C.out)
  have hmvl : ∀ w, Vl C w → Vl D (m w) := by
    intro w hw k hk
    rcases w with v | j
    · cases hk
    · cases hk; exact hw _ rfl
  have hmrk : ∀ w : V ⊕ ℕ, rk (m w) = rk w := by
    intro w
    rcases w with v | j <;> rfl
  have hDW : Wf D := by
    refine ⟨fun g hg => ?_, hmvl _ hW.2⟩
    have := hW.1 g hg
    exact ⟨⟨hmvl _ this.1.1, (hmrk _).le.trans this.1.2⟩,
      ⟨hmvl _ this.2.1, (hmrk _).le.trans this.2.2⟩⟩
  have hval : ∀ ρ, ∀ w, Vl C w → (D.val ρ (m w) ↔ C.val {v | τ v ∈ ρ} w) := by
    intro ρ
    refine wire_ind' hW (fun v => Iff.rfl) (fun g hg hl hr => ?_)
    have e := val_gate hDW (g := g) hg ρ
    show D.val ρ (Sum.inr g) ↔ _
    rw [e, val_gate hW hg]
    show (if C.op g = true then _ else _) ↔ _
    split_ifs
    · exact and_congr hl hr
    · exact or_congr hl hr
  refine ⟨D, ⟨hDW, ?_, ?_, fun y hy => hy.elim⟩, rfl⟩
  · intro g hg ho v hv
    have h1 := (hval {v} (Sum.inr g) (vl_inr hg)).mp hv
    by_cases hex : ∃ u ∈ X, τ u = v
    · obtain ⟨u, hu, hτ⟩ := hex
      refine hcl g hg ho u (escape hW {w | ∃ a, a ∉ X ∧ w = Sum.inl a} ?_ ?_ _ (vl_inr hg) ?_ h1)
      · intro a ha hm
        have haX : a ∈ X := by
          by_contra hn
          exact ha ⟨a, hn, rfl⟩
        exact hinj haX hu ((Set.mem_singleton_iff.mp hm).trans hτ.symm)
      · rintro i hi _ (⟨a, ha, e⟩ | ⟨a, ha, e⟩)
        · exact absurd ⟨hi, Or.inl e⟩ (hrd a ha i)
        · exact absurd ⟨hi, Or.inr e⟩ (hrd a ha i)
      · rintro ⟨a, _, e⟩; cases e
    · refine val_empty hW _ (vl_inr hg) (escape hW {w | ∃ a, a ∉ X ∧ w = Sum.inl a} ?_ ?_ _
        (vl_inr hg) ?_ h1)
      · intro a ha hm
        have haX : a ∈ X := by
          by_contra hn
          exact ha ⟨a, hn, rfl⟩
        exact hex ⟨a, haX, Set.mem_singleton_iff.mp hm⟩
      · rintro i hi _ (⟨a, ha, e⟩ | ⟨a, ha, e⟩)
        · exact absurd ⟨hi, Or.inl e⟩ (hrd a ha i)
        · exact absurd ⟨hi, Or.inr e⟩ (hrd a ha i)
      · rintro ⟨a, _, e⟩; cases e
  · intro ρ
    refine (hval ρ C.out hW.2).trans ((hcomp _).trans ?_)
    constructor
    · rintro ⟨u, v, huv, hu, hv, hu', hv'⟩
      exact ⟨τ u, τ v, (hadj u hu v hv).mp huv, him ▸ ⟨u, hu, rfl⟩, him ▸ ⟨v, hv, rfl⟩, hu', hv'⟩
    · rintro ⟨u, v, huv, hu, hv, hu', hv'⟩
      rw [← him] at hu hv
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      exact ⟨a, b, (hadj a ha b hb).mpr huv, ha, hb, hu', hv'⟩

end

theorem mem_xs {S : Finset Cp} {c : Cp} {k : Fin 5} : cv c k ∈ XS S ↔ c ∈ S := by
  constructor
  · intro h; exact h c k rfl
  · intro h d m e
    cases e
    exact h

theorem inl_xs (S : Finset Cp) (a : Fin 11) : (Sum.inl a : V0) ∈ XS S := by
  intro c k e; cases e

theorem cv_inj {c d : Cp} {k m : Fin 5} : cv c k = cv d m ↔ c = d ∧ k = m := by
  unfold cv
  rw [Sum.inr.injEq, Prod.mk.injEq]

theorem e0_z0 {c : Cp} {u : V0} : E0 (cv c 0) u ↔ u = cv c 3 ∨ u = cv c 4 := by
  rcases u with a | ⟨d, m⟩
  · simp [E0, PL, cv]
  · simp only [E0, PL, cv, Sum.inr.injEq, Prod.mk.injEq]
    fin_cases m <;> simp [eq_comm]

theorem e0_z1 {c : Cp} {u : V0} : E0 (cv c 1) u ↔ u = cv c 3 := by
  rcases u with a | ⟨d, m⟩
  · simp [E0, PL, cv]
  · simp only [E0, PL, cv, Sum.inr.injEq, Prod.mk.injEq]
    fin_cases m <;> simp [eq_comm]

theorem e0_z2 {c : Cp} {u : V0} : E0 (cv c 2) u ↔ u = cv c 4 := by
  rcases u with a | ⟨d, m⟩
  · simp [E0, PL, cv]
  · simp only [E0, PL, cv, Sum.inr.injEq, Prod.mk.injEq]
    fin_cases m <;> simp [eq_comm]

theorem e0_core {c : Cp} {a : Fin 11} (k : Fin 5) (hk : k = 3 ∨ k = 4) :
    E0 (cv c k) (Sum.inl a) ↔ a ∈ Osum c.1 := by
  unfold E0 cv PL
  simp [hk]

theorem e0_core_core {a b : Fin 11} : ¬ E0 (Sum.inl a) (Sum.inl b) := by
  simp [E0, PL]

theorem osum_ne (l : Fin 14) : ∃ a, a ∈ Osum l := by
  fin_cases l <;> simp [Osum]

theorem gr_E0 : Gr E0 := by
  refine ⟨fun u v h => h.symm, fun u h => ?_⟩
  rcases u with a | ⟨c, k⟩
  · exact e0_core_core h
  · simp only [E0, PL, or_self] at h
    fin_cases k <;> simp at h

theorem xs_erase (S : Finset Cp) (c : Cp) :
    XS S \ ↑({cv c 0, cv c 1, cv c 2, cv c 3, cv c 4} : Finset V0) = XS (S.erase c) := by
  ext v
  rcases v with a | ⟨d, m⟩
  · refine ⟨fun _ => inl_xs _ a, fun _ => ⟨inl_xs _ a, ?_⟩⟩
    simp [cv]
  · change (cv d m ∈ XS S \ _) ↔ cv d m ∈ _
    rw [mem_xs, Finset.mem_erase, Set.mem_sdiff, mem_xs]
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, cv_inj]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun e => h2 ?_, h1⟩
      fin_cases m <;> simp [e]
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by tauto⟩

theorem gad_xs {S : Finset Cp} {c : Cp} (hc : c ∈ S) :
    Gad E0 (XS S) (cv c 0) (cv c 1) (cv c 2) (cv c 3) (cv c 4) := by
  obtain ⟨a, ha⟩ := osum_ne c.1
  refine ⟨⟨mem_xs.mpr hc, mem_xs.mpr hc, gr_E0.1 _ _ (e0_z1.mpr rfl), fun u _ h => e0_z1.mp h⟩,
    ⟨mem_xs.mpr hc, mem_xs.mpr hc, gr_E0.1 _ _ (e0_z2.mpr rfl), fun u _ h => e0_z2.mp h⟩,
    mem_xs.mpr hc, e0_z0.mpr (Or.inl rfl), e0_z0.mpr (Or.inr rfl), fun u _ h => e0_z0.mp h, ?_, ?_,
    Sum.inl a, inl_xs _ a, ?_, (e0_core 3 (Or.inl rfl)).mpr ha, (e0_core 4 (Or.inr rfl)).mpr ha⟩
  · simp [cv_inj]
  · simp [E0, PL, cv]
  · simp [cv]

theorem hasEdge_xs {S : Finset Cp} {d : Cp} (hd : d ∈ S) {Q : Set V0}
    (hQ : ∀ k, cv d k ∉ Q) : HasEdge E0 (XS S \ Q) :=
  ⟨cv d 1, ⟨mem_xs.mpr hd, hQ 1⟩, cv d 3, ⟨mem_xs.mpr hd, hQ 3⟩, e0_z1.mpr rfl⟩

theorem good_xs (H : HypH) {S : Finset Cp} (hS : S.Nonempty) :
    ∃ C : Ckt V0, Good E0 (XS S) ∅ C := by
  have hbox : S ⊆ box (S.sup (fun c => c.2) + 1) := by
    intro c hc
    have := Finset.le_sup (f := fun c : Cp => c.2) hc
    simp only [box, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
    exact Nat.lt_succ_of_le this
  obtain ⟨C, hC, _⟩ := H (S.sup (fun c => c.2) + 1) (by omega)
  set T := S.sup (fun c => c.2) + 1
  obtain ⟨c, hc⟩ := hS
  have hP : XS (box T) \ ↑(((box T \ S) ×ˢ (Finset.univ : Finset (Fin 5))).image
      (fun p => cv p.1 p.2)) = XS S := by
    ext v
    rcases v with a | ⟨d, m⟩
    · refine ⟨fun _ => inl_xs _ a, fun _ => ⟨inl_xs _ a, ?_⟩⟩
      simp [cv]
    · change (cv d m ∈ XS (box T) \ _) ↔ cv d m ∈ _
      rw [mem_xs, Set.mem_sdiff, mem_xs]
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
        Finset.mem_sdiff, Finset.mem_univ, and_true, cv_inj, Prod.exists]
      constructor
      · rintro ⟨h1, h2⟩
        by_contra h3
        exact h2 ⟨d.1, d.2, m, ⟨h1, h3⟩, rfl, rfl⟩
      · intro h
        refine ⟨hbox h, ?_⟩
        rintro ⟨d1, d2, m', ⟨_, h2⟩, e, _⟩
        rw [e] at h2
        exact h2 h
  obtain ⟨C', h'⟩ := good_diff hC (((box T \ S) ×ˢ (Finset.univ : Finset (Fin 5))).image
      (fun p => cv p.1 p.2)) (by
    rw [hP]
    exact ⟨cv c 1, mem_xs.mpr hc, cv c 3, mem_xs.mpr hc, e0_z1.mpr rfl⟩)
  rw [hP] at h'
  exact ⟨C', h'⟩

theorem cv_notin {c d : Cp} (hne : d ≠ c) {Q : Finset V0} (hQ : ∀ q ∈ Q, ∃ k, q = cv c k)
    (k : Fin 5) : cv d k ∉ (↑Q : Set V0) := by
  intro h
  obtain ⟨m, e⟩ := hQ _ h
  exact hne (cv_inj.mp e).1

theorem step (H : HypH) {S : Finset Cp} {c d : Cp} (hc : c ∈ S) (hd : d ∈ S) (hdc : d ≠ c)
    (Q : Finset V0) (hQ : ∀ q ∈ Q, ∃ k, q = cv c k) (ky kz : Fin 5) (hky : ky = 3 ∨ ky = 4)
    (hyQ : cv c ky ∉ Q) (hzQ : cv c kz ∉ Q) (hE : E0 (cv c ky) (cv c kz))
    (hp : ∀ u, u ∉ Q → E0 (cv c kz) u → u = cv c ky) :
    sz E0 (XS S \ ↑(Q ∪ {cv c ky, cv c kz})) + 3 ≤ sz E0 (XS S \ ↑Q) := by
  obtain ⟨a, ha⟩ := osum_ne c.1
  obtain ⟨C, hC⟩ := good_xs H ⟨c, hc⟩
  have hset : XS S \ ↑(Q ∪ {cv c ky, cv c kz}) = (XS S \ ↑Q) \ ({cv c ky, cv c kz} : Set V0) := by
    ext v
    simp only [Set.mem_sdiff, Finset.coe_union, Set.mem_union, Finset.coe_insert,
      Finset.coe_singleton]
    tauto
  rw [hset]
  refine sz_pair gr_E0 (good_diff hC Q (hasEdge_xs hd (cv_notin hdc hQ)))
    (x := Sum.inl a) ⟨⟨mem_xs.mpr hc, hyQ⟩, ⟨mem_xs.mpr hc, hzQ⟩, hE, fun u hu h => hp u hu.2 h⟩
    ⟨inl_xs _ a, ?_⟩ ?_ ((e0_core ky hky).mpr ha) ?_
  · intro h
    obtain ⟨m, e⟩ := hQ _ h
    simp [cv] at e
  · simp [cv]
  · rw [← hset]
    refine hasEdge_xs hd (cv_notin hdc ?_)
    intro q hq
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with h | h | h
    · exact hQ q h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩

theorem other_copy {S : Finset Cp} {c : Cp} (hS : (S.erase c).Nonempty) : ∃ d ∈ S, d ≠ c := by
  obtain ⟨d, hd⟩ := hS
  rw [Finset.mem_erase] at hd
  exact ⟨d, hd.2, hd.1⟩

theorem sz_rest0 (H : HypH) {S : Finset Cp} {c : Cp} (hc : c ∈ S) (hS : (S.erase c).Nonempty) :
    sz E0 (XS (S.erase c)) + 6 ≤ sz E0 (XS S \ ↑({cv c 0} : Finset V0)) := by
  obtain ⟨d, hd, hdc⟩ := other_copy hS
  have h1 := step H hc hd hdc {cv c 0} (by simp) 3 1 (by simp) (by simp [cv_inj])
    (by simp [cv_inj]) (gr_E0.1 _ _ (e0_z1.mpr rfl)) (fun u _ h => e0_z1.mp h)
  have h2 := step H hc hd hdc ({cv c 0} ∪ {cv c 3, cv c 1}) (by simp) 4 2 (by simp)
    (by simp [cv_inj]) (by simp [cv_inj]) (gr_E0.1 _ _ (e0_z2.mpr rfl)) (fun u _ h => e0_z2.mp h)
  have e : (({cv c 0} ∪ {cv c 3, cv c 1}) ∪ {cv c 4, cv c 2} : Finset V0) =
      {cv c 0, cv c 1, cv c 2, cv c 3, cv c 4} := by
    ext v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [e, xs_erase] at h2
  omega

theorem sz_rest1 (H : HypH) {S : Finset Cp} {c : Cp} (hc : c ∈ S) (hS : (S.erase c).Nonempty) :
    sz E0 (XS (S.erase c)) + 3 ≤ sz E0 (XS S \ ↑({cv c 1, cv c 2, cv c 4} : Finset V0)) := by
  obtain ⟨d, hd, hdc⟩ := other_copy hS
  have h1 := step H hc hd hdc {cv c 1, cv c 2, cv c 4} (by simp) 3 0 (by simp) (by simp [cv_inj])
    (by simp [cv_inj]) (gr_E0.1 _ _ (e0_z0.mpr (Or.inl rfl))) (fun u hu h => by
      rcases e0_z0.mp h with e | e
      · exact e
      · exact absurd (by rw [e]; simp) hu)
  have e : ({cv c 1, cv c 2, cv c 4} ∪ {cv c 3, cv c 0} : Finset V0) =
      {cv c 0, cv c 1, cv c 2, cv c 3, cv c 4} := by
    ext v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [e, xs_erase] at h1
  exact h1

theorem sz_rest2 (H : HypH) {S : Finset Cp} {c : Cp} (hc : c ∈ S) (hS : (S.erase c).Nonempty) :
    sz E0 (XS (S.erase c)) + 3 ≤ sz E0 (XS S \ ↑({cv c 1, cv c 2, cv c 3} : Finset V0)) := by
  obtain ⟨d, hd, hdc⟩ := other_copy hS
  have h1 := step H hc hd hdc {cv c 1, cv c 2, cv c 3} (by simp) 4 0 (by simp) (by simp [cv_inj])
    (by simp [cv_inj]) (gr_E0.1 _ _ (e0_z0.mpr (Or.inr rfl))) (fun u hu h => by
      rcases e0_z0.mp h with e | e
      · exact absurd (by rw [e]; simp) hu
      · exact e)
  have e : ({cv c 1, cv c 2, cv c 3} ∪ {cv c 4, cv c 0} : Finset V0) =
      {cv c 0, cv c 1, cv c 2, cv c 3, cv c 4} := by
    ext v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [e, xs_erase] at h1
  exact h1

theorem sz_copy (H : HypH) {S : Finset Cp} {c : Cp} (hc : c ∈ S) (hS : (S.erase c).Nonempty) :
    sz E0 (XS (S.erase c)) + 7 ≤ sz E0 (XS S) := by
  obtain ⟨d, hd, hdc⟩ := other_copy hS
  have h0 := sz_rest0 H hc hS
  have hs : (↑({cv c 0} : Finset V0) : Set V0) = {cv c 0} := by simp
  rw [hs] at h0
  have h1 := sz_one gr_E0 (good_xs H ⟨c, hc⟩) (v := cv c 0) (u := cv c 3) (mem_xs.mpr hc)
    (mem_xs.mpr hc) (e0_z0.mpr (Or.inl rfl)) (hasEdge_xs hd (by simp [cv_inj, hdc]))
  omega

theorem sz_chain (H : HypH) {S : Finset Cp} (hS : S.Nonempty) : ∀ (n : ℕ) (S2 : Finset Cp),
    S ⊆ S2 → S2.card = n → sz E0 (XS S) + 7 * S2.card ≤ sz E0 (XS S2) + 7 * S.card := by
  intro n
  induction n with
  | zero =>
    intro S2 h h0
    have : S2 = ∅ := Finset.card_eq_zero.mp h0
    subst this
    obtain ⟨c, hc⟩ := hS
    exact absurd (h hc) (Finset.notMem_empty c)
  | succ n ih =>
    intro S2 h hn
    by_cases he : S = S2
    · rw [he]
    · obtain ⟨c, hc, hcS⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨h, he⟩)
      have hsub : S ⊆ S2.erase c := fun x hx =>
        Finset.mem_erase.mpr ⟨fun e => hcS (e ▸ hx), h hx⟩
      have h1 := sz_copy H hc (hS.mono hsub)
      have hcard := Finset.card_erase_add_one hc
      have h2 := ih (S2.erase c) hsub (by omega)
      omega

theorem sz_upper (H : HypH) {S : Finset Cp} (hS : S.Nonempty) :
    sz E0 (XS S) ≤ 7 * S.card + 16 := by
  have hbox : S ⊆ box (S.sup (fun c => c.2) + 1) := by
    intro c hc
    have := Finset.le_sup (f := fun c : Cp => c.2) hc
    simp only [box, Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
    exact Nat.lt_succ_of_le this
  obtain ⟨C, hC, hcard⟩ := H (S.sup (fun c => c.2) + 1) (by omega)
  have h1 := sz_chain H hS _ _ hbox rfl
  have h2 := sz_le hC
  have h3 : (box (S.sup (fun c => c.2) + 1)).card = 14 * (S.sup (fun c => c.2) + 1) := by
    simp [box]
  omega

theorem loc_xs (H : HypH) {S : Finset Cp} {c : Cp} (hc : c ∈ S) (hS : (S.erase c).Nonempty)
    (ht : sz E0 (XS S) = sz E0 (XS (S.erase c)) + 7) {C : Ckt V0} (hC : Opt E0 (XS S) ∅ C)
    (hN : Nmd E0 (XS S) C) :
    Loc E0 (XS S) C (cv c 0) (cv c 1) (cv c 2) (cv c 3) (cv c 4) := by
  obtain ⟨d, hd, hdc⟩ := other_copy hS
  have he : ∀ Q : Finset V0, (∀ q ∈ Q, ∃ k, q = cv c k) → HasEdge E0 (XS S \ ↑Q) := fun Q hQ =>
    hasEdge_xs hd (cv_notin hdc hQ)
  have k0 := kl_le hC {cv c 0} (he _ (by simp))
  have k1 := kl_le hC {cv c 1, cv c 2, cv c 4} (he _ (by simp))
  have k2 := kl_le hC {cv c 1, cv c 2, cv c 3} (he _ (by simp))
  have k3 := kl_le hC {cv c 0, cv c 1, cv c 2, cv c 3, cv c 4} (he _ (by simp))
  rw [xs_erase] at k3
  have r0 := sz_rest0 H hc hS
  have r1 := sz_rest1 H hc hS
  have r2 := sz_rest2 H hc hS
  refine ⟨gr_E0, hC, hN, gad_xs hc, ?_, by omega, by omega, by omega, by omega⟩
  exact out_live hC.1.2.2.1 (he _ (by simp))

theorem sz_sym (H : HypH) {S S2 : Finset Cp} (hS : S.Nonempty) (h : ∀ l, cnt S l = cnt S2 l) :
    sz E0 (XS S2) ≤ sz E0 (XS S) := by
  have hbij : ∀ l : Fin 14, ∃ g : Cp → Cp, (∀ c ∈ S, c.1 = l → g c ∈ S2 ∧ (g c).1 = l) ∧
      (∀ c ∈ S, c.1 = l → ∀ d ∈ S, d.1 = l → g c = g d → c = d) ∧
      ∀ e ∈ S2, e.1 = l → ∃ c ∈ S, c.1 = l ∧ g c = e := by
    intro l
    have e := Finset.equivOfCardEq (h l)
    refine ⟨fun c => if hc : c ∈ S.filter (fun c => c.1 = l) then (e ⟨c, hc⟩).1 else c, ?_, ?_, ?_⟩
    · intro c hc hl
      have hm : c ∈ S.filter (fun c => c.1 = l) := Finset.mem_filter.mpr ⟨hc, hl⟩
      simp only [dif_pos hm]
      exact Finset.mem_filter.mp (e ⟨c, hm⟩).2
    · intro c hc hl d hd hld heq
      have hm : c ∈ S.filter (fun c => c.1 = l) := Finset.mem_filter.mpr ⟨hc, hl⟩
      have hm' : d ∈ S.filter (fun c => c.1 = l) := Finset.mem_filter.mpr ⟨hd, hld⟩
      simp only [dif_pos hm, dif_pos hm'] at heq
      exact congrArg Subtype.val (e.injective (Subtype.ext heq))
    · intro f hf hl
      have hm : f ∈ S2.filter (fun c => c.1 = l) := Finset.mem_filter.mpr ⟨hf, hl⟩
      obtain ⟨hs, hl'⟩ := Finset.mem_filter.mp (e.symm ⟨f, hm⟩).2
      refine ⟨(e.symm ⟨f, hm⟩).1, hs, hl', ?_⟩
      simp only [dif_pos (e.symm ⟨f, hm⟩).2]
      simp
  choose g g1 g2 g3 using hbij
  let f : Cp → Cp := fun c => g c.1 c
  have f1 : ∀ c ∈ S, f c ∈ S2 ∧ (f c).1 = c.1 := fun c hc => g1 c.1 c hc rfl
  have f2 : ∀ c ∈ S, ∀ d ∈ S, f c = f d → c = d := by
    intro c hc d hd he
    have : c.1 = d.1 := by rw [← (f1 c hc).2, ← (f1 d hd).2, he]
    refine g2 c.1 c hc rfl d hd this.symm ?_
    change g c.1 c = g d.1 d at he
    rw [this] at he ⊢
    exact he
  have f3 : ∀ e ∈ S2, ∃ c ∈ S, f c = e := by
    intro e he
    obtain ⟨c, hc, hl, hgc⟩ := g3 e.1 e he rfl
    refine ⟨c, hc, ?_⟩
    change g c.1 c = e
    rw [hl]; exact hgc
  obtain ⟨C, hC⟩ := opt_exists (good_xs H hS)
  obtain ⟨c0, hc0⟩ := hS
  have hEdge : HasEdge E0 (XS S) :=
    ⟨cv c0 1, mem_xs.mpr hc0, cv c0 3, mem_xs.mpr hc0, e0_z1.mpr rfl⟩
  have hadjPL : ∀ u ∈ XS S, ∀ v ∈ XS S, (PL u v ↔
      PL (Sum.map id (fun p : Cp × Fin 5 => (f p.1, p.2)) u)
        (Sum.map id (fun p : Cp × Fin 5 => (f p.1, p.2)) v)) := by
    rintro (a | ⟨c, k⟩) hu (b | ⟨d, m⟩) hv
    · exact Iff.rfl
    · have hd : d ∈ S := mem_xs.mp hv
      show (_ ∧ _) ↔ (_ ∧ _)
      rw [(f1 d hd).2]
      exact Iff.rfl
    · exact Iff.rfl
    · have hc : c ∈ S := mem_xs.mp hu
      have hd : d ∈ S := mem_xs.mp hv
      show (_ ∧ _) ↔ (_ ∧ _)
      refine and_congr_left fun _ => ⟨fun e => congrArg f e, fun e => f2 c hc d hd e⟩
  have hinj : Set.InjOn (Sum.map id (fun p : Cp × Fin 5 => (f p.1, p.2)) : V0 → V0) (XS S) := by
    rintro (a | ⟨c, k⟩) hu (b | ⟨d, m⟩) hv he
    · exact congrArg Sum.inl (Sum.inl.inj he)
    · cases he
    · cases he
    · simp only [Sum.map_inr, Sum.inr.injEq, Prod.mk.injEq] at he
      have := f2 c (mem_xs.mp hu) d (mem_xs.mp hv) he.1
      rw [this, he.2]
  have him : (Sum.map id (fun p : Cp × Fin 5 => (f p.1, p.2)) : V0 → V0) '' XS S = XS S2 := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      rcases u with a | ⟨c, k⟩
      · exact inl_xs S2 a
      · exact mem_xs.mpr (f1 c (mem_xs.mp hu)).1
    · intro hv
      rcases v with a | ⟨d, m⟩
      · exact ⟨Sum.inl a, inl_xs S a, rfl⟩
      · obtain ⟨c, hc, rfl⟩ := f3 d (mem_xs.mp hv)
        exact ⟨cv c m, mem_xs.mpr hc, rfl⟩
  obtain ⟨C2, h2, hcard⟩ := relabel gr_E0 hEdge hC
    (Sum.map id (fun p : Cp × Fin 5 => (f p.1, p.2))) hinj him
    (fun u hu v hv => or_congr (hadjPL u hu v hv) (hadjPL v hv u hu))
  rw [← opt_sz hC, ← hcard]
  exact sz_le h2

theorem stab (H : HypH) : ∃ t a : ℕ, 1 ≤ t ∧
    ∀ S : Finset Cp, rich t S → sz E0 (XS S) + a = 7 * S.card + 16 := by
  have hne : ∃ a, ∃ S : Finset Cp, S.Nonempty ∧ sz E0 (XS S) + a = 7 * S.card + 16 := by
    have hS : ({((0 : Fin 14), 0)} : Finset Cp).Nonempty := ⟨_, Finset.mem_singleton_self _⟩
    have := sz_upper H hS
    exact ⟨7 * ({((0 : Fin 14), 0)} : Finset Cp).card + 16 -
      sz E0 (XS ({((0 : Fin 14), 0)} : Finset Cp)), _, hS, by omega⟩
  obtain ⟨S0, hS0, h0⟩ := Nat.find_spec hne
  have hmin := fun a h => Nat.find_min' hne (m := a) h
  set a := Nat.find hne
  refine ⟨Finset.univ.sup (cnt S0) + 1, a, by omega, fun S hr => ?_⟩
  have hsub : ∀ l : Fin 14, ∃ A ⊆ S.filter (fun c => c.1 = l), A.card = cnt S0 l := by
    intro l
    refine Finset.exists_subset_card_eq ?_
    have h1 := hr l
    have h2 := Finset.le_sup (f := cnt S0) (Finset.mem_univ l)
    unfold cnt at h1 h2 ⊢
    omega
  choose A hA1 hA2 using hsub
  let S1 : Finset Cp := Finset.univ.biUnion A
  have hS1 : S1 ⊆ S := by
    intro c hc
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hc
    exact (Finset.mem_filter.mp (hA1 l hl)).1
  have hcnt : ∀ l, cnt S0 l = cnt S1 l := by
    intro l
    rw [← hA2 l]
    unfold cnt
    congr 1
    ext c
    rw [Finset.mem_filter]
    constructor
    · intro hc
      exact ⟨Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, hc⟩, (Finset.mem_filter.mp (hA1 l hc)).2⟩
    · rintro ⟨hc, hl⟩
      obtain ⟨m, _, hm⟩ := Finset.mem_biUnion.mp hc
      have := (Finset.mem_filter.mp (hA1 m hm)).2
      rw [hl] at this
      exact this ▸ hm
  have hcard : ∀ S : Finset Cp, S.card = ∑ l : Fin 14, cnt S l := fun S =>
    Finset.card_eq_sum_card_fiberwise (f := fun c : Cp => c.1) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  have hcards : S1.card = S0.card := by
    rw [hcard S1, hcard S0]
    exact Finset.sum_congr rfl fun l _ => (hcnt l).symm
  have hS1n : S1.Nonempty := by
    rw [← Finset.card_pos, hcards]
    exact Finset.card_pos.mpr hS0
  have hSn : S.Nonempty := hS1n.mono hS1
  have e1 := sz_sym H hS0 hcnt
  have e2 := sz_sym H hS1n (fun l => (hcnt l).symm)
  have e3 := sz_chain H hS1n _ _ hS1 rfl
  have e4 := sz_upper H hSn
  have e5 := hmin (7 * S.card + 16 - sz E0 (XS S)) ⟨S, hSn, by omega⟩
  omega

theorem and_lower {S : Finset Cp} {C : Ckt V0} (hC : Good E0 (XS S) ∅ C) :
    2 * S.card ≤ nAnd C := by
  obtain ⟨hW, _, hcomp, _⟩ := hC
  have h := and_bound hW (S ×ˢ ({3, 4} : Finset (Fin 5))) (fun j => cv j.1 j.2)
    (fun j => cv j.1 (j.2 - 2)) ?_ ?_ ?_ ?_
  · rw [Finset.card_product] at h
    have : ({3, 4} : Finset (Fin 5)).card = 2 := by decide
    rw [this] at h
    omega
  · rintro ⟨c, k⟩ _ ⟨d, m⟩ _ e
    exact Prod.ext (cv_inj.mp e).1 (cv_inj.mp e).2
  · rintro ⟨c, k⟩ _ ⟨d, m⟩ _ e
    exact Prod.ext (cv_inj.mp e).1 (sub_left_injective (cv_inj.mp e).2)
  · rintro ⟨c, k⟩ hi ⟨d, m⟩ hj e
    have e2 := (cv_inj.mp e).2
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi.2 with h | h <;> rcases hj.2 with h' | h' <;>
      · simp only at h h' e2
        rw [h, h'] at e2
        revert e2; decide
  · intro ρ hρ
    rw [hcomp]
    have hform : ∀ u ∈ ρ, ∃ c ∈ S, ∃ k : Fin 5, u = cv c k ∧ (k = 3 ∨ k = 4 ∨ k = 1 ∨ k = 2) := by
      intro u hu
      obtain ⟨⟨c, k⟩, hj, e⟩ := hρ u hu
      simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hj
      obtain ⟨hc, hk⟩ := hj
      rcases hk with rfl | rfl <;> rcases e with e | e
      · exact ⟨c, hc, _, e, Or.inl rfl⟩
      · exact ⟨c, hc, _, e, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨c, hc, _, e, Or.inr (Or.inl rfl)⟩
      · exact ⟨c, hc, _, e, Or.inr (Or.inr (Or.inr rfl))⟩
    constructor
    · rintro ⟨u, v, huv, -, -, hu, hv⟩
      have key : ∀ u ∈ ρ, ∀ v ∈ ρ, PL u v → ∃ i ∈ S ×ˢ ({3, 4} : Finset (Fin 5)),
          cv i.1 i.2 ∈ ρ ∧ cv i.1 (i.2 - 2) ∈ ρ := by
        intro u hu v hv hpl
        obtain ⟨c, hc, k, rfl, hk⟩ := hform u hu
        obtain ⟨d, hd, m, rfl, hm⟩ := hform v hv
        obtain ⟨rfl, hpl⟩ := hpl
        rcases hpl with ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp at hk
        · exact ⟨(c, 3), by simp [hc], hv, hu⟩
        · exact ⟨(c, 4), by simp [hc], hv, hu⟩
      rcases huv with h | h
      · exact key u hu v hv h
      · exact key v hv u hu h
    · rintro ⟨⟨c, k⟩, hj, h1, h2⟩
      simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hj
      obtain ⟨hc, rfl | rfl⟩ := hj
      · exact ⟨cv c 1, cv c 3, e0_z1.mpr rfl, mem_xs.mpr hc, mem_xs.mpr hc, h2, h1⟩
      · exact ⟨cv c 2, cv c 4, e0_z2.mpr rfl, mem_xs.mpr hc, mem_xs.mpr hc, h2, h1⟩

theorem del_copy (H : HypH) {S : Finset Cp} {c : Cp} (hc : c ∈ S) (hS : (S.erase c).Nonempty)
    (ht : sz E0 (XS S) = sz E0 (XS (S.erase c)) + 7) {C : Ckt V0} (hC : Opt E0 (XS S) ∅ C)
    (hN : Nmd E0 (XS S) C) :
    ∃ C' : Ckt V0, Opt E0 (XS (S.erase c)) ∅ C' ∧ Nmd E0 (XS (S.erase c)) C' ∧
      nAnd C' + ((if fo C (Sum.inl (cv c 3)) = 1 then 1 else 0) +
        (if fo C (Sum.inl (cv c 4)) = 1 then 1 else 0)) = nAnd C := by
  have hL := loc_xs H hc hS ht hC hN
  have hf := loc_final hL
  obtain ⟨C1, g1, g2, g3⟩ := zero hC.1 _ hL.2.2.2.2.1
  rw [xs_erase] at g1
  have hO : Opt E0 (XS (S.erase c)) ∅ C1 := by
    refine opt_of_sz g1 ?_
    have := opt_sz hC
    rw [g2]
    omega
  obtain ⟨C2, o2, n2, a2⟩ := normalize gr_E0 hO
  refine ⟨C2, o2, n2, ?_⟩
  rw [a2, ← hf.2]
  unfold nAnd
  rw [g2, g3]

theorem noc (H : HypH) (T : ℕ) : ∃ S : Finset Cp, rich T S ∧ S.Nonempty ∧
    ∃ C : Ckt V0, Opt E0 (XS S) ∅ C ∧ C.G.card ≤ 7 * S.card + 16 ∧
      ∀ c ∈ S, ∀ k : Fin 5, (k = 3 ∨ k = 4) → fo C (Sum.inl (cv c k)) ≤ 1 ∧
        ∀ g, Rd C g (Sum.inl (cv c k)) → C.op g = true := by
  obtain ⟨t, a, ht, hstab⟩ := stab H
  have hcnt : ∀ (S : Finset Cp) (c : Cp), ∀ l, cnt S l ≤ cnt (S.erase c) l + 1 := by
    intro S c l
    unfold cnt
    rw [Finset.filter_erase]
    have := Finset.pred_card_le_card_erase (s := S.filter (fun c => c.1 = l)) (a := c)
    omega
  have hcnt' : ∀ (S : Finset Cp) (c : Cp), ∀ l, l ≠ c.1 → cnt S l = cnt (S.erase c) l := by
    intro S c l hl
    unfold cnt
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
    intro h
    exact hl (Finset.mem_filter.mp h).2.symm
  have hcard : ∀ S : Finset Cp, S.card = ∑ l : Fin 14, cnt S l := fun S =>
    Finset.card_eq_sum_card_fiberwise (f := fun c : Cp => c.1) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
  have hne : ∀ S : Finset Cp, rich t S → S.Nonempty := by
    intro S hr
    have := hr 0
    unfold cnt at this
    obtain ⟨c, hc⟩ := Finset.card_pos.mp (lt_of_lt_of_le ht this)
    exact ⟨c, (Finset.mem_filter.mp hc).1⟩
  have hfew : ∀ n (S : Finset Cp), S.card = n → rich t S → ∀ C : Ckt V0, Opt E0 (XS S) ∅ C →
      Nmd E0 (XS S) C → nAnd C ≤ 2 * S.card + (70 * t + 16) := by
    intro n
    induction n with
    | zero =>
      intro S h0 hr C _ _
      have := hne S hr
      rw [Finset.card_eq_zero.mp h0] at this
      exact absurd this (by simp)
    | succ n ih =>
      intro S hn hr C hC hN
      by_cases hall : ∀ l, cnt S l = t
      · have h1 : S.card = 14 * t := by
          rw [hcard S, Finset.sum_congr rfl (fun l _ => hall l)]
          simp
        have h2 : nAnd C ≤ C.G.card := Finset.card_filter_le _ _
        have h3 := opt_sz hC
        have h4 := sz_upper H (hne S hr)
        omega
      · push Not at hall
        obtain ⟨l, hl⟩ := hall
        have hlt : t < cnt S l := lt_of_le_of_ne (hr l) hl.symm
        obtain ⟨c, hc⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le t) hlt)
        obtain ⟨hcS, hcl⟩ := Finset.mem_filter.mp hc
        have hr' : rich t (S.erase c) := by
          intro m
          by_cases hm : m = c.1
          · have := hcnt S c m
            rw [hm, hcl] at this ⊢
            omega
          · rw [← hcnt' S c m hm]; exact hr m
        have e1 := hstab S hr
        have e2 := hstab _ hr'
        have e3 := Finset.card_erase_add_one hcS
        obtain ⟨C', o, nm, hA⟩ := del_copy H hcS (hne _ hr') (by omega) hC hN
        have := ih (S.erase c) (by omega) hr' C' o nm
        split_ifs at hA <;> omega
  have hdel : ∀ n (S : Finset Cp) (C : Ckt V0), rich (t + 1 + T + n) S → Opt E0 (XS S) ∅ C →
      Nmd E0 (XS S) C → 2 * S.card + (70 * t + 16) ≤ nAnd C + n →
      ∃ S : Finset Cp, rich (t + 1 + T) S ∧ ∃ C : Ckt V0, Opt E0 (XS S) ∅ C ∧ Nmd E0 (XS S) C ∧
        ∀ c ∈ S, fo C (Sum.inl (cv c 3)) = 1 ∧ fo C (Sum.inl (cv c 4)) = 1 := by
    intro n
    induction n with
    | zero =>
      intro S C hr hC hN hA
      refine ⟨S, hr, C, hC, hN, fun c hc => ?_⟩
      by_contra hbad
      have hr0 : rich t S := fun l => le_trans (by omega) (hr l)
      have hT : rich t (S.erase c) := by
        intro l
        have h1 := hcnt S c l
        have h2 := hr l
        omega
      have e1 := hstab S hr0
      have e2 := hstab _ hT
      have e3 := Finset.card_erase_add_one hc
      obtain ⟨C', o, nm, hA'⟩ := del_copy H hc (hne _ hT) (by omega) hC hN
      have h1 := hfew _ _ rfl hT C' o nm
      have h2 := hfew _ _ rfl hr0 C hC hN
      split_ifs at hA' <;> first | omega | exact hbad ⟨‹_›, ‹_›⟩
    | succ n ih =>
      intro S C hr hC hN hA
      by_cases hall : ∀ c ∈ S, fo C (Sum.inl (cv c 3)) = 1 ∧ fo C (Sum.inl (cv c 4)) = 1
      · exact ⟨S, fun l => le_trans (by omega) (hr l), C, hC, hN, hall⟩
      · push Not at hall
        obtain ⟨c, hc, hbad⟩ := hall
        have hr' : rich (t + 1 + T + n) (S.erase c) := by
          intro l
          have h1 := hcnt S c l
          have h2 := hr l
          omega
        have hr0 : rich t S := fun l => le_trans (by omega) (hr l)
        have hT : rich t (S.erase c) := fun l => le_trans (by omega) (hr' l)
        have e1 := hstab S hr0
        have e2 := hstab _ hT
        have e3 := Finset.card_erase_add_one hc
        obtain ⟨C', o, nm, hA'⟩ := del_copy H hc (hne _ hT) (by omega) hC hN
        refine ih (S.erase c) C' hr' o nm ?_
        split_ifs at hA' <;> first | omega | exact absurd ‹_› (hbad ‹_›)
  have hboxr : ∀ m, rich m (box m) := by
    intro m l
    unfold cnt
    have hsub : (Finset.range m).image (fun i => ((l, i) : Cp)) ⊆
        (box m).filter (fun c => c.1 = l) := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
      simp only [box, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true]
      exact hi
    have := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).2),
      Finset.card_range] at this
  have hr := hboxr (t + 1 + T + (70 * t + 16))
  have hr0 : rich t (box (t + 1 + T + (70 * t + 16))) := fun l => le_trans (by omega) (hr l)
  obtain ⟨C0, hC0⟩ := opt_exists (good_xs H (hne _ hr0))
  obtain ⟨C, hC, hN, _⟩ := normalize gr_E0 hC0
  have hlow := and_lower hC.1
  obtain ⟨S, hS, D, hD, hDN, hall⟩ := hdel (70 * t + 16) _ C hr hC hN (by omega)
  have hSt : rich t S := fun l => le_trans (by omega) (hS l)
  refine ⟨S, fun l => le_trans (by omega) (hS l), hne _ hSt, D, hD, ?_, ?_⟩
  · rw [opt_sz hD]
    exact sz_upper H (hne _ hSt)
  · intro c hc k hk
    have hfo : fo D (Sum.inl (cv c k)) = 1 := by
      rcases hk with rfl | rfl
      · exact (hall c hc).1
      · exact (hall c hc).2
    refine ⟨hfo.le, fun g hg => ?_⟩
    by_contra ho
    have hgad := gad_xs hc
    have : 2 ≤ fo D (Sum.inl (cv c k)) := by
      rcases hk with rfl | rfl
      · exact hDN _ _ hgad.1 g hg (by simpa using ho)
      · exact hDN _ _ hgad.2.1 g hg (by simpa using ho)
    omega

theorem drop_z (H : HypH) (T : ℕ) : ∃ S : Finset Cp, rich T S ∧ ∃ C : Ckt V0,
    H6 C (S ×ˢ ({3, 4} : Finset (Fin 5))) (fun j => cv j.1 j.2) (fun j => cv j.1 (j.2 - 2))
      (fun j => {x | ∃ a ∈ Osum j.1.1, x = Sum.inl a}) := by
  obtain ⟨S, hr, hS, C, hC, hcard, hy⟩ := noc H T
  refine ⟨S, hr, ?_⟩
  let Z : Finset V0 := S.image (fun c => cv c 0)
  let Y : Set V0 := {v | ∃ c ∈ S, ∃ k : Fin 5, (k = 3 ∨ k = 4) ∧ v = cv c k}
  have hZcard : Z.card = S.card :=
    Finset.card_image_of_injective _ (fun a b h => (cv_inj.mp h).1)
  have hmX : ∀ v, v ∈ XS S \ (↑Z : Set V0) ↔ (∃ a, v = Sum.inl a) ∨
      ∃ c ∈ S, ∃ k : Fin 5, k ≠ 0 ∧ v = cv c k := by
    intro v
    rcases v with a | ⟨d, m⟩
    · refine ⟨fun _ => Or.inl ⟨a, rfl⟩, fun _ => ⟨inl_xs _ a, ?_⟩⟩
      simp [Z, cv]
    · change (cv d m ∈ XS S \ _) ↔ _
      rw [Set.mem_sdiff, mem_xs]
      constructor
      · rintro ⟨h1, h2⟩
        refine Or.inr ⟨d, h1, m, ?_, rfl⟩
        rintro rfl
        exact h2 (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨d, h1, rfl⟩))
      · rintro (⟨a, e⟩ | ⟨c, hc, k, hk, e⟩)
        · cases e
        · obtain ⟨rfl, rfl⟩ := cv_inj.mp e
          refine ⟨hc, fun h => ?_⟩
          obtain ⟨c', _, e'⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h)
          exact hk (cv_inj.mp e').2.symm
  obtain ⟨c0, hc0⟩ := hS
  have hEdge : HasEdge E0 (XS S \ (↑Z : Set V0)) :=
    ⟨cv c0 1, (hmX _).mpr (Or.inr ⟨c0, hc0, 1, by decide, rfl⟩), cv c0 3,
      (hmX _).mpr (Or.inr ⟨c0, hc0, 3, by decide, rfl⟩), e0_z1.mpr rfl⟩
  have hgood : Good E0 (XS S) Y C := by
    refine ⟨hC.1.1, hC.1.2.1, hC.1.2.2.1, ?_⟩
    rintro y ⟨c, hc, k, hk, rfl⟩
    exact hy c hc k hk
  have hlive := out_live hC.1.2.2.1 hEdge
  obtain ⟨C1, g1, g2, -⟩ := zero hgood Z hlive
  have hkl := count_live (opt_useful hC) (P := Z) (by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    exact read_pos gr_E0 hC.1 (mem_xs.mpr hc) (u := cv c 3) (mem_xs.mpr hc)
      (e0_z0.mpr (Or.inl rfl))) hlive
  have hpart := count_part C Z
  unfold kl at hpart
  obtain ⟨D, hD⟩ := opt_exists ⟨C1, g1⟩
  have hDle := hD.2 C1 g1
  rw [g2] at hDle
  have hDcard : D.G.card ≤ 6 * S.card + 16 := by omega
  have hcomp := hD.1.2.2.1
  refine ⟨D, ?_⟩
  set X' : Set V0 := XS S \ (↑Z : Set V0) with hX'
  have hJ : ∀ j : Cp × Fin 5, j ∈ S ×ˢ ({3, 4} : Finset (Fin 5)) ↔ j.1 ∈ S ∧ (j.2 = 3 ∨ j.2 = 4) := by
    intro j
    simp [Finset.mem_product]
  have hedge : ∀ u v, E0 u v → u ∈ X' → v ∈ X' →
      (∃ c ∈ S, ∃ k : Fin 5, (k = 3 ∨ k = 4) ∧ ((u = cv c k ∧ (v = cv c (k - 2) ∨
        ∃ a ∈ Osum c.1, v = Sum.inl a)) ∨ (v = cv c k ∧ (u = cv c (k - 2) ∨
        ∃ a ∈ Osum c.1, u = Sum.inl a)))) := by
    have key : ∀ u v, PL u v → u ∈ X' → v ∈ X' → ∃ c ∈ S, ∃ k : Fin 5, (k = 3 ∨ k = 4) ∧
        (v = cv c k ∧ (u = cv c (k - 2) ∨ ∃ a ∈ Osum c.1, u = Sum.inl a)) := by
      intro u v h hu hv
      rcases (hmX v).mp hv with ⟨b, rfl⟩ | ⟨d, hd, m, hm, rfl⟩
      · rcases u with a | ⟨c, k⟩ <;> exact absurd h (by simp [PL])
      rcases (hmX u).mp hu with ⟨a, rfl⟩ | ⟨c, hc, k, hk, rfl⟩
      · exact ⟨d, hd, m, h.1, rfl, Or.inr ⟨a, h.2, rfl⟩⟩
      · obtain ⟨rfl, h⟩ := h
        rcases h with ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd rfl hk
        · exact ⟨c, hc, 3, Or.inl rfl, rfl, Or.inl rfl⟩
        · exact ⟨c, hc, 4, Or.inr rfl, rfl, Or.inl rfl⟩
    rintro u v (h | h) hu hv
    · obtain ⟨c, hc, k, hk, h⟩ := key u v h hu hv
      exact ⟨c, hc, k, hk, Or.inr h⟩
    · obtain ⟨c, hc, k, hk, h⟩ := key v u h hv hu
      exact ⟨c, hc, k, hk, Or.inl h⟩
  have hPP : ∀ c ∈ S, ∀ k : Fin 5, (k = 3 ∨ k = 4) →
      cv c k ∈ PP (S ×ˢ ({3, 4} : Finset (Fin 5))) (fun j => cv j.1 j.2)
        (fun j => cv j.1 (j.2 - 2)) := by
    intro c hc k hk
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(c, k), (hJ _).mpr ⟨hc, hk⟩, rfl⟩)
  have hPz : ∀ c ∈ S, ∀ k : Fin 5, (k = 3 ∨ k = 4) →
      cv c (k - 2) ∈ PP (S ×ˢ ({3, 4} : Finset (Fin 5))) (fun j => cv j.1 j.2)
        (fun j => cv j.1 (j.2 - 2)) := by
    intro c hc k hk
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(c, k), (hJ _).mpr ⟨hc, hk⟩, rfl⟩)
  have hPin : ∀ a : Fin 11, (Sum.inl a : V0) ∉ PP (S ×ˢ ({3, 4} : Finset (Fin 5)))
      (fun j => cv j.1 j.2) (fun j => cv j.1 (j.2 - 2)) := by
    intro a ha
    simp [PP, cv] at ha
  have hXy : ∀ c ∈ S, ∀ k : Fin 5, (k = 3 ∨ k = 4) → cv c k ∈ X' ∧ cv c (k - 2) ∈ X' := by
    intro c hc k hk
    refine ⟨(hmX _).mpr (Or.inr ⟨c, hc, k, ?_, rfl⟩), (hmX _).mpr (Or.inr ⟨c, hc, k - 2, ?_, rfl⟩)⟩
    · rcases hk with rfl | rfl <;> decide
    · rcases hk with rfl | rfl <;> decide
  have hyzE : ∀ c : Cp, ∀ k : Fin 5, (k = 3 ∨ k = 4) → E0 (cv c k) (cv c (k - 2)) := by
    intro c k hk
    rcases hk with rfl | rfl
    · exact gr_E0.1 _ _ (e0_z1.mpr rfl)
    · exact gr_E0.1 _ _ (e0_z2.mpr rfl)
  refine ⟨hD.1.2.1, opt_useful hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨c, k⟩ _ ⟨d, m⟩ _ e
    exact Prod.ext (cv_inj.mp e).1 (cv_inj.mp e).2
  · rintro ⟨c, k⟩ _ ⟨d, m⟩ _ e
    exact Prod.ext (cv_inj.mp e).1 (sub_left_injective (cv_inj.mp e).2)
  · rintro ⟨c, k⟩ hi ⟨d, m⟩ hj e
    have e2 := (cv_inj.mp e).2
    have hi := ((hJ _).mp hi).2
    have hj := ((hJ _).mp hj).2
    rcases hi with h | h <;> rcases hj with h' | h' <;>
      · simp only at h h' e2
        rw [h, h'] at e2
        revert e2; decide
  · intro ρ hρ hon
    obtain ⟨u, v, huv, hu, hv, hu', hv'⟩ := (hcomp ρ).mp hon
    obtain ⟨c, hc, k, hk, ⟨e, -⟩ | ⟨e, -⟩⟩ := hedge u v huv hu hv
    · exact hρ _ (hPP c hc k hk) (e ▸ hu')
    · exact hρ _ (hPP c hc k hk) (e ▸ hv')
  · exact fun v h => fn_single gr_E0 v ((hcomp _).mp h)
  · rintro ⟨c, k⟩ hj
    obtain ⟨hc, hk⟩ := (hJ _).mp hj
    exact (hcomp _).mpr ((fn_pair gr_E0).mpr ⟨hyzE c k hk, (hXy c hc k hk).1, (hXy c hc k hk).2⟩)
  · rintro ⟨d, m⟩ hi ⟨c, k⟩ hj hne hon
    obtain ⟨hc, hk⟩ := (hJ _).mp hj
    obtain ⟨hd, hm⟩ := (hJ _).mp hi
    have h := ((fn_pair gr_E0).mp ((hcomp _).mp hon)).1
    simp only at hk hm
    refine hne ?_
    have h' : E0 (cv d (m - 2)) (cv c k) := gr_E0.1 _ _ h
    rcases hm with rfl | rfl
    · have e := cv_inj.mp (e0_z1.mp h')
      exact Prod.ext e.1.symm e.2.symm
    · have e := cv_inj.mp (e0_z2.mp h')
      exact Prod.ext e.1.symm e.2.symm
  · rintro ⟨c, k⟩ hj x hx
    obtain ⟨hc, hk⟩ := (hJ _).mp hj
    simp only at hk
    refine (hcomp _).trans ((fn_pair gr_E0).trans ?_)
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases (hmX x).mp h3 with ⟨a, rfl⟩ | ⟨d, hd, m, hm, rfl⟩
      · exact ⟨a, (e0_core k hk).mp h1, rfl⟩
      · exfalso
        obtain ⟨c', hc', k', hk', ⟨-, e | ⟨a, -, e⟩⟩ | ⟨e, -⟩⟩ := hedge _ _ h1 h2 h3
        · exact hx (e ▸ hPz c' hc' k' hk')
        · cases e
        · exact hx (e ▸ hPP c' hc' k' hk')
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(e0_core k hk).mpr ha, (hXy c hc k hk).1, (hmX _).mpr (Or.inl ⟨a, rfl⟩)⟩
  · rintro ⟨c, k⟩ hj
    obtain ⟨a, ha⟩ := osum_ne c.1
    exact ⟨Sum.inl a, hPin a, a, ha, rfl⟩
  · rintro ⟨c, k⟩ hj
    obtain ⟨hc, hk⟩ := (hJ _).mp hj
    exact hD.1.2.2.2 _ ⟨c, hc, k, hk, rfl⟩
  · rw [Finset.card_product]
    have : ({3, 4} : Finset (Fin 5)).card = 2 := by decide
    rw [this]
    omega

section
variable {V ι : Type} [DecidableEq V] {C : Ckt V} {J : Finset ι} {y z : ι → V} {O : ι → Set V}

theorem s6_setup (h : H6 C J y z O) : ∃ (c : ι → ℕ) (L : ι → V ⊕ ℕ), CL C J y z O c L := by
  obtain ⟨hcl, hU, hyi, hzi, hyz, o1, o2, o3, o4, o5, o6, hrig, hcard⟩ := h
  have hW := hU.1
  have hout : ∀ v, C.out ≠ Sum.inl v := by
    intro v e
    refine o2 v ?_
    rw [e]; exact Set.mem_singleton v
  have hread : ∀ v σ, C.val (insert v σ) C.out → ¬ C.val σ C.out → 1 ≤ fo C (Sum.inl v) := by
    intro v σ h1 h2
    rw [fo_pos]
    by_contra hno
    push Not at hno
    refine h2 (ignore hW (v := v) (n := rk C.out) (σ := σ) (fun k hk => absurd hk (hno k)) ?_ _
      hW.2 le_rfl (hout v) h1)
    intro u hu hm
    rcases hm with hm | hm
    · exact absurd hm hu
    · exact hm
  have hry : ∀ j ∈ J, 1 ≤ fo C (Sum.inl (y j)) := fun j hj => hread _ {z j} (o3 j hj) (o2 _)
  have hrz : ∀ j ∈ J, 1 ≤ fo C (Sum.inl (z j)) := fun j hj =>
    hread _ {y j} (by rw [Set.pair_comm]; exact o3 j hj) (o2 _)
  have hex : ∀ j, ∃ g, j ∈ J → Rd C g (Sum.inl (y j)) := by
    intro j
    by_cases hj : j ∈ J
    · obtain ⟨g, hg⟩ := fo_pos.mp (hry j hj)
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose c hc using hex
  have hexL : ∀ j, ∃ k, j ∈ J → ((C.l (c j) = Sum.inl (y j) ∧ C.r (c j) = k) ∨
      (C.r (c j) = Sum.inl (y j) ∧ C.l (c j) = k)) ∧ Rd C (c j) k := by
    intro j
    by_cases hj : j ∈ J
    · obtain ⟨k, hk⟩ := other_operand (hc j hj)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨Sum.inr 0, fun h => absurd h hj⟩
  choose L hL using hexL
  have hyP : ∀ j ∈ J, y j ∈ PP J y z := fun j hj =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj)
  have hzP : ∀ j ∈ J, z j ∈ PP J y z := fun j hj =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
  have hop : ∀ j ∈ J, C.op (c j) = true := fun j hj => (hrig j hj).2 _ (hc j hj)
  have hLon : ∀ j ∈ J, ∀ v, C.val {y j, v} C.out → C.val {v} (L j) := by
    intro j hj v hv
    by_contra hoff
    exact o2 v (and_off hW (hrig j hj).1 (hc j hj).1 (hop j hj) (hL j hj).1 (hout _) hoff hv)
  have hLig : ∀ j ∈ J, ∀ ρ : Set V, C.val (ρ ∪ {y j}) (L j) → C.val ρ (L j) := by
    intro j hj ρ hv
    have hrd := rd_vl hW (hL j hj).2
    refine ignore hW (v := y j) (n := c j)
      (fun i hi => (rd_unique (hrig j hj).1 (hc j hj) hi).le) ?_ _ hrd.1 hrd.2
      (other_ne (hc j hj).1 (hrig j hj).1 (hL j hj).1) hv
    intro u hu hm
    rcases hm with hm | hm
    · exact hm
    · exact absurd hm hu
  have hLl : ∀ j ∈ J, ¬ Dd C (PP J y z) (L j) := by
    intro j hj hd
    obtain ⟨x, hx, hxO⟩ := o6 j hj
    refine dd_off hW (rd_vl hW (hL j hj).2).1 hd (ρ := {x}) ?_
      (hLon j hj x ((o5 j hj x hx).mpr hxO))
    rintro p hp hm
    exact hx (Set.mem_singleton_iff.mp hm ▸ hp)
  have hcb : ∀ j ∈ J, c j ∈ be C (PP J y z) := by
    intro j hj
    refine Finset.mem_filter.mpr ⟨(hc j hj).1, hop j hj, ?_⟩
    have hd : Dd C (PP J y z) (Sum.inl (y j)) := (dd_inl _ _ _).mpr (hyP j hj)
    have hl := hLl j hj
    rcases (hL j hj).1 with e | e
    · rw [e.1, e.2]; tauto
    · rw [e.1, e.2]; tauto
  have hci : Set.InjOn c ↑J := by
    intro i hi j hj he
    by_contra hne
    have hyne : (Sum.inl (y i) : V ⊕ ℕ) ≠ Sum.inl (y j) := fun e => hne (hyi hi hj (Sum.inl.inj e))
    have h1 := (hc i hi).2
    rw [he] at h1
    have hd : Dd C (PP J y z) (Sum.inl (y i)) := (dd_inl _ _ _).mpr (hyP i hi)
    have hl := hLl j hj
    rcases (hL j hj).1 with e | e <;> rcases h1 with e' | e'
    · exact hyne (e'.symm.trans e.1)
    · rw [e.2] at e'; rw [e'] at hl; exact hl hd
    · rw [e.2] at e'; rw [e'] at hl; exact hl hd
    · exact hyne (e'.symm.trans e.1)
  refine ⟨c, L, hci, fun j hj => ⟨hcb j hj, (hL j hj).1,
    fun g hg => rd_unique (hrig j hj).1 hg (hc j hj), le_antisymm (hrig j hj).1 (hry j hj),
    (rd_vl hW (hL j hj).2).1, hLl j hj, hLon j hj _ (o3 j hj), hLig j hj,
    fun x hx hxO => hLon j hj x ((o5 j hj x hx).mpr hxO)⟩, ?_⟩
  have hPc : (PP J y z).card = 2 * J.card := by
    unfold PP
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injOn hyi,
      Finset.card_image_of_injOn hzi]
    · omega
    · rw [Finset.disjoint_left]
      intro v h1 h2
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨j, hj, e⟩ := Finset.mem_image.mp h2
      exact hyz i hi j hj e.symm
  have hdead : Dd C (PP J y z) C.out := o1 _ (fun p hp hm => hm (Finset.mem_coe.mpr hp))
  have h2 := count_dead hU (P := PP J y z) (by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      exact hry j hj
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      exact hrz j hj) hdead
  have h3 := count_part C (PP J y z)
  unfold kl at h3
  have hsub : J.image c ⊆ be C (PP J y z) := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hg
    exact hcb j hj
  have h4 := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_image_of_injOn hci] at h4
  omega

end

section
variable {V ι : Type} [DecidableEq V] {C : Ckt V} {J : Finset ι} {y z : ι → V} {O : ι → Set V}

def ChStep (C : Ckt V) (P : Finset V) (u w : V ⊕ ℕ) : Prop :=
  ∃ k ∈ al C P, w = Sum.inr k ∧ C.op k = false ∧ Rd C k u ∧ fo C u ≤ 1

def Ch (C : Ckt V) (P : Finset V) (v : V) (w : V ⊕ ℕ) : Prop :=
  Relation.ReflTransGen (ChStep C P) (Sum.inl v) w

theorem ch_shape (hW : Wf C) {P : Finset V} {v : V} {w : V ⊕ ℕ} (h : Ch C P v w) :
    (w = Sum.inl v ∨ ∃ k ∈ al C P, w = Sum.inr k ∧ C.op k = false) ∧ Vl C w ∧
      ∀ ρ : Set V, v ∈ ρ → C.val ρ w := by
  unfold Ch at h
  induction h with
  | refl => exact ⟨Or.inl rfl, vl_inl C v, fun ρ hρ => hρ⟩
  | tail _ hs ih =>
    obtain ⟨k, hk, rfl, ho, hr, -⟩ := hs
    refine ⟨Or.inr ⟨k, hk, rfl, ho⟩, vl_inr hr.1, fun ρ hρ => ?_⟩
    rw [val_or hW hr.1 ho]
    rcases hr.2 with e | e
    · exact Or.inl (e ▸ ih.2.2 ρ hρ)
    · exact Or.inr (e ▸ ih.2.2 ρ hρ)

theorem ch_runique (P : Finset V) : Relator.RightUnique (ChStep C P) := by
  rintro u w w' ⟨k, _, rfl, _, hr, hf⟩ ⟨k', _, rfl, _, hr', _⟩
  rw [rd_unique hf hr hr']

theorem ch_end (hW : Wf C) (P : Finset V) (v : V) : ∃ w, Ch C P v w ∧ (¬ ∃ w', ChStep C P w w') ∧
    ∀ u, Ch C P v u → u ≠ w → fo C u ≤ 1 ∧ ∃ k, Rd C k u ∧ Ch C P v (Sum.inr k) := by
  have hfin : ∀ w, Ch C P v w → rk w ≤ C.G.sup id + 1 := by
    intro w hw
    have hvl := (ch_shape hW hw).2.1
    rcases w with u | k
    · simp [rk]
    · have := Finset.le_sup (f := id) (hvl k rfl)
      simp only [id] at this
      simpa [rk] using this
  have hmax : ∃ w, Ch C P v w ∧ ∀ w', Ch C P v w' → rk w' ≤ rk w := by
    by_contra hno
    push Not at hno
    have : ∀ n, ∃ w, Ch C P v w ∧ n ≤ rk w := by
      intro n
      induction n with
      | zero => exact ⟨_, Relation.ReflTransGen.refl, Nat.zero_le _⟩
      | succ n ih =>
        obtain ⟨w, hw, hn⟩ := ih
        obtain ⟨w', hw', hlt⟩ := hno w hw
        exact ⟨w', hw', by omega⟩
    obtain ⟨w, hw, hn⟩ := this (C.G.sup id + 2)
    have := hfin w hw
    omega
  obtain ⟨w, hw, hm⟩ := hmax
  have hend : ¬ ∃ w', ChStep C P w w' := by
    rintro ⟨w', hs⟩
    have h1 := hm w' (hw.tail hs)
    obtain ⟨k, _, rfl, _, hr, _⟩ := hs
    have h2 := (rd_vl hW hr).2
    simp only [rk, Sum.elim_inr] at h1 h2
    omega
  refine ⟨w, hw, hend, fun u hu hne => ?_⟩
  rcases Relation.ReflTransGen.total_of_right_unique (ch_runique P) hu hw with h | h
  · rcases Relation.ReflTransGen.cases_head h with e | ⟨a, hs, _⟩
    · exact absurd e hne
    · have hua := hu.tail hs
      obtain ⟨k, _, rfl, _, hr, hf⟩ := hs
      exact ⟨hf, k, hr, hua⟩
  · rcases Relation.ReflTransGen.cases_head h with e | ⟨a, hs, _⟩
    · exact absurd e.symm hne
    · exact absurd ⟨a, hs⟩ hend

theorem s6_chain (h : H6 C J y z O) {c : ι → ℕ} {L : ι → V ⊕ ℕ} (hc : CL C J y z O c L) :
    ∃ B ⊆ J, B.card ≤ 17 ∧ ∀ j ∈ J, j ∉ B → ∃ K g, ChainOK C (PP J y z) (z j) K g ∧
      ∀ ρ, C.val ρ (Sum.inr g) → C.val ρ (L j) := by
  obtain ⟨hcl, hU, hyi, hzi, hyz, o1, o2, o3, o4, o5, o6, hrig, hcard⟩ := h
  have hW := hU.1
  set P := PP J y z with hP
  have hzP : ∀ j ∈ J, z j ∈ P := fun j hj =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
  choose w hw hend hbelow using fun j => ch_end hW P (z j)
  have hoff : ∀ j u, Ch C P (z j) u → u ≠ C.out := by
    rintro j u hu rfl
    exact o2 (z j) ((ch_shape hW hu).2.2 _ rfl)
  have hdead : ∀ j ∈ J, ∀ u, Ch C P (z j) u → Dd C P u := by
    intro j hj u hu
    rcases (ch_shape hW hu).1 with rfl | ⟨k, hk, rfl, -⟩
    · exact (dd_inl _ _ _).mpr (hzP j hj)
    · exact (kinds_dead hW P (Finset.mem_filter.mp hk).1).mpr (Or.inl hk)
  have hin : ∀ j u k, Ch C P (z j) u → u ≠ w j → Rd C k u → Ch C P (z j) (Sum.inr k) := by
    intro j u k hu hne hr
    obtain ⟨hf, k', hr', hc'⟩ := hbelow j u hu hne
    rw [rd_unique hf hr hr']
    exact hc'
  refine ⟨J.filter (fun j => 2 ≤ fo C (w j)), Finset.filter_subset _ _, ?_, ?_⟩
  · have hinj : Set.InjOn w ↑(J.filter (fun j => 2 ≤ fo C (w j))) := by
      intro i hi j hj he
      have hi := (Finset.mem_filter.mp hi).1
      have hj := (Finset.mem_filter.mp hj).1
      by_contra hne
      refine o4 i hi j hj hne ?_
      have hwon : C.val {y j, z i} (w j) := by
        rw [← he]
        exact (ch_shape hW (hw i)).2.2 _ (Or.inr rfl)
      refine escape hW {u | Ch C P (z j) u ∧ u ≠ w j} (ρ := {y j, z j}) ?_ ?_ _ hW.2 ?_ (o3 j hj)
      · rintro v hv (rfl | hm)
        · exact Or.inl rfl
        · rw [Set.mem_singleton_iff] at hm
          subst hm
          have : Sum.inl (z j) = w j := by
            by_contra hn
            exact hv ⟨Relation.ReflTransGen.refl, hn⟩
          rw [← this] at hwon
          exact hwon
      · intro k hk hkK hb _
        have hkw : Ch C P (z j) (Sum.inr k) := by
          rcases hb with h | h
          · exact hin j _ k h.1 h.2 ⟨hk, Or.inl rfl⟩
          · exact hin j _ k h.1 h.2 ⟨hk, Or.inr rfl⟩
        have : Sum.inr k = w j := by
          by_contra hn
          exact hkK ⟨hkw, hn⟩
        rw [this]; exact hwon
      · rintro ⟨hc', -⟩
        exact hoff j _ hc' rfl
    rw [← Finset.card_image_of_injOn hinj]
    have hsub : (J.filter (fun j => 2 ≤ fo C (w j))).image w ⊆
        ((dw C P).erase C.out) := by
      intro u hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
      have hj := (Finset.mem_filter.mp hj).1
      exact Finset.mem_erase.mpr ⟨hoff j _ (hw j), mem_dw.mpr
        ⟨(ch_shape hW (hw j)).2.1, hdead j hj _ (hw j)⟩⟩
    have h1 : ((J.filter (fun j => 2 ≤ fo C (w j))).image w).card ≤ exc C P := by
      rw [Finset.card_eq_sum_ones]
      refine le_trans (Finset.sum_le_sum (fun u hu => ?_))
        (Finset.sum_le_sum_of_subset (f := fun w => fo C w - 1) hsub)
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
      have := (Finset.mem_filter.mp hj).2
      omega
    have h6 : exc C P + (be C P \ J.image c).card + (su C P).card ≤ 17 := hc.2.2
    omega
  · intro j hj hjB
    have hf : fo C (w j) ≤ 1 := by
      by_contra h
      exact hjB (Finset.mem_filter.mpr ⟨hj, by omega⟩)
    have hLd : ¬ Ch C P (z j) (L j) := fun h => (hc.2.1 j hj).2.2.2.2.2.1 (hdead j hj _ h)
    have hLv := (hc.2.1 j hj).2.2.2.2.1
    have hLz := (hc.2.1 j hj).2.2.2.2.2.2.1
    obtain ⟨k, hk⟩ : ∃ k, Rd C k (w j) := by
      by_contra hno
      push Not at hno
      refine o2 (y j) (escape hW {u | Ch C P (z j) u} (ρ := {y j, z j}) ?_ ?_ _ hW.2
        (fun h => hoff j _ h rfl) (o3 j hj))
      · rintro v hv (rfl | hm)
        · rfl
        · rw [Set.mem_singleton_iff] at hm
          subst hm
          exact absurd Relation.ReflTransGen.refl hv
      · intro i hi hiK hb _
        exfalso
        have key : ∀ u, Ch C P (z j) u → Rd C i u → False := by
          intro u hu hr
          by_cases hne : u = w j
          · exact hno i (hne ▸ hr)
          · exact hiK (hin j u i hu hne hr)
        rcases hb with h | h
        · exact key _ h ⟨hi, Or.inl rfl⟩
        · exact key _ h ⟨hi, Or.inr rfl⟩
    have hread : ∀ u, Ch C P (z j) u → ∀ i, Rd C i u → Ch C P (z j) (Sum.inr i) ∨ i = k := by
      intro u hu i hr
      by_cases hne : u = w j
      · exact Or.inr (rd_unique hf (hne ▸ hr) hk)
      · exact Or.inl (hin j u i hu hne hr)
    have hop : C.op k = false := by
      by_contra ho
      have ho : C.op k = true := by simpa using ho
      refine val_empty hW (L j) hLv (escape hW {u | Ch C P (z j) u} ?_ ?_ _ hLv hLd hLz)
      · intro v hv hm
        rw [Set.mem_singleton_iff] at hm
        subst hm
        exact absurd Relation.ReflTransGen.refl hv
      · intro i hi hiK hb hon
        have hik : i = k := by
          rcases hb with h | h
          · exact (hread _ h i ⟨hi, Or.inl rfl⟩).resolve_left hiK
          · exact (hread _ h i ⟨hi, Or.inr rfl⟩).resolve_left hiK
        subst hik
        exact absurd hon (hcl i hi ho (z j))
    have hwd := hdead j hj _ (hw j)
    have hga : k ∈ ga C P := by
      have hnal : k ∉ al C P := fun h => hend j ⟨_, k, h, rfl, hop, hk, hf⟩
      have hd : Dd C P (C.l k) ∨ Dd C P (C.r k) := by
        rcases hk.2 with e | e
        · exact Or.inl (e ▸ hwd)
        · exact Or.inr (e ▸ hwd)
      have hna : ¬ (Dd C P (C.l k) ∧ Dd C P (C.r k)) := fun h =>
        hnal (Finset.mem_filter.mpr ⟨hk.1, h⟩)
      exact Finset.mem_filter.mpr ⟨hk.1, hop, by tauto⟩
    have hkK : ¬ Ch C P (z j) (Sum.inr k) := by
      intro h
      rcases (ch_shape hW h).1 with e | ⟨k', hk', e, -⟩
      · cases e
      · cases e
        have h1 := (Finset.mem_filter.mp hk').2
        have h2 := (Finset.mem_filter.mp hga).2.2
        tauto
    refine ⟨{u | Ch C P (z j) u}, k, ⟨Relation.ReflTransGen.refl, hga, hkK, ?_, ?_, hread, ?_,
      w j, hw j, hk⟩, ?_⟩
    · intro v hv
      rcases (ch_shape hW hv).1 with e | ⟨k', _, e, -⟩
      · exact Sum.inl.inj e
      · cases e
    · intro i hi
      rcases (ch_shape hW hi).1 with e | ⟨k', hk', e, ho⟩
      · cases e
      · cases e; exact ⟨hk', ho⟩
    · intro ρ hρ
      refine ⟨?_, fun u hu => (ch_shape hW hu).2.imp id (fun h => h ρ hρ)⟩
      rw [val_or hW hk.1 hop]
      have := (ch_shape hW (hw j)).2.2 ρ hρ
      rcases hk.2 with e | e
      · exact Or.inl (e ▸ this)
      · exact Or.inr (e ▸ this)
    · intro ρ hρ
      have key : ∀ u, Vl C u → ¬ Ch C P (z j) u → C.val {z j} u → C.val ρ u := by
        refine wire_ind' hW (p := fun u => ¬ Ch C P (z j) u → C.val {z j} u → C.val ρ u) ?_ ?_
        · intro v hv hm
          have : v = z j := hm
          subst this
          exact absurd Relation.ReflTransGen.refl hv
        · intro i hi hl hr hiK hon
          by_cases ho : C.op i = true
          · exact absurd hon (hcl i hi ho (z j))
          · have ho : C.op i = false := by simpa using ho
            rw [val_or hW hi ho] at hon
            rcases hon with hon | hon
            · by_cases hc' : Ch C P (z j) (C.l i)
              · rw [(hread _ hc' i ⟨hi, Or.inl rfl⟩).resolve_left hiK]; exact hρ
              · rw [val_or hW hi ho]; exact Or.inl (hl hc' hon)
            · by_cases hc' : Ch C P (z j) (C.r i)
              · rw [(hread _ hc' i ⟨hi, Or.inr rfl⟩).resolve_left hiK]; exact hρ
              · rw [val_or hW hi ho]; exact Or.inr (hr hc' hon)
      exact key _ hLv hLd hLz

end

section
variable {V ι : Type} [DecidableEq V] {C : Ckt V} {J : Finset ι} {y z : ι → V} {O : ι → Set V}

theorem s6_sig (h : H6 C J y z O) {c : ι → ℕ} {L : ι → V ⊕ ℕ} (hc : CL C J y z O c L) {j : ι}
    (hj : j ∈ J) {K : Set (V ⊕ ℕ)} {g : ℕ} (hK : ChainOK C (PP J y z) (z j) K g) {σ : Set V}
    (hy : y j ∈ σ) (hL : C.val σ (L j))
    (hs : ∀ v ∈ LLs C (PP J y z) (be C (PP J y z) \ J.image c),
      GP C (PP J y z) v (Sum.inr g) → C.val σ v) : C.val σ C.out := by
  obtain ⟨hcl, hU, hyi, hzi, hyz, o1, o2, o3, o4, o5, o6, hrig, hcard⟩ := h
  have hW := hU.1
  set P := PP J y z with hP
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, -⟩ := hK
  have hzP : z j ∈ P := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
  have hKd : ∀ w ∈ K, Dd C P w := by
    intro w hw
    rcases w with v | k
    · rw [k4 v hw]; exact (dd_inl _ _ _).mpr hzP
    · exact (kinds_dead hW P (Finset.mem_filter.mp (k5 k hw).1).1).mpr (Or.inl (k5 k hw).1)
  have hgl : ¬ Dd C P (Sum.inr g) := by
    have hg := Finset.mem_filter.mp k2
    rw [dd_gate hW P hg.1, if_neg (by simp [hg.2.1])]
    have := hg.2.2
    tauto
  have hLL : ∀ k u, (k ∈ be C P \ J.image c ∨ k ∈ su C P) → Rd C k u → ¬ Dd C P u →
      u ∈ LLs C P (be C P \ J.image c) := by
    intro k u hk hr hu
    refine Finset.mem_filter.mpr ⟨?_, hu⟩
    have hk' : k ∈ be C P \ J.image c ∪ su C P := Finset.mem_union.mpr hk
    rcases hr.2 with e | e
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hk', e⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk', e⟩)
  have main : ∀ w, Vl C w → w ∉ K → (¬ Dd C P w → ¬ GP C P w (Sum.inr g)) →
      C.val {y j, z j} w → C.val σ w := by
    refine wire_ind' hW (p := fun w => w ∉ K → (¬ Dd C P w → ¬ GP C P w (Sum.inr g)) →
      C.val {y j, z j} w → C.val σ w) ?_ ?_
    · rintro v hv _ (rfl | hm)
      · exact hy
      · rw [Set.mem_singleton_iff.mp hm] at hv
        exact absurd k1 hv
    · intro k hk hl hr hkK hgp hon
      have hdop : ∀ u, Rd C k u → Dd C P u → k ≠ g →
          (u ∉ K → (¬ Dd C P u → ¬ GP C P u (Sum.inr g)) → C.val {y j, z j} u → C.val σ u) →
          C.val {y j, z j} u → C.val σ u := by
        intro u hu hd hkg ih
        refine ih (fun huK => ?_) (fun h => absurd hd h)
        rcases k6 u huK k hu with h | h
        · exact hkK h
        · exact hkg h
      have hlop : ∀ u, Rd C k u → ¬ Dd C P u → (k ∈ be C P \ J.image c ∨ k ∈ su C P) →
          (u ∉ K → (¬ Dd C P u → ¬ GP C P u (Sum.inr g)) → C.val {y j, z j} u → C.val σ u) →
          C.val {y j, z j} u → C.val σ u := by
        intro u hu hd hkk ih hv
        by_cases hg' : GP C P u (Sum.inr g)
        · exact hs u (hLL k u hkk hu hd) hg'
        · exact ih (fun h => hd (hKd u h)) (fun _ => hg') hv
      have hrl : Rd C k (C.l k) := ⟨hk, Or.inl rfl⟩
      have hrr : Rd C k (C.r k) := ⟨hk, Or.inr rfl⟩
      have finish : (C.val {y j, z j} (C.l k) → C.val σ (C.l k)) →
          (C.val {y j, z j} (C.r k) → C.val σ (C.r k)) → C.val σ (Sum.inr k) := by
        intro a b
        rw [val_gate hW hk] at hon ⊢
        split_ifs at hon ⊢
        · exact hon.imp a b
        · exact hon.imp a b
      rcases kinds_cover P hk with h | h | h | h
      · have hd := (Finset.mem_filter.mp h).2
        have hkg : k ≠ g := by
          rintro rfl
          exact hgl ((kinds_dead hW P hk).mpr (Or.inl h))
        exact finish (hdop _ hrl hd.1 hkg hl) (hdop _ hrr hd.2 hkg hr)
      · have hkg : k ≠ g := by
          rintro rfl
          exact hgl ((kinds_dead hW P hk).mpr (Or.inr h))
        by_cases him : k ∈ J.image c
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp him
          have hci := hc.2.1 i hi
          have ho := (Finset.mem_filter.mp h).2.1
          rw [val_and hW hk ho] at hon ⊢
          have hyon : y i ∈ ({y j, z j} : Set V) := by
            rcases hci.2.1 with e | e
            · have := hon.1; rw [e.1] at this; exact this
            · have := hon.2; rw [e.1] at this; exact this
          have hij : i = j := by
            rcases hyon with e | e
            · exact hyi hi hj e
            · exact absurd (Set.mem_singleton_iff.mp e) (hyz i hi j hj)
          subst hij
          rcases hci.2.1 with e | e
          · rw [e.1, e.2]; exact ⟨hy, hL⟩
          · rw [e.1, e.2]; exact ⟨hL, hy⟩
        · have hkb : k ∈ be C P \ J.image c := Finset.mem_sdiff.mpr ⟨h, him⟩
          have hd := (Finset.mem_filter.mp h).2.2
          by_cases hdl : Dd C P (C.l k)
          · exact finish (hdop _ hrl hdl hkg hl) (hlop _ hrr (hd.mp hdl) (Or.inl hkb) hr)
          · have hdr : Dd C P (C.r k) := by tauto
            exact finish (hlop _ hrl hdl (Or.inl hkb) hl) (hdop _ hrr hdr hkg hr)
      · have hd := (Finset.mem_filter.mp h).2.2
        have ho := (Finset.mem_filter.mp h).2.1
        have hkl : ¬ Dd C P (Sum.inr k) := by
          rw [dd_gate hW P hk, if_neg (by simp [ho])]
          tauto
        have hkg : k ≠ g := by
          rintro rfl
          exact hgp hkl Relation.ReflTransGen.refl
        have hlive : ∀ u, Rd C k u → ¬ Dd C P u →
            (u ∉ K → (¬ Dd C P u → ¬ GP C P u (Sum.inr g)) → C.val {y j, z j} u → C.val σ u) →
            C.val {y j, z j} u → C.val σ u := by
          intro u hu hud ih
          exact ih (fun hh => hud (hKd u hh)) (fun _ hg' => hgp hkl
            (Relation.ReflTransGen.head ⟨k, h, rfl, hu.2, hud⟩ hg'))
        by_cases hdl : Dd C P (C.l k)
        · exact finish (hdop _ hrl hdl hkg hl) (hlive _ hrr (hd.mp hdl) hr)
        · have hdr : Dd C P (C.r k) := by tauto
          exact finish (hlive _ hrl hdl hl) (hdop _ hrr hdr hkg hr)
      · have hd := (Finset.mem_filter.mp h).2
        exact finish (hlop _ hrl hd.1 (Or.inr h) hl) (hlop _ hrr hd.2 (Or.inr h) hr)
  have hdead : Dd C P C.out := o1 _ (fun p hp hm => hm (Finset.mem_coe.mpr hp))
  refine main C.out hW.2 (fun hh => ?_) (fun hh => absurd hdead hh) (o3 j hj)
  exact o2 (z j) (((k7 {z j} rfl).2 _ hh).2)

end

section
variable {V ι : Type} [DecidableEq V] {C : Ckt V} {J : Finset ι} {y z : ι → V} {O : ι → Set V}

theorem s6_lowest (h : H6 C J y z O) {c : ι → ℕ} {L : ι → V ⊕ ℕ} (hc : CL C J y z O c L) {j : ι}
    (hj : j ∈ J) {K : Set (V ⊕ ℕ)} {g : ℕ} (hK : ChainOK C (PP J y z) (z j) K g) {v : V ⊕ ℕ}
    (hv : v ∈ LLs C (PP J y z) (be C (PP J y z) \ J.image c)) (hon : C.val {z j} v)
    (hmin : ∀ u ∈ LLs C (PP J y z) (be C (PP J y z) \ J.image c), C.val {z j} u → rk v ≤ rk u) :
    GP C (PP J y z) v (Sum.inr g) := by
  obtain ⟨hcl, hU, hyi, hzi, hyz, o1, o2, o3, o4, o5, o6, hrig, hcard⟩ := h
  have hW := hU.1
  set P := PP J y z with hP
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, -⟩ := hK
  have hzP : z j ∈ P := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
  have hgl : ¬ Dd C P (Sum.inr g) := by
    have hg := Finset.mem_filter.mp k2
    rw [dd_gate hW P hg.1, if_neg (by simp [hg.2.1])]
    have := hg.2.2
    tauto
  have hdK : ∀ w, Vl C w → Dd C P w → C.val {z j} w → w ∈ K := by
    refine wire_ind' hW (p := fun w => Dd C P w → C.val {z j} w → w ∈ K) ?_ ?_
    · intro u _ hu
      have : u = z j := hu
      rw [this]; exact k1
    · intro k hk hl hr hd hon
      by_cases ho : C.op k = true
      · exact absurd hon (hcl k hk ho (z j))
      have ho : C.op k = false := by simpa using ho
      have hd' := hd
      rw [dd_gate hW P hk, if_neg (by simp [ho])] at hd'
      have hkg : k ≠ g := by
        rintro rfl
        exact hgl hd
      rw [val_or hW hk ho] at hon
      rcases hon with hon | hon
      · exact (k6 _ (hl hd'.1 hon) k ⟨hk, Or.inl rfl⟩).resolve_right hkg
      · exact (k6 _ (hr hd'.2 hon) k ⟨hk, Or.inr rfl⟩).resolve_right hkg
  have hvm := Finset.mem_filter.mp hv
  have hvv : Vl C v := by
    rcases Finset.mem_union.mp hvm.1 with h | h
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      have hkG : k ∈ C.G := by
        rcases Finset.mem_union.mp hk with hk | hk
        · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hk).1).1
        · exact (Finset.mem_filter.mp hk).1
      exact (hW.1 k hkG).1.1
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      have hkG : k ∈ C.G := by
        rcases Finset.mem_union.mp hk with hk | hk
        · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hk).1).1
        · exact (Finset.mem_filter.mp hk).1
      exact (hW.1 k hkG).2.1
  have hrk : ∀ u, GP C P v u → rk u ≤ rk v := by
    intro u hu
    unfold GP at hu
    induction hu with
    | refl => exact le_rfl
    | tail _ hs ih =>
      obtain ⟨k, hk, rfl, hr, -⟩ := hs
      have := (rd_vl hW (⟨(Finset.mem_filter.mp hk).1, hr⟩ : Rd C k _)).2
      simp only [rk, Sum.elim_inr] at ih this ⊢
      omega
  have main : ∀ u, Vl C u → ¬ Dd C P u → GP C P v u → C.val {z j} u →
      GP C P v (Sum.inr g) := by
    refine wire_ind' hW (p := fun u => ¬ Dd C P u → GP C P v u → C.val {z j} u →
      GP C P v (Sum.inr g)) ?_ ?_
    · intro u hu _ hm
      have : u = z j := hm
      rw [this] at hu
      exact absurd ((dd_inl _ _ _).mpr hzP) hu
    · intro k hk hl hr hlive hgp hon
      by_cases ho : C.op k = true
      · exact absurd hon (hcl k hk ho (z j))
      have ho : C.op k = false := by simpa using ho
      rw [val_or hW hk ho] at hon
      rcases kinds_cover P hk with h | h | h | h
      · exact absurd ((kinds_dead hW P hk).mpr (Or.inl h)) hlive
      · exact absurd ((kinds_dead hW P hk).mpr (Or.inr h)) hlive
      · have key : ∀ u, Rd C k u → (¬ Dd C P u → GP C P v u → C.val {z j} u →
            GP C P v (Sum.inr g)) → C.val {z j} u → GP C P v (Sum.inr g) := by
          intro u hu ih hv
          by_cases hd : Dd C P u
          · rcases k6 u (hdK u (rd_vl hW hu).1 hd hv) k hu with hh | hh
            · exact absurd ((kinds_dead hW P hk).mpr (Or.inl (k5 k hh).1)) hlive
            · exact hh ▸ hgp
          · exact ih hd (hgp.tail ⟨k, h, rfl, hu.2, hd⟩) hv
        rcases hon with hon | hon
        · exact key _ ⟨hk, Or.inl rfl⟩ hl hon
        · exact key _ ⟨hk, Or.inr rfl⟩ hr hon
      · exfalso
        have hd := (Finset.mem_filter.mp h).2
        have hk' : k ∈ be C P \ J.image c ∪ su C P := Finset.mem_union_right _ h
        have h2 := hrk _ hgp
        simp only [rk, Sum.elim_inr] at h2
        rcases hon with hon | hon
        · have h1 := hmin _ (Finset.mem_filter.mpr ⟨Finset.mem_union_left _
            (Finset.mem_image_of_mem _ hk'), hd.1⟩) hon
          have h3 := (hW.1 k hk).1.2
          change rk v ≤ _ at h1
          simp only [rk] at h1 h3 h2
          omega
        · have h1 := hmin _ (Finset.mem_filter.mpr ⟨Finset.mem_union_right _
            (Finset.mem_image_of_mem _ hk'), hd.2⟩) hon
          have h3 := (hW.1 k hk).2.2
          simp only [rk] at h1 h3 h2
          omega
  exact main v hvv hvm.2 Relation.ReflTransGen.refl hon

theorem s6_bad (h : H6 C J y z O) {c : ι → ℕ} {L : ι → V ⊕ ℕ} (hc : CL C J y z O c L) :
    (J.filter (fun j => ∃ x, x ∉ PP J y z ∧ x ∉ O j ∧ C.val {x} (L j))).card ≤ 17 + 2 ^ 34 := by
  have h' := h
  obtain ⟨hcl, hU, hyi, hzi, hyz, o1, o2, o3, o4, o5, o6, hrig, hcard⟩ := h'
  have hW := hU.1
  obtain ⟨B, hBJ, hB, hch⟩ := s6_chain h hc
  set P := PP J y z with hP
  set Bd := J.filter (fun j => ∃ x, x ∉ P ∧ x ∉ O j ∧ C.val {x} (L j)) with hBd
  set LS := LLs C P (be C P \ J.image c) with hLS
  have hLSv : ∀ v ∈ LS, Vl C v := by
    intro v hv
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with h | h
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      have hkG : k ∈ C.G := by
        rcases Finset.mem_union.mp hk with hk | hk
        · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hk).1).1
        · exact (Finset.mem_filter.mp hk).1
      exact (hW.1 k hkG).1.1
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      have hkG : k ∈ C.G := by
        rcases Finset.mem_union.mp hk with hk | hk
        · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hk).1).1
        · exact (Finset.mem_filter.mp hk).1
      exact (hW.1 k hkG).2.1
  have hLScard : LS.card ≤ 34 := by
    have h1 : LS.card ≤ ((be C P \ J.image c ∪ su C P).image C.l ∪
        (be C P \ J.image c ∪ su C P).image C.r).card := Finset.card_filter_le _ _
    have h2 := Finset.card_union_le ((be C P \ J.image c ∪ su C P).image C.l)
      ((be C P \ J.image c ∪ su C P).image C.r)
    have h3 := Finset.card_image_le (s := be C P \ J.image c ∪ su C P) (f := C.l)
    have h4 := Finset.card_image_le (s := be C P \ J.image c ∪ su C P) (f := C.r)
    have h5 := Finset.card_union_le (be C P \ J.image c) (su C P)
    have h6 : exc C P + (be C P \ J.image c).card + (su C P).card ≤ 17 := hc.2.2
    have h7 : LS.card ≤ _ := h1.trans h2
    omega
  have hgpval : ∀ {v u : V ⊕ ℕ}, GP C P v u → ∀ ρ, C.val ρ u → C.val ρ v := by
    intro v u hvu ρ
    unfold GP at hvu
    induction hvu with
    | refl => exact id
    | tail _ hs ih =>
      obtain ⟨k, hk, rfl, hr, -⟩ := hs
      intro hu
      refine ih ?_
      have hk' := Finset.mem_filter.mp hk
      rw [val_or hW hk'.1 hk'.2.1]
      rcases hr with e | e
      · exact Or.inl (e ▸ hu)
      · exact Or.inr (e ▸ hu)
  have hgpu : Relator.RightUnique (GStep C P) := by
    rintro a b b' ⟨k, hk, rfl, hr, hb⟩ ⟨k', hk', e, hr', hb'⟩
    cases e
    have hd := (Finset.mem_filter.mp hk).2.2
    rcases hr with e | e <;> rcases hr' with e' | e'
    · rw [← e, ← e']
    · rw [e, e'] at hd; tauto
    · rw [e, e'] at hd; tauto
    · rw [← e, ← e']
  let τ : ι → Finset (V ⊕ ℕ) := fun j => LS.filter (fun v => C.val {z j} v)
  have key : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → τ i = τ j → ∀ K g K' g',
      ChainOK C P (z j) K g → (∀ ρ, C.val ρ (Sum.inr g) → C.val ρ (L j)) →
      ChainOK C P (z i) K' g' → GP C P (Sum.inr g) (Sum.inr g') → False := by
    intro i hi j hj hne hτ K g K' g' hK hLg hK' hgg
    have hzi : C.val {z i} (L j) := hLg _ (hgpval hgg _ ((hK'.2.2.2.2.2.2.1 {z i} rfl).1))
    refine o4 i hi j hj hne (s6_sig h hc hj hK (Or.inl rfl) ?_ ?_)
    · exact val_mono hW (by intro v hv; exact Or.inr hv) _ (hc.2.1 j hj).2.2.2.2.1 hzi
    · intro v hv hgv
      have hvj : v ∈ τ j := Finset.mem_filter.mpr
        ⟨hv, hgpval hgv _ ((hK.2.2.2.2.2.2.1 {z j} rfl).1)⟩
      rw [← hτ] at hvj
      exact val_mono hW (by intro u hu; exact Or.inr hu) _ (hLSv v hv)
        (Finset.mem_filter.mp hvj).2
  have hinj : Set.InjOn τ ↑(Bd \ B) := by
    intro i hi j hj hτ
    by_contra hne
    obtain ⟨hi1, hiB⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨hj1, hjB⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨hiJ, -⟩ := Finset.mem_filter.mp hi1
    obtain ⟨hjJ, x, hx, hxO, hxL⟩ := Finset.mem_filter.mp hj1
    obtain ⟨K, g, hK, hLg⟩ := hch j hjJ hjB
    obtain ⟨K', g', hK', hLg'⟩ := hch i hiJ hiB
    have hnonempty : (τ j).Nonempty := by
      by_contra hemp
      refine hxO ((o5 j hjJ x hx).mp (s6_sig h hc hjJ hK (Or.inl rfl) ?_ ?_))
      · exact val_mono hW (by intro v hv; exact Or.inr hv) _ (hc.2.1 j hjJ).2.2.2.2.1 hxL
      · intro v hv hgv
        refine absurd ⟨v, ?_⟩ hemp
        exact Finset.mem_filter.mpr ⟨hv, hgpval hgv _ ((hK.2.2.2.2.2.2.1 {z j} rfl).1)⟩
    obtain ⟨v, hv, hvmin⟩ := Finset.exists_min_image (τ j) rk hnonempty
    have hvi : v ∈ τ i := hτ ▸ hv
    have g1 : GP C P v (Sum.inr g) := s6_lowest h hc hjJ hK (Finset.mem_filter.mp hv).1
      (Finset.mem_filter.mp hv).2 (fun u hu hon => hvmin u (Finset.mem_filter.mpr ⟨hu, hon⟩))
    have g2 : GP C P v (Sum.inr g') := s6_lowest h hc hiJ hK' (Finset.mem_filter.mp hvi).1
      (Finset.mem_filter.mp hvi).2 (fun u hu hon => hvmin u (by
        rw [← hτ]; exact Finset.mem_filter.mpr ⟨hu, hon⟩))
    rcases Relation.ReflTransGen.total_of_right_unique hgpu g1 g2 with hh | hh
    · exact key i hiJ j hjJ hne hτ K g K' g' hK hLg hK' hh
    · exact key j hjJ i hiJ (Ne.symm hne) hτ.symm K' g' K g hK' hLg' hK hh
  have h1 : (Bd \ B).card ≤ 2 ^ 34 := by
    rw [← Finset.card_image_of_injOn hinj]
    have hsub : (Bd \ B).image τ ⊆ LS.powerset := by
      intro t ht
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by norm_num) hLScard
  have h2 : Bd.card ≤ (Bd \ B).card + B.card := by
    have := Finset.card_le_card_sdiff_add_card (s := Bd) (t := B)
    exact this
  omega

end

theorem extract {C : Ckt V0} (hW : Wf C) (hcl : Clean C) {P : Finset V0}
    (hP : ∀ a : Fin 11, (Sum.inl a : V0) ∉ P) (w : Fin 14 → V0 ⊕ ℕ)
    (hw : ∀ l, Vl C (w l) ∧ ¬ Dd C P (w l) ∧ ∀ a : Fin 11, C.val {Sum.inl a} (w l) ↔ a ∈ Osum l) :
    ∃ F : Finset (Finset (Fin 11)), F.card ≤ (su C P).card ∧ (∀ l, Osum l ∈ F) ∧
      ∀ A ∈ F, 2 ≤ A.card ∧ ∃ A1 A2, A1 ∪ A2 = A ∧ A1 ≠ A ∧ A2 ≠ A ∧
        (A1 ∈ F ∨ A1.card ≤ 1) ∧ (A2 ∈ F ∨ A2.card ≤ 1) := by
  let l : V0 ⊕ ℕ → Finset (Fin 11) := fun w => Finset.univ.filter (fun a => C.val {Sum.inl a} w)
  have hl : ∀ w a, a ∈ l w ↔ C.val {Sum.inl a} w := by
    intro w a; simp [l]
  let F : Finset (Finset (Fin 11)) :=
    ((su C P).image (fun g => l (Sum.inr g))).filter (fun A => 2 ≤ A.card)
  have main : ∀ w, Vl C w → ¬ Dd C P w → 2 ≤ (l w).card → l w ∈ F ∧
      ∃ A1 A2, A1 ∪ A2 = l w ∧ A1 ≠ l w ∧ A2 ≠ l w ∧
        (A1 ∈ F ∨ A1.card ≤ 1) ∧ (A2 ∈ F ∨ A2.card ≤ 1) := by
    refine wire_ind' hW (p := fun w => ¬ Dd C P w → 2 ≤ (l w).card → l w ∈ F ∧
      ∃ A1 A2, A1 ∪ A2 = l w ∧ A1 ≠ l w ∧ A2 ≠ l w ∧
        (A1 ∈ F ∨ A1.card ≤ 1) ∧ (A2 ∈ F ∨ A2.card ≤ 1)) ?_ ?_
    · intro v _ h2
      exfalso
      have : (l (Sum.inl v)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        rw [hl] at ha hb
        exact Sum.inl.inj ((Set.mem_singleton_iff.mp ha).symm.trans (Set.mem_singleton_iff.mp hb))
      omega
    · intro g hg ihl ihr hlive h2
      have hdoff : ∀ u, Vl C u → Dd C P u → l u = ∅ := by
        intro u hu hd
        rw [Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rw [hl] at ha
        refine dd_off hW hu hd ?_ ha
        intro p hp hm
        rw [Set.mem_singleton_iff.mp hm] at hp
        exact hP a hp
      have hor : C.op g = false → l (Sum.inr g) = l (C.l g) ∪ l (C.r g) := by
        intro ho
        ext a
        rw [Finset.mem_union, hl, hl, hl, val_or hW hg ho]
      rcases kinds_cover P hg with h | h | h | h
      · exact absurd ((kinds_dead hW P hg).mpr (Or.inl h)) hlive
      · exact absurd ((kinds_dead hW P hg).mpr (Or.inr h)) hlive
      · obtain ⟨-, ho, hd⟩ := Finset.mem_filter.mp h
        have e := hor ho
        by_cases hdl : Dd C P (C.l g)
        · rw [hdoff _ (hW.1 g hg).1.1 hdl, Finset.empty_union] at e
          rw [e] at h2 ⊢
          exact ihr (hd.mp hdl) h2
        · have hdr : Dd C P (C.r g) := by tauto
          rw [hdoff _ (hW.1 g hg).2.1 hdr, Finset.union_empty] at e
          rw [e] at h2 ⊢
          exact ihl hdl h2
      · obtain ⟨-, hdl, hdr⟩ := Finset.mem_filter.mp h
        by_cases ho : C.op g = true
        · exfalso
          have : l (Sum.inr g) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro a ha
            rw [hl] at ha
            exact hcl g hg ho _ ha
          rw [this] at h2
          simp at h2
        · have ho : C.op g = false := by simpa using ho
          have e := hor ho
          have hF : l (Sum.inr g) ∈ F :=
            Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨g, h, rfl⟩, h2⟩
          by_cases e1 : l (C.l g) = l (Sum.inr g)
          · rw [← e1] at h2 ⊢
            exact ihl hdl h2
          by_cases e2 : l (C.r g) = l (Sum.inr g)
          · rw [← e2] at h2 ⊢
            exact ihr hdr h2
          refine ⟨hF, l (C.l g), l (C.r g), e.symm, e1, e2, ?_, ?_⟩
          · by_cases hc : 2 ≤ (l (C.l g)).card
            · exact Or.inl (ihl hdl hc).1
            · exact Or.inr (by omega)
          · by_cases hc : 2 ≤ (l (C.r g)).card
            · exact Or.inl (ihr hdr hc).1
            · exact Or.inr (by omega)
  refine ⟨F, (Finset.card_filter_le _ _).trans Finset.card_image_le, ?_, ?_⟩
  · intro i
    have e : l (w i) = Osum i := by
      ext a
      rw [hl]
      exact (hw i).2.2 a
    have hc : 2 ≤ (Osum i).card := by
      fin_cases i <;> decide
    rw [← e] at hc ⊢
    exact (main _ (hw i).1 (hw i).2.1 hc).1
  · intro A hA
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hA
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp h1
    have hg' := Finset.mem_filter.mp hg
    refine ⟨h2, (main _ (vl_inr hg'.1) ?_ h2).2⟩
    rw [dd_gate hW P hg'.1]
    split_ifs <;> tauto

def Dec (F : Finset (Finset (Fin 11))) : Prop :=
  ∀ A ∈ F, 2 ≤ A.card ∧ ∃ A1 A2, A1 ∪ A2 = A ∧ A1 ≠ A ∧ A2 ≠ A ∧
    (A1 ∈ F ∨ A1.card ≤ 1) ∧ (A2 ∈ F ∨ A2.card ≤ 1)

noncomputable def Hs (F : Finset (Finset (Fin 11))) : Finset (Finset (Fin 11)) :=
  F.filter (fun A => ∀ l, A ≠ Osum l)

theorem hlp {F : Finset (Finset (Fin 11))} (hF : Dec F) {B : Finset (Fin 11)} {e : Fin 11}
    (hB : B ∈ F) (he : e ∈ B) (h1 : ∀ l, Osum l ⊆ B → e ∈ Osum l → Osum l = B)
    (h2 : ∀ l, B.erase e ≠ Osum l) (h3 : 3 ≤ B.card) :
    ∃ H ∈ Hs F, H ⊆ B ∧ ((e ∈ H ∧ ∃ D, H ∪ D = B ∧ D ≠ B ∧ (D ∈ F ∨ D.card ≤ 1)) ∨
      H = B.erase e) := by
  obtain ⟨-, A1, A2, hu, n1, n2, c1, c2⟩ := hF B hB
  have key : ∀ A1 A2 : Finset (Fin 11), A1 ∪ A2 = B → A1 ≠ B → A2 ≠ B →
      (A1 ∈ F ∨ A1.card ≤ 1) → (A2 ∈ F ∨ A2.card ≤ 1) → e ∈ A1 →
      ∃ H ∈ Hs F, H ⊆ B ∧ ((e ∈ H ∧ ∃ D, H ∪ D = B ∧ D ≠ B ∧ (D ∈ F ∨ D.card ≤ 1)) ∨
        H = B.erase e) := by
    intro A1 A2 hu n1 n2 c1 c2 he1
    have s1 : A1 ⊆ B := hu ▸ Finset.subset_union_left
    have s2 : A2 ⊆ B := hu ▸ Finset.subset_union_right
    rcases c1 with c1 | c1
    · refine ⟨A1, Finset.mem_filter.mpr ⟨c1, ?_⟩, s1, Or.inl ⟨he1, A2, hu, n2, c2⟩⟩
      rintro l rfl
      exact n1 (h1 l s1 he1)
    · have hA1 : ∀ a ∈ A1, a = e := fun a ha => Finset.card_le_one.mp c1 a ha e he1
      have hsub : B.erase e ⊆ A2 := by
        intro a ha
        obtain ⟨hne, haB⟩ := Finset.mem_erase.mp ha
        rw [← hu] at haB
        rcases Finset.mem_union.mp haB with h | h
        · exact absurd (hA1 a h) hne
        · exact h
      have heA2 : e ∉ A2 := by
        intro h
        refine n2 (Finset.Subset.antisymm s2 fun a ha => ?_)
        by_cases hae : a = e
        · exact hae ▸ h
        · exact hsub (Finset.mem_erase.mpr ⟨hae, ha⟩)
      have hA2 : A2 = B.erase e := Finset.Subset.antisymm
        (fun a ha => Finset.mem_erase.mpr ⟨fun h => heA2 (h ▸ ha), s2 ha⟩) hsub
      have hc := Finset.card_erase_add_one he
      rw [← hA2] at hc
      refine ⟨A2, Finset.mem_filter.mpr ⟨c2.resolve_right (by omega), ?_⟩, s2, Or.inr hA2⟩
      intro l hl
      exact h2 l (hA2 ▸ hl)
  have he' := he
  rw [← hu] at he'
  rcases Finset.mem_union.mp he' with h | h
  · exact key A1 A2 hu n1 n2 c1 c2 h
  · exact key A2 A1 (by rw [Finset.union_comm]; exact hu) n2 n1 c2 c1 h

theorem three_le {S : Finset (Finset (Fin 11))} {a b c : Finset (Fin 11)} (ha : a ∈ S)
    (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ S.card := by
  have : ({a, b, c} : Finset (Finset (Fin 11))) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h := Finset.card_le_card this
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at h

theorem tri {F : Finset (Finset (Fin 11))} (hF : Dec F) {B1 B2 M H : Finset (Fin 11)}
    {c1 c2 : Fin 11} (hH : H ∈ Hs F) (hHM : H ⊆ M)
    (s0 : ∀ l, ¬ Osum l ⊆ M)
    (s1 : ∀ l, Osum l ⊆ B1 → c1 ∈ Osum l → (∃ t ∈ M, t ∈ Osum l) → Osum l = B1)
    (s2 : ∀ l, Osum l ⊆ B2 → c2 ∈ Osum l → (∃ t ∈ M, t ∈ Osum l) → Osum l = B2)
    (m1 : M ⊆ B1) (m2 : M ⊆ B2) (a1 : c1 ∈ B1) (a2 : c2 ∈ B2) (b1 : c1 ∉ B2) (b2 : c2 ∉ B1)
    (hM : M.card = 4)
    (d1 : ∃ D, H ∪ D = B1 ∧ D ≠ B1 ∧ (D ∈ F ∨ D.card ≤ 1))
    (d2 : ∃ D, H ∪ D = B2 ∧ D ≠ B2 ∧ (D ∈ F ∨ D.card ≤ 1)) :
    3 ≤ ((Hs F).filter (fun A => A ⊆ B1 ∪ B2)).card := by
  have hMU : M ⊆ B1 ∪ B2 := m1.trans Finset.subset_union_left
  have hhelp : ∀ A ∈ F, A ⊆ M → A ∈ (Hs F).filter (fun A => A ⊆ B1 ∪ B2) := by
    intro A hA hAM
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hA, ?_⟩, hAM.trans hMU⟩
    rintro l rfl
    exact s0 l hAM
  have hHF := (Finset.mem_filter.mp hH).1
  by_cases hHe : H = M
  · subst hHe
    obtain ⟨-, A1, A2, hu, n1, n2, k1, k2⟩ := hF H hHF
    have main : ∀ A1 A2 : Finset (Fin 11), A1 ∪ A2 = H → A1 ≠ H → A2 ≠ H →
        A1 ∈ F → (A2 ∈ F ∨ A2.card ≤ 1) →
        3 ≤ ((Hs F).filter (fun A => A ⊆ B1 ∪ B2)).card := by
      intro A1 A2 hu n1 n2 k1 k2
      have u1 : A1 ⊆ H := hu ▸ Finset.subset_union_left
      have u2 : A2 ⊆ H := hu ▸ Finset.subset_union_right
      rcases k2 with k2 | k2
      · refine three_le (hhelp H hHF hHM) (hhelp A1 k1 u1) (hhelp A2 k2 u2) n1.symm n2.symm ?_
        rintro rfl
        rw [Finset.union_self] at hu
        exact n1 hu
      · have hcu := Finset.card_union_le A1 A2
        rw [hu, hM] at hcu
        obtain ⟨-, C1, C2, hv, q1, q2, j1, j2⟩ := hF A1 k1
        have fin : ∀ D ∈ F, D ⊆ A1 → D ≠ A1 →
            3 ≤ ((Hs F).filter (fun A => A ⊆ B1 ∪ B2)).card := by
          intro D hD hDA hne
          refine three_le (hhelp H hHF hHM) (hhelp A1 k1 u1) (hhelp D hD (hDA.trans u1)) n1.symm ?_
            hne.symm
          rintro rfl
          exact n1 (Finset.Subset.antisymm u1 hDA)
        rcases j1 with j1 | j1
        · exact fin C1 j1 (hv ▸ Finset.subset_union_left) q1
        rcases j2 with j2 | j2
        · exact fin C2 j2 (hv ▸ Finset.subset_union_right) q2
        have hcv := Finset.card_union_le C1 C2
        rw [hv] at hcv
        omega
    rcases k1 with k1 | k1
    · exact main A1 A2 hu n1 n2 k1 k2
    rcases k2 with k2 | k2
    · exact main A2 A1 (by rw [Finset.union_comm]; exact hu) n2 n1 k2 (Or.inr k1)
    have hcu := Finset.card_union_le A1 A2
    rw [hu, hM] at hcu
    omega
  · obtain ⟨t, htM, htH⟩ : ∃ t ∈ M, t ∉ H := by
      by_contra hno
      push Not at hno
      exact hHe (Finset.Subset.antisymm hHM hno)
    have cH1 : c1 ∉ H := fun h => b1 (m2 (hHM h))
    have cH2 : c2 ∉ H := fun h => b2 (m1 (hHM h))
    have main : ∀ (B D : Finset (Fin 11)) (c : Fin 11), H ∪ D = B → D ≠ B →
        (D ∈ F ∨ D.card ≤ 1) → c ∈ B → c ∉ H → t ∈ B → c ≠ t → B ⊆ B1 ∪ B2 →
        (∀ l, Osum l ⊆ B → c ∈ Osum l → (∃ t ∈ M, t ∈ Osum l) → Osum l = B) →
        D ∈ (Hs F).filter (fun A => A ⊆ B1 ∪ B2) ∧ c ∈ D ∧ D ⊆ B := by
      intro B D c hu hne hD hcB hcH htB hct hBU hs
      have hin : ∀ a ∈ B, a ∉ H → a ∈ D := by
        intro a ha haH
        rw [← hu] at ha
        exact (Finset.mem_union.mp ha).resolve_left haH
      have hcD := hin c hcB hcH
      have htD := hin t htB htH
      have hDB : D ⊆ B := hu ▸ Finset.subset_union_right
      have hDF : D ∈ F := by
        refine hD.resolve_right fun hle => hct ?_
        exact Finset.card_le_one.mp hle c hcD t htD
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hDF, ?_⟩, hDB.trans hBU⟩, hcD, hDB⟩
      rintro l rfl
      exact hne (hs l hDB hcD ⟨t, htM, htD⟩)
    obtain ⟨D1, u1, n1, f1⟩ := d1
    obtain ⟨D2, u2, n2, f2⟩ := d2
    have r1 := main B1 D1 c1 u1 n1 f1 a1 cH1 (m1 htM) (fun h => b1 (m2 (h ▸ htM)))
      Finset.subset_union_left s1
    have r2 := main B2 D2 c2 u2 n2 f2 a2 cH2 (m2 htM) (fun h => b2 (m1 (h ▸ htM)))
      Finset.subset_union_right s2
    refine three_le (hhelp H hHF hHM) r1.1 r2.1 ?_ ?_ ?_
    · rintro rfl; exact cH1 r1.2.1
    · rintro rfl; exact cH2 r2.2.1
    · rintro rfl; exact b1 (r2.2.2 r1.2.1)

theorem osum_inj : Function.Injective Osum := by
  decide

theorem t2 (F : Finset (Finset (Fin 11))) (hO : ∀ l, Osum l ∈ F)
    (hF : ∀ A ∈ F, 2 ≤ A.card ∧ ∃ A1 A2, A1 ∪ A2 = A ∧ A1 ≠ A ∧ A2 ≠ A ∧
        (A1 ∈ F ∨ A1.card ≤ 1) ∧ (A2 ∈ F ∨ A2.card ≤ 1)) : 18 ≤ F.card := by
  have hF' : Dec F := hF
  obtain ⟨H0, h0, s0, r0⟩ := hlp hF' (hO 10) (e := 4) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨H1, h1, s1, r1⟩ := hlp hF' (hO 11) (e := 4) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨H2, h2, s2, r2⟩ := hlp hF' (hO 12) (e := 5) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨H3, h3, s3, r3⟩ := hlp hF' (hO 13) (e := 5) (by decide) (by decide) (by decide)
    (by decide)
  have m0 : (4 : Fin 11) ∈ H0 ∨ (0 : Fin 11) ∈ H0 := by
    rcases r0 with r | r
    · exact Or.inl r.1
    · rw [r]; exact Or.inr (by decide)
  have m1 : (4 : Fin 11) ∈ H1 ∨ (1 : Fin 11) ∈ H1 := by
    rcases r1 with r | r
    · exact Or.inl r.1
    · rw [r]; exact Or.inr (by decide)
  have m2 : (5 : Fin 11) ∈ H2 ∨ (2 : Fin 11) ∈ H2 := by
    rcases r2 with r | r
    · exact Or.inl r.1
    · rw [r]; exact Or.inr (by decide)
  have m3 : (5 : Fin 11) ∈ H3 ∨ (3 : Fin 11) ∈ H3 := by
    rcases r3 with r | r
    · exact Or.inl r.1
    · rw [r]; exact Or.inr (by decide)
  have out : ∀ {H B : Finset (Fin 11)} {a : Fin 11}, H ⊆ B → a ∉ B → a ∉ H :=
    fun hs ha h => ha (hs h)
  have hfour : 4 ≤ (Hs F).card := by
    by_cases e1 : H0 = H1
    · subst e1
      have x4 : (4 : Fin 11) ∈ H0 := m0.resolve_right (out s1 (by decide))
      have d0 := r0.resolve_right (fun h => by rw [h] at x4; exact absurd x4 (by decide))
      have d1 := r1.resolve_right (fun h => by rw [h] at x4; exact absurd x4 (by decide))
      have ht := tri hF' (B1 := Osum 10) (B2 := Osum 11) (M := {4, 6, 7, 8}) (c1 := 0) (c2 := 1)
        h0 (fun a ha => (show ∀ a, a ∈ Osum 10 → a ∈ Osum 11 →
          a ∈ ({4, 6, 7, 8} : Finset (Fin 11)) by decide) a (s0 ha) (s1 ha)) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) d0.2 d1.2
      have hn : H2 ∉ (Hs F).filter (fun A => A ⊆ Osum 10 ∪ Osum 11) := by
        intro hm
        have hs := (Finset.mem_filter.mp hm).2
        rcases m2 with h | h
        · exact absurd (hs h) (by decide)
        · exact absurd (hs h) (by decide)
      have : insert H2 ((Hs F).filter (fun A => A ⊆ Osum 10 ∪ Osum 11)) ⊆ Hs F :=
        Finset.insert_subset h2 (Finset.filter_subset _ _)
      have := Finset.card_le_card this
      rw [Finset.card_insert_of_notMem hn] at this
      omega
    by_cases e2 : H2 = H3
    · subst e2
      have x5 : (5 : Fin 11) ∈ H2 := m2.resolve_right (out s3 (by decide))
      have d2 := r2.resolve_right (fun h => by rw [h] at x5; exact absurd x5 (by decide))
      have d3 := r3.resolve_right (fun h => by rw [h] at x5; exact absurd x5 (by decide))
      have ht := tri hF' (B1 := Osum 12) (B2 := Osum 13) (M := {5, 6, 7, 8}) (c1 := 2) (c2 := 3)
        h2 (fun a ha => (show ∀ a, a ∈ Osum 12 → a ∈ Osum 13 →
          a ∈ ({5, 6, 7, 8} : Finset (Fin 11)) by decide) a (s2 ha) (s3 ha)) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) d2.2 d3.2
      have hn : H0 ∉ (Hs F).filter (fun A => A ⊆ Osum 12 ∪ Osum 13) := by
        intro hm
        have hs := (Finset.mem_filter.mp hm).2
        rcases m0 with h | h
        · exact absurd (hs h) (by decide)
        · exact absurd (hs h) (by decide)
      have : insert H0 ((Hs F).filter (fun A => A ⊆ Osum 12 ∪ Osum 13)) ⊆ Hs F :=
        Finset.insert_subset h0 (Finset.filter_subset _ _)
      have := Finset.card_le_card this
      rw [Finset.card_insert_of_notMem hn] at this
      omega
    have n02 : H0 ≠ H2 := by
      rintro rfl
      rcases m0 with h | h
      · exact out s2 (by decide) h
      · exact out s2 (by decide) h
    have n03 : H0 ≠ H3 := by
      rintro rfl
      rcases m0 with h | h
      · exact out s3 (by decide) h
      · exact out s3 (by decide) h
    have n12 : H1 ≠ H2 := by
      rintro rfl
      rcases m1 with h | h
      · exact out s2 (by decide) h
      · exact out s2 (by decide) h
    have n13 : H1 ≠ H3 := by
      rintro rfl
      rcases m1 with h | h
      · exact out s3 (by decide) h
      · exact out s3 (by decide) h
    have hsub : insert H0 ({H1, H2, H3} : Finset (Finset (Fin 11))) ⊆ Hs F := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [e1, n02, n03]),
      Finset.card_insert_of_notMem (by simp [n12, n13]), Finset.card_pair e2] at hc
    exact hc
  have hdis : Disjoint (Finset.univ.image Osum) (Hs F) := by
    rw [Finset.disjoint_left]
    intro A hA hA'
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hA
    exact (Finset.mem_filter.mp hA').2 l rfl
  have hsub : Finset.univ.image Osum ∪ Hs F ⊆ F := by
    intro A hA
    rcases Finset.mem_union.mp hA with h | h
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h
      exact hO l
    · exact (Finset.mem_filter.mp h).1
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ osum_inj,
    Finset.card_univ, Fintype.card_fin] at h
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem runW_length (gs : List Gate) : ∀ w, (runW gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [runW]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [runW, List.foldl_cons, List.length_cons, List.length_append, List.length_nil]
      at this ⊢
    omega

theorem runW_getD (gs : List Gate) : ∀ w i, i < w.length →
    (runW gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i
      (by rw [List.length_append]; omega)
    rw [show runW (g :: gs) w =
      runW gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) from rfl, this]
    rw [List.getD_append _ _ _ _ hi]

theorem runW_gate (gs : List Gate) : ∀ w j (hj : j < gs.length),
    (runW gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (runW (gs.take j) w).getD i false) := by
  induction gs with
  | nil => intro w j hj; simp at hj
  | cons g gs ih =>
    intro w j hj
    rw [show runW (g :: gs) w =
      runW gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) from rfl]
    rcases j with _ | j
    · rw [runW_getD _ _ _ (by simp)]
      simp [runW]
    · have hj' : j < gs.length := by simpa using hj
      have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) j hj'
      rw [List.length_append, List.length_singleton] at this
      rw [show w.length + (j + 1) = w.length + 1 + j by omega, this]
      rfl

theorem wires_length (D : Circuit) (x : List Bool) :
    (D.wires x).length = x.length + D.gates.length := by
  exact runW_length D.gates x

theorem wires_input (D : Circuit) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (D.wires x).getD i false = x.getD i false := by
  exact runW_getD D.gates x i hi

theorem wires_gate {n : ℕ} {D : Circuit} (hR : ReadsBack n D) (x : List Bool)
    (hx : x.length = n) {j : ℕ} (hj : j < D.gates.length) :
    (D.wires x).getD (n + j) false =
      (gateAt D j).op.eval ((gateAt D j).inputs.map fun i => (D.wires x).getD i false) := by
  have hg : gateAt D j = D.gates[j] := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
  have h := runW_gate D.gates x j hj
  rw [hx] at h
  rw [hg]
  refine h.trans ?_
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < n + j := by
    have := hR j hj i
    rw [hg] at this
    exact this hi
  have hlen : (runW (D.gates.take j) x).length = n + j := by
    rw [runW_length, hx, List.length_take, Nat.min_eq_left hj.le]
  have e : runW D.gates x = runW (D.gates.drop j) (runW (D.gates.take j) x) := by
    unfold runW
    rw [← List.foldl_append, List.take_append_drop]
  show _ = (runW D.gates x).getD i false
  rw [e, runW_getD (D.gates.drop j) (runW (D.gates.take j) x) i (by rw [hlen]; exact hi')]

theorem bridge_in {V : Type} {n : ℕ} (enc : V → Option (Fin n))
    (hinj : ∀ u v q, enc u = some q → enc v = some q → u = v) (hne : ∃ v q, enc v = some q)
    (f : Set V → Prop) (hf : ∃ ρ, f ρ) (D : Circuit) (hM : Monotone2 D) (hR : ReadsBack n D)
    (hD : ∀ ρ : Set V, circuitFun n D (fun q => decide (∃ v ∈ ρ, enc v = some q)) = true ↔ f ρ)
    (hcl : ∀ v q, enc v = some q → ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      (D.wires (List.ofFn (fun k : Fin n => decide (k = q)))).getD (n + j) false = false) :
    ∃ C : Ckt V, Wf C ∧ Clean C ∧ (∀ ρ, C.val ρ C.out ↔ f ρ) ∧ C.G.card ≤ D.size := by
  have hlen : ∀ z : Fin n → Bool, (List.ofFn z).length = n := fun z => List.length_ofFn
  let inp : Set V → List Bool := fun ρ => List.ofFn (fun q => decide (∃ v ∈ ρ, enc v = some q))
  have hinp : ∀ (ρ : Set V) (q : ℕ) (hq : q < n), (inp ρ).getD q false = true ↔
      ∃ v ∈ ρ, enc v = some ⟨q, hq⟩ := by
    intro ρ q hq
    have : (inp ρ).getD q false = decide (∃ v ∈ ρ, enc v = some ⟨q, hq⟩) := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hq)]
      simp [inp]
    rw [this, decide_eq_true_eq]
  let W : Set V → ℕ → Bool := fun ρ q => (D.wires (inp ρ)).getD q false
  have hWin : ∀ ρ q (hq : q < n), W ρ q = true ↔ ∃ v ∈ ρ, enc v = some ⟨q, hq⟩ := by
    intro ρ q hq
    rw [← hinp ρ q hq]
    show (D.wires (inp ρ)).getD q false = true ↔ _
    rw [wires_input D _ (by rw [hlen]; exact hq)]
  have hWg : ∀ ρ j, j < D.gates.length → W ρ (n + j) =
      (gateAt D j).op.eval ((gateAt D j).inputs.map fun i => W ρ i) := fun ρ j hj =>
    wires_gate hR _ (hlen _) hj
  have hWbig : ∀ ρ q, n + D.gates.length ≤ q → W ρ q = false := by
    intro ρ q hq
    show (D.wires (inp ρ)).getD q false = false
    rw [List.getD_eq_default]
    rw [wires_length, hlen]
    exact hq
  have hclv : ∀ v q, enc v = some q → ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      W {v} (n + j) = false := by
    intro v q hv j hj ho
    have : inp {v} = List.ofFn (fun k : Fin n => decide (k = q)) := by
      show List.ofFn _ = List.ofFn _
      congr 1
      funext k
      rw [decide_eq_decide]
      constructor
      · rintro ⟨u, hu, he⟩
        rw [Set.mem_singleton_iff.mp hu, hv] at he
        exact (Option.some.inj he).symm
      · rintro rfl
        exact ⟨v, rfl, hv⟩
    show (D.wires (inp {v})).getD (n + j) false = false
    rw [this]
    exact hcl v q hv j hj ho
  have hgmem : ∀ j < D.gates.length, gateAt D j ∈ D.gates := by
    intro j hj
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  let Off : ℕ → Prop := fun q => ∀ ρ, W ρ q = false
  have hon : ∀ {q}, ¬ Off q → ∃ ρ, W ρ q = true := by
    intro q h
    by_contra hno
    push Not at hno
    exact h fun ρ => by simpa using hno ρ
  have hnoff : ∀ {q ρ}, W ρ q = true → ¬ Off q := by
    intro q ρ h ho
    rw [ho ρ] at h
    cases h
  obtain ⟨v0, q0, hv0⟩ := hne
  have hbd : ∀ {q}, ¬ Off q → q < n + D.gates.length := by
    intro q h
    by_contra hge
    exact h fun ρ => hWbig ρ q (by omega)
  let op : ℕ → Bool := fun k => decide ((gateAt D k).op = GateOp.and)
  have hgate : ∀ k, ∃ a b, k < D.gates.length → ¬ Off (n + k) → (a < n + k ∧ b < n + k ∧
      ¬ Off a ∧ ¬ Off b ∧ ∀ ρ, W ρ (n + k) = true ↔
        if op k = true then W ρ a = true ∧ W ρ b = true else W ρ a = true ∨ W ρ b = true) := by
    intro k
    by_cases hk : k < D.gates.length ∧ ¬ Off (n + k)
    swap
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
    obtain ⟨hk, hkoff⟩ := hk
    have hm := hM _ (hgmem k hk)
    have hrb := hR k hk
    have hw := fun ρ => hWg ρ k hk
    obtain ⟨ρ0, h0⟩ := hon hkoff
    have hop : (gateAt D k).op = GateOp.and ∨ (gateAt D k).op = GateOp.or := by
      simpa using hm.1
    rcases hins : (gateAt D k).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · exfalso
      rcases hop with ho | ho
      · have h1 := hclv v0 q0 hv0 k hk ho
        rw [hw, hins, ho] at h1
        simp [GateOp.eval] at h1
      · rw [hw, hins, ho] at h0
        simp [GateOp.eval] at h0
    · have hw' : ∀ ρ, W ρ (n + k) = W ρ a := by
        intro ρ
        rw [hw, hins]
        rcases hop with ho | ho <;> rw [ho] <;> simp [GateOp.eval]
      have ha : ¬ Off a := hnoff (by rw [← hw']; exact h0)
      refine ⟨a, a, fun _ _ => ⟨hrb a (by simp [hins]), hrb a (by simp [hins]), ha, ha, fun ρ => ?_⟩⟩
      rw [hw']
      split_ifs <;> simp
    · have hla := hrb a (by simp [hins])
      have hlb := hrb b (by simp [hins])
      rcases hop with ho | ho
      · have hw' : ∀ ρ, W ρ (n + k) = true ↔ W ρ a = true ∧ W ρ b = true := by
          intro ρ
          rw [hw, hins, ho]
          simp [GateOp.eval]
        have h1 := (hw' ρ0).mp h0
        refine ⟨a, b, fun _ _ => ⟨hla, hlb, hnoff h1.1, hnoff h1.2, fun ρ => ?_⟩⟩
        rw [hw', if_pos (by simp [op, ho])]
      · have hw' : ∀ ρ, W ρ (n + k) = true ↔ W ρ a = true ∨ W ρ b = true := by
          intro ρ
          rw [hw, hins, ho]
          simp [GateOp.eval]
        have hop' : ¬ op k = true := by simp [op, ho]
        by_cases ha : Off a
        · have hb : ¬ Off b := by
            rcases (hw' ρ0).mp h0 with h | h
            · rw [ha ρ0] at h; cases h
            · exact hnoff h
          refine ⟨b, b, fun _ _ => ⟨hlb, hlb, hb, hb, fun ρ => ?_⟩⟩
          rw [hw', if_neg hop', ha ρ]
          simp
        · by_cases hb : Off b
          · refine ⟨a, a, fun _ _ => ⟨hla, hla, ha, ha, fun ρ => ?_⟩⟩
            rw [hw', if_neg hop', hb ρ]
            simp
          · refine ⟨a, b, fun _ _ => ⟨hla, hlb, ha, hb, fun ρ => ?_⟩⟩
            rw [hw', if_neg hop']
    · exfalso
      have := hm.2
      rw [hins] at this
      simp at this
  choose a b hab using hgate
  let m : ℕ → V ⊕ ℕ := fun q => if h : q < n then
    (if h' : ∃ v, enc v = some ⟨q, h⟩ then Sum.inl h'.choose else Sum.inl v0) else Sum.inr (q - n)
  let G : Finset ℕ := (Finset.range D.gates.length).filter (fun k => ¬ Off (n + k))
  have hG : ∀ k, k ∈ G ↔ k < D.gates.length ∧ ¬ Off (n + k) := by
    intro k; simp [G]
  let C : Ckt V := Ckt.mk G op (fun k => m (a k)) (fun k => m (b k)) (m D.output)
  have hmvl : ∀ q, ¬ Off q → Vl C (m q) := by
    intro q hq k hk
    by_cases h : q < n
    · simp only [m, dif_pos h] at hk
      split_ifs at hk
    · simp only [m, dif_neg h] at hk
      have hk' := Sum.inr.inj hk
      have := hbd hq
      refine (hG k).mpr ⟨by omega, ?_⟩
      rwa [show n + k = q by omega]
  have hmrk : ∀ q, rk (m q) ≤ q - n + 1 ∧ (q < n → rk (m q) = 0) := by
    intro q
    by_cases h : q < n
    · simp only [m, dif_pos h]
      split_ifs <;> simp [rk]
    · simp only [m, dif_neg h]
      simp [rk, h]
  have hmrk' : ∀ q k, q < n + k → rk (m q) ≤ k := by
    intro q k hq
    rcases Nat.lt_or_ge q n with h | h
    · rw [(hmrk q).2 h]; omega
    · have := (hmrk q).1; omega
  have hout : ¬ Off D.output := by
    obtain ⟨ρ, hρ⟩ := hf
    exact hnoff ((hD ρ).mpr hρ)
  have hCW : Wf C := by
    refine ⟨fun k hk => ?_, hmvl _ hout⟩
    obtain ⟨hk1, hk2⟩ := (hG k).mp hk
    have h := hab k hk1 hk2
    exact ⟨⟨hmvl _ h.2.2.1, hmrk' _ _ h.1⟩, ⟨hmvl _ h.2.2.2.1, hmrk' _ _ h.2.1⟩⟩
  have hval : ∀ ρ q, ¬ Off q → (C.val ρ (m q) ↔ W ρ q = true) := by
    intro ρ q
    induction q using Nat.strong_induction_on with
    | _ q ih =>
      intro hq
      by_cases h : q < n
      · rw [hWin ρ q h]
        have hex : ∃ v, enc v = some ⟨q, h⟩ := by
          obtain ⟨σ, hσ⟩ := hon hq
          obtain ⟨v, -, hv⟩ := (hWin σ q h).mp hσ
          exact ⟨v, hv⟩
        simp only [m, dif_pos h, dif_pos hex]
        constructor
        · intro hv
          exact ⟨_, hv, hex.choose_spec⟩
        · rintro ⟨v, hv, he⟩
          have := hinj _ _ _ hex.choose_spec he
          show hex.choose ∈ ρ
          rw [this]; exact hv
      · have hb := hbd hq
        have hk : n + (q - n) = q := by omega
        have hkG : q - n ∈ G := (hG _).mpr ⟨by omega, by rwa [hk]⟩
        obtain ⟨hk1, hk2⟩ := (hG _).mp hkG
        have hh := hab (q - n) hk1 hk2
        have e : m q = Sum.inr (q - n) := by simp only [m, dif_neg h]
        rw [e, val_gate hCW hkG]
        have h1 := ih (a (q - n)) (by omega) hh.2.2.1
        have h2 := ih (b (q - n)) (by omega) hh.2.2.2.1
        have h3 := hh.2.2.2.2 ρ
        rw [hk] at h3
        rw [h3]
        show (if op (q - n) = true then C.val ρ (m (a (q - n))) ∧ C.val ρ (m (b (q - n)))
          else C.val ρ (m (a (q - n))) ∨ C.val ρ (m (b (q - n)))) ↔ _
        split_ifs
        · exact and_congr h1 h2
        · exact or_congr h1 h2
  refine ⟨C, hCW, ?_, fun ρ => (hval ρ _ hout).trans (hD ρ), ?_⟩
  · intro k hk ho v hv
    obtain ⟨hk1, hk2⟩ := (hG k).mp hk
    have hmk : m (n + k) = Sum.inr k := by
      simp only [m, dif_neg (show ¬ n + k < n by omega)]
      rw [Nat.add_sub_cancel_left]
    have hW := (hval {v} (n + k) hk2).mp (by rw [hmk]; exact hv)
    have ho' : (gateAt D k).op = GateOp.and := by
      have : op k = true := ho
      simpa [op] using this
    rcases he : enc v with _ | q
    · have : inp {v} = inp ∅ := by
        show List.ofFn _ = List.ofFn _
        congr 1
        funext q
        rw [decide_eq_decide]
        constructor
        · rintro ⟨u, hu, hq⟩
          rw [Set.mem_singleton_iff.mp hu, he] at hq
          cases hq
        · rintro ⟨u, hu, -⟩
          exact hu.elim
      have h2 : W ∅ (n + k) = true := by
        show (D.wires (inp ∅)).getD (n + k) false = true
        rw [← this]; exact hW
      have h3 := (hval ∅ (n + k) hk2).mpr h2
      rw [hmk] at h3
      exact val_empty hCW _ (vl_inr hk) h3
    · rw [hclv v q he k hk1 ho'] at hW
      cases hW
  · exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range]; exact le_rfl)

def NN (T : ℕ) : ℕ := 11 + 42 * T

def Irel (T : ℕ) (p q : Fin (NN T)) : Prop :=
  ∃ n < 14 * T, ∃ e < 2, q.val = 2 * n + e ∧
    ((∃ a : Fin 11, p.val = a.val ∧ a ∈ Osum ⟨n % 14, Nat.mod_lt _ (by norm_num)⟩) ∨
      p.val = 11 + 3 * n ∨ p.val = 11 + 3 * n + 1 + e)

def coreG (b : ℕ) : ℕ → Gate
  | 0 => ⟨GateOp.or, [0, 9]⟩
  | 1 => ⟨GateOp.or, [1, 10]⟩
  | 2 => ⟨GateOp.or, [2, 9]⟩
  | 3 => ⟨GateOp.or, [3, 10]⟩
  | 4 => ⟨GateOp.or, [6, 9]⟩
  | 5 => ⟨GateOp.or, [b + 4, 7]⟩
  | 6 => ⟨GateOp.or, [b + 5, 8]⟩
  | 7 => ⟨GateOp.or, [6, 10]⟩
  | 8 => ⟨GateOp.or, [b + 7, 7]⟩
  | 9 => ⟨GateOp.or, [b + 8, 8]⟩
  | 10 => ⟨GateOp.and, [b + 6, b + 9]⟩
  | 11 => ⟨GateOp.or, [b + 10, 4]⟩
  | 12 => ⟨GateOp.or, [b + 10, 5]⟩
  | 13 => ⟨GateOp.or, [b + 11, b + 0]⟩
  | 14 => ⟨GateOp.or, [b + 11, b + 1]⟩
  | 15 => ⟨GateOp.or, [b + 12, b + 2]⟩
  | _ => ⟨GateOp.or, [b + 12, b + 3]⟩

def osw (l : ℕ) : ℕ := if l < 10 then l else l + 3

def bet (n : ℕ) : ℕ := if n = 0 then 17 else 16 + 7 * n

def blockG (N n : ℕ) : ℕ → Gate
  | 0 => ⟨GateOp.or, [11 + 3 * n, N + N + osw (n % 14)]⟩
  | 1 => ⟨GateOp.or, [N + N + bet n, 11 + 3 * n + 1]⟩
  | 2 => ⟨GateOp.or, [N + N + bet n, 11 + 3 * n + 2]⟩
  | 3 => ⟨GateOp.and, [N + 2 * n, N + N + (bet n + 1)]⟩
  | 4 => ⟨GateOp.and, [N + (2 * n + 1), N + N + (bet n + 2)]⟩
  | 5 => if n = 0 then ⟨GateOp.or, [N + N + (bet n + 3), N + N + (bet n + 4)]⟩
      else ⟨GateOp.or, [N + N + (15 + 7 * n), N + N + (bet n + 3)]⟩
  | _ => ⟨GateOp.or, [N + N + (bet n + 5), N + N + (bet n + 4)]⟩

def gf (N j : ℕ) : Gate :=
  if j < 17 then coreG (N + N) j
  else if j < 23 then blockG N 0 (j - 17) else blockG N ((j - 16) / 7) ((j - 16) % 7)

def upC (T : ℕ) : Circuit :=
  ⟨(List.range (7 * (14 * T) + 16)).map (gf (NN T)), NN T + NN T + (7 * (14 * T) + 15)⟩

theorem gf_bet (N n t : ℕ) (ht : t < 7) (h0 : n = 0 → t < 6) : gf N (bet n + t) = blockG N n t := by
  unfold gf bet
  by_cases hn : n = 0
  · subst hn
    have := h0 rfl
    rw [if_neg (by simp), if_pos (by simp; omega)]
    simp
  · rw [if_neg hn, if_neg (by omega), if_neg (by omega)]
    rw [show (16 + 7 * n + t - 16) / 7 = n by omega, show (16 + 7 * n + t - 16) % 7 = t by omega]

theorem coreG_ok (b j : ℕ) (hj : j < 17) (hb : 11 ≤ b) :
    ((coreG b j).op = GateOp.and ∨ (coreG b j).op = GateOp.or) ∧ (coreG b j).inputs.length ≤ 2 ∧
      ∀ i ∈ (coreG b j).inputs, i < b + j := by
  interval_cases j <;> simp [coreG] <;> omega

theorem blockG_ok (N n t : ℕ) (hN : 11 + 3 * n + 2 < N + N) (hN2 : N + (2 * n + 1) < N + N)
    (ht : t < 7) (h0 : n = 0 → t < 6) :
    ((blockG N n t).op = GateOp.and ∨ (blockG N n t).op = GateOp.or) ∧
      (blockG N n t).inputs.length ≤ 2 ∧ ∀ i ∈ (blockG N n t).inputs, i < N + N + (bet n + t) := by
  have hos : osw (n % 14) < 17 := by
    unfold osw
    have := Nat.mod_lt n (show 0 < 14 by norm_num)
    split_ifs <;> omega
  have hbet : 17 ≤ bet n := by
    unfold bet
    split_ifs <;> omega
  have hb2 : n ≠ 0 → bet n = 16 + 7 * n := fun h => if_neg h
  interval_cases t
  · simp [blockG]; omega
  · simp [blockG]; omega
  · simp [blockG]; omega
  · simp [blockG]; omega
  · simp [blockG]; omega
  · by_cases hn : n = 0
    · simp [blockG, hn]
    · have := hb2 hn
      simp [blockG, hn]; omega
  · simp [blockG]

theorem idx (M j : ℕ) (hM : 1 ≤ M) (hj : j < 7 * M + 16) : j < 17 ∨ ∃ n t, n < M ∧ t < 7 ∧
    (n = 0 → t < 6) ∧ j = bet n + t := by
  by_cases h1 : j < 17
  · exact Or.inl h1
  · right
    by_cases h2 : j < 23
    · exact ⟨0, j - 17, by omega, by omega, by omega, by simp [bet]; omega⟩
    · refine ⟨(j - 16) / 7, (j - 16) % 7, by omega, by omega, by omega, ?_⟩
      unfold bet
      rw [if_neg (by omega)]
      omega

theorem core_bool (p u a b c y z : Bool) :
    (((a || y || b || c) && (a || z || b || c) || u || (p || y)) = true) ↔
      (p = true ∨ u = true ∨ a = true ∨ b = true ∨ c = true ∨ y = true) := by
  have h : ((a || y || b || c) && (a || z || b || c) || u || (p || y)) =
      (p || u || a || b || c || y) := by
    cases p <;> cases u <;> cases a <;> cases b <;> cases c <;> cases y <;> cases z <;> rfl
  rw [h]
  simp [or_assoc]

theorem sum_core (W : ℕ → Bool) (b : ℕ) (c0 : W (b + 0) = (W 0 || W 9))
    (c1 : W (b + 1) = (W 1 || W 10)) (c2 : W (b + 2) = (W 2 || W 9))
    (c3 : W (b + 3) = (W 3 || W 10)) (c4 : W (b + 4) = (W 6 || W 9))
    (c5 : W (b + 5) = (W 6 || W 9 || W 7)) (c6 : W (b + 6) = (W 6 || W 9 || W 7 || W 8))
    (c7 : W (b + 7) = (W 6 || W 10)) (c8 : W (b + 8) = (W 6 || W 10 || W 7))
    (c9 : W (b + 9) = (W 6 || W 10 || W 7 || W 8))
    (c13 : W (b + 13) = ((W 6 || W 9 || W 7 || W 8) && (W 6 || W 10 || W 7 || W 8) || W 4 ||
      (W 0 || W 9)))
    (c14 : W (b + 14) = ((W 6 || W 9 || W 7 || W 8) && (W 6 || W 10 || W 7 || W 8) || W 4 ||
      (W 1 || W 10)))
    (c15 : W (b + 15) = ((W 6 || W 9 || W 7 || W 8) && (W 6 || W 10 || W 7 || W 8) || W 5 ||
      (W 2 || W 9)))
    (c16 : W (b + 16) = ((W 6 || W 9 || W 7 || W 8) && (W 6 || W 10 || W 7 || W 8) || W 5 ||
      (W 3 || W 10))) :
    ∀ l : Fin 14, W (b + osw l.val) = true ↔ ∃ a ∈ Osum l, W a.val = true := by
  have ex : ∀ l : Fin 14, (∃ a ∈ Osum l, W a.val = true) ↔
      ((0 ∈ Osum l ∧ W 0 = true) ∨ (1 ∈ Osum l ∧ W 1 = true) ∨ (2 ∈ Osum l ∧ W 2 = true) ∨
      (3 ∈ Osum l ∧ W 3 = true) ∨ (4 ∈ Osum l ∧ W 4 = true) ∨ (5 ∈ Osum l ∧ W 5 = true) ∨
      (6 ∈ Osum l ∧ W 6 = true) ∨ (7 ∈ Osum l ∧ W 7 = true) ∨ (8 ∈ Osum l ∧ W 8 = true) ∨
      (9 ∈ Osum l ∧ W 9 = true) ∨ (10 ∈ Osum l ∧ W 10 = true)) := by
    intro l
    simp only [Fin.exists_fin_succ, Fin.exists_fin_zero]
    simp [Fin.ext_iff]
  intro l
  rw [ex]
  have hv : W (b + osw l.val) = ![W (b + 0), W (b + 1), W (b + 2), W (b + 3), W (b + 4), W (b + 5),
      W (b + 6), W (b + 7), W (b + 8), W (b + 9), W (b + 13), W (b + 14), W (b + 15),
      W (b + 16)] l := by
    fin_cases l <;> rfl
  rw [hv, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c13, c14, c15, c16]
  clear hv ex c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c13 c14 c15 c16
  generalize W 0 = x0
  generalize W 1 = x1
  generalize W 2 = x2
  generalize W 3 = x3
  generalize W 4 = x4
  generalize W 5 = x5
  generalize W 6 = x6
  generalize W 7 = x7
  generalize W 8 = x8
  generalize W 9 = x9
  generalize W 10 = x10
  clear W b
  fin_cases l
  · simp [Osum]
  · simp [Osum]
  · simp [Osum]
  · simp [Osum]
  · simp [Osum]
  · cases x6 <;> cases x7 <;> cases x9 <;> simp [Osum]
  · cases x6 <;> cases x7 <;> cases x8 <;> cases x9 <;> simp [Osum]
  · simp [Osum]
  · cases x6 <;> cases x7 <;> cases x10 <;> simp [Osum]
  · cases x6 <;> cases x7 <;> cases x8 <;> cases x10 <;> simp [Osum]
  · have h := core_bool x0 x4 x6 x7 x8 x9 x10
    simpa [Osum] using h
  · have h := core_bool x1 x4 x6 x7 x8 x10 x9
    rw [Bool.and_comm] at h
    simpa [Osum] using h
  · have h := core_bool x2 x5 x6 x7 x8 x9 x10
    simpa [Osum] using h
  · have h := core_bool x3 x5 x6 x7 x8 x10 x9
    rw [Bool.and_comm] at h
    simpa [Osum] using h

theorem upper (T : ℕ) (hT : 1 ≤ T) : ∃ C : Circuit, Monotone2 C ∧ ReadsBack (NN T + NN T) C ∧
    (∀ z : Fin (NN T + NN T) → Bool, circuitFun (NN T + NN T) C z = true ↔
      ∃ p l : Fin (NN T), Irel T p l ∧ z (Fin.castAdd (NN T) p) = true ∧
        z (Fin.natAdd (NN T) l) = true) ∧ C.size = 7 * (14 * T) + 16 := by
  have hN : NN T = 11 + 42 * T := rfl
  have hlen : (upC T).gates.length = 7 * (14 * T) + 16 := by simp [upC]
  have hgate : ∀ j, j < 7 * (14 * T) + 16 → gateAt (upC T) j = gf (NN T) j := by
    intro j hj
    unfold gateAt
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hj)]
    simp [upC]
  have hok : ∀ j, j < 7 * (14 * T) + 16 →
      ((gf (NN T) j).op = GateOp.and ∨ (gf (NN T) j).op = GateOp.or) ∧
      (gf (NN T) j).inputs.length ≤ 2 ∧ ∀ i ∈ (gf (NN T) j).inputs, i < NN T + NN T + j := by
    intro j hj
    rcases idx (14 * T) j (by omega) hj with h | ⟨n, t, hn, ht, h0, rfl⟩
    · have : gf (NN T) j = coreG (NN T + NN T) j := if_pos h
      rw [this]
      exact coreG_ok _ j h (by omega)
    · rw [gf_bet _ _ _ ht h0]
      exact blockG_ok _ n t (by omega) (by omega) ht h0
  have hRB : ReadsBack (NN T + NN T) (upC T) := by
    intro j hj i hi
    rw [hlen] at hj
    rw [hgate j hj] at hi
    exact (hok j hj).2.2 i hi
  refine ⟨upC T, ?_, hRB, ?_, hlen⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    have := hok j (List.mem_range.mp hj)
    exact ⟨by simpa using this.1, this.2.1⟩
  · intro z
    let W : ℕ → Bool := fun q => ((upC T).wires (List.ofFn z)).getD q false
    have hzl : (List.ofFn z).length = NN T + NN T := List.length_ofFn
    have hWin : ∀ q (hq : q < NN T + NN T), W q = z ⟨q, hq⟩ := by
      intro q hq
      show ((upC T).wires (List.ofFn z)).getD q false = _
      rw [wires_input _ _ (by rw [hzl]; exact hq), List.getD_eq_getElem _ _ (by rw [hzl]; exact hq)]
      simp
    have hWg : ∀ j, j < 7 * (14 * T) + 16 → W (NN T + NN T + j) =
        (gf (NN T) j).op.eval ((gf (NN T) j).inputs.map W) := by
      intro j hj
      have := wires_gate hRB (List.ofFn z) hzl (j := j) (by rw [hlen]; exact hj)
      rw [hgate j hj] at this
      exact this
    have hcore : ∀ j, j < 17 → W (NN T + NN T + j) =
        (coreG (NN T + NN T) j).op.eval ((coreG (NN T + NN T) j).inputs.map W) := by
      intro j hj
      rw [hWg j (by omega), show gf (NN T) j = coreG (NN T + NN T) j from if_pos hj]
    have hsum : ∀ l : Fin 14, W (NN T + NN T + osw l.val) = true ↔
        ∃ a ∈ Osum l, W a.val = true := by
      have c0 := hcore 0 (by norm_num)
      have c1 := hcore 1 (by norm_num)
      have c2 := hcore 2 (by norm_num)
      have c3 := hcore 3 (by norm_num)
      have c4 := hcore 4 (by norm_num)
      have c5 := hcore 5 (by norm_num)
      have c6 := hcore 6 (by norm_num)
      have c7 := hcore 7 (by norm_num)
      have c8 := hcore 8 (by norm_num)
      have c9 := hcore 9 (by norm_num)
      have c10 := hcore 10 (by norm_num)
      have c11 := hcore 11 (by norm_num)
      have c12 := hcore 12 (by norm_num)
      have c13 := hcore 13 (by norm_num)
      have c14 := hcore 14 (by norm_num)
      have c15 := hcore 15 (by norm_num)
      have c16 := hcore 16 (by norm_num)
      simp only [coreG, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
      rw [c0, c11] at c13
      rw [c1, c11] at c14
      rw [c2, c12] at c15
      rw [c3, c12] at c16
      rw [c4] at c5
      rw [c5] at c6
      rw [c7] at c8
      rw [c8] at c9
      rw [c6, c9] at c10
      rw [c10] at c13 c14 c15 c16
      exact sum_core W _ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c13 c14 c15 c16
    have hblk : ∀ n t, n < 14 * T → t < 7 → (n = 0 → t < 6) → W (NN T + NN T + (bet n + t)) =
        (blockG (NN T) n t).op.eval ((blockG (NN T) n t).inputs.map W) := by
      intro n t hn ht h0
      have hlt : bet n + t < 7 * (14 * T) + 16 := by
        unfold bet
        split_ifs with h
        · have := h0 h; omega
        · omega
      rw [hWg _ hlt, gf_bet _ _ _ ht h0]
    let A : ℕ → ℕ → Prop := fun n e => W (NN T + (2 * n + e)) = true ∧
      (W (11 + 3 * n) = true ∨ (∃ a ∈ Osum ⟨n % 14, Nat.mod_lt _ (by norm_num)⟩, W a.val = true) ∨
        W (11 + 3 * n + 1 + e) = true)
    have hand : ∀ n, n < 14 * T → (W (NN T + NN T + (bet n + 3)) = true ↔ A n 0) ∧
        (W (NN T + NN T + (bet n + 4)) = true ↔ A n 1) := by
      intro n hn
      have b0 := hblk n 0 hn (by norm_num) (by intro; norm_num)
      have b1 := hblk n 1 hn (by norm_num) (by intro; norm_num)
      have b2 := hblk n 2 hn (by norm_num) (by intro; norm_num)
      have b3 := hblk n 3 hn (by norm_num) (by intro; norm_num)
      have b4 := hblk n 4 hn (by norm_num) (by intro; norm_num)
      simp only [blockG, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true, Nat.add_zero] at b0 b1 b2 b3 b4
      have hs := hsum ⟨n % 14, Nat.mod_lt _ (by norm_num)⟩
      simp only at hs
      rw [b3, b4, b1, b2, b0]
      simp only [A, Bool.and_eq_true, Bool.or_eq_true, hs, Nat.add_zero]
      constructor
      · rw [or_assoc]
      · rw [or_assoc]
    have hacc : ∀ n, n < 14 * T → (W (NN T + NN T + (22 + 7 * n)) = true ↔
        ∃ k ≤ n, A k 0 ∨ A k 1) := by
      intro n
      induction n with
      | zero =>
        intro hn
        have b5 := hblk 0 5 hn (by norm_num) (by intro; norm_num)
        simp only [blockG, if_true, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
          List.any_nil, id, Bool.or_false] at b5
        have e : bet 0 + 5 = 22 + 7 * 0 := by simp [bet]
        rw [e] at b5
        rw [b5, Bool.or_eq_true, (hand 0 hn).1, (hand 0 hn).2]
        constructor
        · intro h; exact ⟨0, le_rfl, h⟩
        · rintro ⟨k, hk, h⟩
          rw [Nat.le_zero.mp hk] at h
          exact h
      | succ n ih =>
        intro hn
        have b5 := hblk (n + 1) 5 hn (by norm_num) (by intro; norm_num)
        have b6 := hblk (n + 1) 6 hn (by norm_num) (by intro h; omega)
        simp only [blockG, if_neg (Nat.succ_ne_zero n), GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id, Bool.or_false] at b5 b6
        have e : bet (n + 1) + 6 = 22 + 7 * (n + 1) := by
          unfold bet
          rw [if_neg (Nat.succ_ne_zero n)]
          omega
        have e' : 15 + 7 * (n + 1) = 22 + 7 * n := by omega
        rw [e] at b6
        rw [e'] at b5
        rw [b6, b5, Bool.or_eq_true, Bool.or_eq_true, ih (by omega), (hand _ hn).1, (hand _ hn).2]
        constructor
        · rintro ((⟨k, hk, h⟩ | h) | h)
          · exact ⟨k, by omega, h⟩
          · exact ⟨n + 1, le_rfl, Or.inl h⟩
          · exact ⟨n + 1, le_rfl, Or.inr h⟩
        · rintro ⟨k, hk, h⟩
          rcases Nat.lt_or_ge k (n + 1) with hlt | hge
          · exact Or.inl (Or.inl ⟨k, by omega, h⟩)
          · rw [show k = n + 1 by omega] at h
            rcases h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
    have hev : circuitFun (NN T + NN T) (upC T) z = W (NN T + NN T + (22 + 7 * (14 * T - 1))) := by
      show ((upC T).wires (List.ofFn z)).getD (NN T + NN T + (7 * (14 * T) + 15)) false = _
      rw [show 7 * (14 * T) + 15 = 22 + 7 * (14 * T - 1) by omega]
    rw [hev, hacc _ (by omega)]
    constructor
    · rintro ⟨n, hn, h⟩
      obtain ⟨e, he, hA⟩ : ∃ e < 2, A n e := by
        rcases h with h | h
        · exact ⟨0, by norm_num, h⟩
        · exact ⟨1, by norm_num, h⟩
      obtain ⟨hy, hx⟩ := hA
      have hline : 2 * n + e < NN T := by omega
      rw [hWin _ (by omega)] at hy
      rcases hx with hx | ⟨a, ha, hx⟩ | hx
      · rw [hWin _ (by omega)] at hx
        exact ⟨⟨11 + 3 * n, by omega⟩, ⟨2 * n + e, hline⟩,
          ⟨n, by omega, e, he, rfl, Or.inr (Or.inl rfl)⟩, hx, hy⟩
      · have := a.isLt
        rw [hWin _ (by omega)] at hx
        exact ⟨⟨a.val, by omega⟩, ⟨2 * n + e, hline⟩,
          ⟨n, by omega, e, he, rfl, Or.inl ⟨a, rfl, ha⟩⟩, hx, hy⟩
      · rw [hWin _ (by omega)] at hx
        exact ⟨⟨11 + 3 * n + 1 + e, by omega⟩, ⟨2 * n + e, hline⟩,
          ⟨n, by omega, e, he, rfl, Or.inr (Or.inr rfl)⟩, hx, hy⟩
    · rintro ⟨p, l, ⟨n, hn, e, he, hl, hp⟩, hzp, hzl⟩
      have hpl := p.isLt
      have hll := l.isLt
      have hWp : W p.val = true := by
        rw [hWin _ (by omega)]; exact hzp
      have hWl : W (NN T + l.val) = true := by
        rw [hWin _ (by omega)]; exact hzl
      rw [hl] at hWl
      refine ⟨n, by omega, ?_⟩
      have hA : A n e := by
        refine ⟨hWl, ?_⟩
        rcases hp with ⟨a, ha, haO⟩ | h | h
        · exact Or.inr (Or.inl ⟨a, haO, ha ▸ hWp⟩)
        · exact Or.inl (h ▸ hWp)
        · exact Or.inr (Or.inr (h ▸ hWp))
      rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
      · exact Or.inl hA
      · exact Or.inr hA

def St : Prop :=
  ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false)

def encN (T : ℕ) : V0 → ℕ
  | Sum.inl a => a.val
  | Sum.inr ((l, i), k) =>
    if k.val ≤ 2 then 11 + 3 * (14 * i + l.val) + k.val
    else NN T + (2 * (14 * i + l.val) + (k.val - 3))

noncomputable def enc (T : ℕ) (v : V0) : Option (Fin (NN T + NN T)) :=
  if h : v ∈ XS (box T) ∧ encN T v < NN T + NN T then some ⟨encN T v, h.2⟩ else none

theorem enc_inj (T : ℕ) (u v : V0) (q : Fin (NN T + NN T)) (hu : enc T u = some q)
    (hv : enc T v = some q) : u = v := by
  unfold enc at hu hv
  split_ifs at hu hv with h1 h2
  have e : encN T u = encN T v := by
    have := (Option.some.inj hu).trans (Option.some.inj hv).symm
    exact Fin.mk.inj this
  have hx : 0 < NN T := by unfold NN; omega
  rcases u with a | ⟨⟨l, i⟩, k⟩ <;> rcases v with b | ⟨⟨m, j⟩, n⟩
  · simp only [encN] at e
    exact congrArg Sum.inl (Fin.ext e)
  · exfalso
    simp only [encN] at e
    have := a.isLt
    have hN : 11 ≤ NN T := by unfold NN; omega
    split_ifs at e <;> omega
  · exfalso
    simp only [encN] at e
    have := b.isLt
    have hN : 11 ≤ NN T := by unfold NN; omega
    split_ifs at e <;> omega
  · have hi : i < T := by
      have := h1.1 (l, i) k rfl
      simpa [box] using this
    have hj : j < T := by
      have := h2.1 (m, j) n rfl
      simpa [box] using this
    simp only [encN] at e
    have hl := l.isLt
    have hm := m.isLt
    have hk := k.isLt
    have hn := n.isLt
    have hN : NN T = 11 + 42 * T := rfl
    have hall : l.val = m.val ∧ i = j ∧ k.val = n.val := by
      split_ifs at e <;> omega
    obtain ⟨a1, a2, a3⟩ := hall
    rw [Fin.ext a1, a2, Fin.ext a3]

theorem enc_rel (T : ℕ) (ρ : Set V0) :
    (∃ p l : Fin (NN T), Irel T p l ∧
      (∃ v ∈ ρ, enc T v = some (Fin.castAdd (NN T) p)) ∧
      (∃ v ∈ ρ, enc T v = some (Fin.natAdd (NN T) l))) ↔ Fn E0 (XS (box T)) ρ := by
  have hN : NN T = 11 + 42 * T := rfl
  have henc : ∀ v (q : Fin (NN T + NN T)), enc T v = some q ↔ v ∈ XS (box T) ∧ encN T v = q.val := by
    intro v q
    unfold enc
    constructor
    · intro h
      split_ifs at h with h1
      exact ⟨h1.1, congrArg Fin.val (Option.some.inj h)⟩
    · rintro ⟨h1, h2⟩
      rw [dif_pos ⟨h1, by rw [h2]; exact q.isLt⟩]
      exact congrArg some (Fin.ext h2)
  have hcp : ∀ (c : Cp) (k : Fin 5), (Sum.inr (c, k) : V0) ∈ XS (box T) ↔ c.2 < T := by
    intro c k
    constructor
    · intro h
      have := h c k rfl
      simpa [box] using this
    · intro h d m e
      cases e
      simpa [box] using h
  have hcore : ∀ a : Fin 11, (Sum.inl a : V0) ∈ XS (box T) := by
    intro a c k e; cases e
  have hpt : ∀ v (p : Fin (NN T)), enc T v = some (Fin.castAdd (NN T) p) ↔
      (∃ a : Fin 11, v = Sum.inl a ∧ p.val = a.val) ∨ ∃ l : Fin 14, ∃ i < T, ∃ k : Fin 5,
        k.val ≤ 2 ∧ v = Sum.inr ((l, i), k) ∧ p.val = 11 + 3 * (14 * i + l.val) + k.val := by
    intro v p
    rw [henc]
    have hp := p.isLt
    rcases v with a | ⟨⟨l, i⟩, k⟩
    · constructor
      · rintro ⟨-, h⟩
        exact Or.inl ⟨a, rfl, by simpa [encN] using h.symm⟩
      · rintro (⟨b, e, h⟩ | ⟨l, i, -, k, -, e, -⟩)
        · cases e
          exact ⟨hcore a, by simpa [encN] using h.symm⟩
        · cases e
    · rw [hcp]
      constructor
      · rintro ⟨hi, h⟩
        refine Or.inr ⟨l, i, hi, k, ?_⟩
        simp only [encN, Fin.val_castAdd] at h
        split_ifs at h with hk
        · exact ⟨hk, rfl, h.symm⟩
        · omega
      · rintro (⟨b, e, h⟩ | ⟨l', i', hi, k', hk, e, h⟩)
        · cases e
        · cases e
          refine ⟨hi, ?_⟩
          simp only [encN, Fin.val_castAdd, if_pos hk]
          omega
  have hln : ∀ v (q : Fin (NN T)), enc T v = some (Fin.natAdd (NN T) q) ↔
      ∃ l : Fin 14, ∃ i < T, ∃ k : Fin 5,
        3 ≤ k.val ∧ v = Sum.inr ((l, i), k) ∧ q.val = 2 * (14 * i + l.val) + (k.val - 3) := by
    intro v q
    rw [henc]
    rcases v with a | ⟨⟨l, i⟩, k⟩
    · constructor
      · rintro ⟨-, h⟩
        simp only [encN, Fin.val_natAdd] at h
        have := a.isLt
        omega
      · rintro ⟨l, i, -, k, -, e, -⟩
        cases e
    · rw [hcp]
      have hl := l.isLt
      constructor
      · rintro ⟨hi, h⟩
        simp only at hi
        refine ⟨l, i, hi, k, ?_⟩
        simp only [encN, Fin.val_natAdd] at h
        split_ifs at h with hk
        · omega
        · exact ⟨by omega, rfl, by omega⟩
      · rintro ⟨l', i', hi, k', hk, e, h⟩
        cases e
        refine ⟨hi, ?_⟩
        simp only [encN, Fin.val_natAdd, if_neg (show ¬ k.val ≤ 2 by omega)]
        omega
  have hmod : ∀ (l : Fin 14) (i : ℕ) (h : (14 * i + l.val) % 14 < 14),
      (⟨(14 * i + l.val) % 14, h⟩ : Fin 14) = l := by
    intro l i h
    apply Fin.ext
    have := l.isLt
    simp only
    omega
  constructor
  · rintro ⟨p, q, ⟨n, hn, e, he, hq, hpq⟩, ⟨u, hu, hup⟩, ⟨v, hv, hvq⟩⟩
    obtain ⟨l, i, hi, k, hk, rfl, hqv⟩ := (hln v q).mp hvq
    have hl := l.isLt
    have hk5 := k.isLt
    have hne : n = 14 * i + l.val ∧ e = k.val - 3 := by omega
    obtain ⟨rfl, rfl⟩ := hne
    refine ⟨u, _, Or.inl ?_, ?_, (hcp _ _).mpr hi, hu, hv⟩
    · rcases (hpt u p).mp hup with ⟨a, rfl, hpa⟩ | ⟨l', i', hi', k', hk', rfl, hp'⟩
      · show (k = 3 ∨ k = 4) ∧ a ∈ Osum l
        refine ⟨?_, ?_⟩
        · rcases (show k.val = 3 ∨ k.val = 4 by omega) with h | h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Fin.ext h)
        · rcases hpq with ⟨b, hb, hbO⟩ | h | h
          · rw [hmod] at hbO
            rw [show a = b from Fin.ext (by omega)]
            exact hbO
          · have := a.isLt; omega
          · have := a.isLt; omega
      · have hl' := l'.isLt
        have hcase : 14 * i' + l'.val = 14 * i + l.val ∧ (k'.val = 0 ∨ k'.val = 1 + (k.val - 3)) := by
          rcases hpq with ⟨b, hb, -⟩ | h | h
          · have := b.isLt; omega
          · omega
          · omega
        have e1 : i' = i := by omega
        have e2 : l' = l := Fin.ext (by omega)
        subst e1
        subst e2
        refine ⟨rfl, ?_⟩
        rcases (show k.val = 3 ∨ k.val = 4 by omega) with h | h <;> rcases hcase.2 with h' | h'
        · exact Or.inl ⟨Fin.ext h', Or.inl (Fin.ext h)⟩
        · exact Or.inr (Or.inl ⟨Fin.ext (show k'.val = 1 by omega), Fin.ext h⟩)
        · exact Or.inl ⟨Fin.ext h', Or.inr (Fin.ext h)⟩
        · exact Or.inr (Or.inr ⟨Fin.ext (show k'.val = 2 by omega), Fin.ext h⟩)
    · exact ((henc u _).mp hup).1
  · -- an edge, point first
    have key : ∀ u v, PL u v → u ∈ XS (box T) → v ∈ XS (box T) → u ∈ ρ → v ∈ ρ →
        ∃ p l : Fin (NN T), Irel T p l ∧
          (∃ v ∈ ρ, enc T v = some (Fin.castAdd (NN T) p)) ∧
          (∃ v ∈ ρ, enc T v = some (Fin.natAdd (NN T) l)) := by
      intro u v huv hu hv hu' hv'
      rcases v with b | ⟨⟨l, i⟩, k⟩
      · rcases u with a | ⟨c, m⟩ <;> exact absurd huv (by simp [PL])
      have hi : i < T := (hcp _ _).mp hv
      have hl := l.isLt
      rcases u with a | ⟨⟨l', i'⟩, k'⟩
      · obtain ⟨hk, ha⟩ := huv
        have hk3 : k.val = 3 ∨ k.val = 4 := by
          rcases hk with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hab := a.isLt
        refine ⟨⟨a.val, by omega⟩, ⟨2 * (14 * i + l.val) + (k.val - 3), by omega⟩,
          ⟨14 * i + l.val, by omega, k.val - 3, by omega, rfl, Or.inl ⟨a, rfl, ?_⟩⟩,
          ⟨_, hu', (hpt _ _).mpr (Or.inl ⟨a, rfl, rfl⟩)⟩,
          ⟨_, hv', (hln _ _).mpr ⟨l, i, hi, k, by omega, rfl, rfl⟩⟩⟩
        rw [hmod]; exact ha
      · obtain ⟨hc, h⟩ := huv
        cases hc
        have hk : (k'.val = 0 ∧ (k.val = 3 ∨ k.val = 4)) ∨ (k'.val = 1 ∧ k.val = 3) ∨
            (k'.val = 2 ∧ k.val = 4) := by
          rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨rfl, Or.inl rfl⟩
          · exact Or.inl ⟨rfl, Or.inr rfl⟩
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        refine ⟨⟨11 + 3 * (14 * i + l.val) + k'.val, by omega⟩,
          ⟨2 * (14 * i + l.val) + (k.val - 3), by omega⟩,
          ⟨14 * i + l.val, by omega, k.val - 3, by omega, rfl, Or.inr ?_⟩,
          ⟨_, hu', (hpt _ _).mpr (Or.inr ⟨l, i, hi, k', by omega, rfl, rfl⟩)⟩,
          ⟨_, hv', (hln _ _).mpr ⟨l, i, hi, k, by omega, rfl, rfl⟩⟩⟩
        simp only
        omega
    rintro ⟨u, v, h | h, hu, hv, hu', hv'⟩
    · exact key u v h hu hv hu' hv'
    · exact key v u h hv hu hv' hu'

theorem hypH_of_st (h : St) : HypH := by
  intro T hT
  obtain ⟨C, hM, hR, hC, hsz⟩ := upper T hT
  obtain ⟨D, dM, dR, dsz, dC, dcl⟩ := h (NN T) (Irel T) C hM hR hC
  have hNN : 0 < NN T := by unfold NN; omega
  have henc0 : enc T (Sum.inl 0) = some (⟨0, by omega⟩ : Fin (NN T + NN T)) := by
    unfold enc
    rw [dif_pos ⟨(by intro c k hk; cases hk), (by simp [encN]; omega)⟩]
    simp [encN]
  have hf : ∃ ρ, Fn E0 (XS (box T)) ρ := by
    refine ⟨Set.univ, Sum.inl 0, cv (0, 0) 3, Or.inl ?_, ?_, ?_, trivial, trivial⟩
    · simp [PL, cv, Osum]
    · intro c k hk; cases hk
    · intro c k hk
      cases hk
      simp [box]; omega
  obtain ⟨K, kW, kcl, kf, ksz⟩ := bridge_in (enc T) (enc_inj T) ⟨_, _, henc0⟩
    (Fn E0 (XS (box T))) hf D dM dR (by
      intro ρ
      rw [dC, ← enc_rel]
      simp only [decide_eq_true_eq]) (by
      intro v q _ j hj ho
      have := dcl j hj ho
      rcases Nat.lt_or_ge q.val (NN T) with hq | hq
      · have e : q = Fin.castAdd (NN T) ⟨q.val, hq⟩ := Fin.ext rfl
        rw [e]; exact this.1 _
      · have e : q = Fin.natAdd (NN T) ⟨q.val - NN T, by omega⟩ := Fin.ext (by simp; omega)
        rw [e]; exact this.2 _)
  exact ⟨K, ⟨kW, kcl, kf, fun y hy => hy.elim⟩, by omega⟩

theorem no_hypH (H : HypH) : False := by
  obtain ⟨S, hr, C, h6⟩ := drop_z H (18 + 2 ^ 34)
  obtain ⟨c, L, hc⟩ := s6_setup h6
  have hbad := s6_bad h6 hc
  have hpick : ∀ l : Fin 14, ∃ d ∈ S, d.1 = l ∧
      ¬ ∃ x, x ∉ PP (S ×ˢ ({3, 4} : Finset (Fin 5))) (fun j => cv j.1 j.2)
        (fun j => cv j.1 (j.2 - 2)) ∧ x ∉ {x : V0 | ∃ a ∈ Osum d.1, x = Sum.inl a} ∧
        C.val {x} (L (d, 3)) := by
    intro l
    by_contra hno
    push Not at hno
    have hsub : (S.filter (fun d => d.1 = l)).image (fun d => (d, (3 : Fin 5))) ⊆
        (S ×ˢ ({3, 4} : Finset (Fin 5))).filter (fun j => ∃ x, x ∉ PP (S ×ˢ ({3, 4} :
          Finset (Fin 5))) (fun j => cv j.1 j.2) (fun j => cv j.1 (j.2 - 2)) ∧
          x ∉ {x : V0 | ∃ a ∈ Osum j.1.1, x = Sum.inl a} ∧ C.val {x} (L j)) := by
      intro j hj
      simp only [Finset.mem_image, Finset.mem_filter] at hj
      obtain ⟨d, ⟨hd, hl⟩, rfl⟩ := hj
      refine Finset.mem_filter.mpr ⟨?_, hno d hd hl⟩
      simp [hd]
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).1)] at hcard
    have := hr l
    unfold cnt at this
    have h3 := le_trans hcard hbad
    omega
  choose d hdS hdl hdb using hpick
  have hPin : ∀ a : Fin 11, (Sum.inl a : V0) ∉ PP (S ×ˢ ({3, 4} : Finset (Fin 5)))
      (fun j => cv j.1 j.2) (fun j => cv j.1 (j.2 - 2)) := by
    intro a ha
    simp [PP, cv] at ha
  have hJ : ∀ l, (d l, (3 : Fin 5)) ∈ S ×ˢ ({3, 4} : Finset (Fin 5)) := by
    intro l; simp [hdS l]
  obtain ⟨F, hF1, hF2, hF3⟩ := extract (C := C) h6.2.1.1 h6.1 hPin (fun l => L (d l, 3)) (by
    intro l
    obtain ⟨_, hx, _⟩ := hc
    have := hx _ (hJ l)
    refine ⟨this.2.2.2.2.1, this.2.2.2.2.2.1, fun a => ⟨fun hv => ?_, fun ha => ?_⟩⟩
    · by_contra hna
      refine hdb l ⟨Sum.inl a, hPin a, ?_, hv⟩
      rintro ⟨b, hb, he⟩
      rw [hdl l] at hb
      cases he
      exact hna hb
    · refine this.2.2.2.2.2.2.2.2 _ (hPin a) ⟨a, ?_, rfl⟩
      simpa [hdl l] using ha)
  have h18 := t2 F hF2 hF3
  have := hc.2.2
  omega

theorem main (h : St) : False := no_hypH (hypH_of_st h)

end PEqualNP.Outside.L_meta_3669

theorem PEqualNP.Outside.L_meta_3669 : ¬ (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false)) :=
  fun h => PEqualNP.Outside.L_meta_3669.main h
