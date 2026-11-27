import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2052

def fo {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) : List α :=
  G.foldl (fun w g => w ++ [Φ g (g.inputs.map fun i => w.getD i dflt)]) x

def gv {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) (i : ℕ) : α :=
  (fo dflt Φ G x).getD i dflt

def gd : Gate := ⟨GateOp.or, []⟩

def Φb (g : Gate) (l : List Bool) : Bool := g.op.eval l


theorem hA_fo_append {α : Type} (dflt : α) (Φ : Gate → List α → α) (G1 G2 : List Gate) (x : List α) :
    fo dflt Φ (G1 ++ G2) x = fo dflt Φ G2 (fo dflt Φ G1 x) := by
  unfold fo
  rw [List.foldl_append]

theorem hA_fo_pre {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) :
    ∀ x : List α, ∃ t, fo dflt Φ G x = x ++ t ∧ t.length = G.length := by
  induction G with
  | nil => intro x; exact ⟨[], by simp [fo], rfl⟩
  | cons g G ih =>
    intro x
    obtain ⟨t, ht, hl⟩ := ih (x ++ [Φ g (g.inputs.map fun i => x.getD i dflt)])
    refine ⟨Φ g (g.inputs.map fun i => x.getD i dflt) :: t, ?_, by simp [hl]⟩
    show fo dflt Φ G (x ++ [Φ g (g.inputs.map fun i => x.getD i dflt)]) = _
    rw [ht]
    simp

theorem hA_fo_len {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) :
    (fo dflt Φ G x).length = x.length + G.length := by
  obtain ⟨t, ht, hl⟩ := hA_fo_pre dflt Φ G x
  rw [ht, List.length_append, hl]

theorem gv_stable {α : Type} (dflt : α) (Φ : Gate → List α → α) (G1 G2 : List Gate) (x : List α) (i : ℕ)
    (h : i < x.length + G1.length) : gv dflt Φ (G1 ++ G2) x i = gv dflt Φ G1 x i := by
  have hl := hA_fo_len dflt Φ G1 x
  obtain ⟨t, ht, _⟩ := hA_fo_pre dflt Φ G2 (fo dflt Φ G1 x)
  show (fo dflt Φ (G1 ++ G2) x).getD i dflt = (fo dflt Φ G1 x).getD i dflt
  rw [hA_fo_append, ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega)]

theorem gv_input {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) (i : ℕ)
    (h : i < x.length) : gv dflt Φ G x i = x.getD i dflt := by
  obtain ⟨t, ht, _⟩ := hA_fo_pre dflt Φ G x
  show (fo dflt Φ G x).getD i dflt = x.getD i dflt
  rw [ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gv_oob {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) (i : ℕ)
    (h : x.length + G.length ≤ i) : gv dflt Φ G x i = dflt := by
  have hl := hA_fo_len dflt Φ G x
  show (fo dflt Φ G x).getD i dflt = dflt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem gv_snoc {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (g : Gate) (x : List α) :
    gv dflt Φ (G ++ [g]) x (x.length + G.length) = Φ g (g.inputs.map (gv dflt Φ G x)) := by
  have hl := hA_fo_len dflt Φ G x
  show (fo dflt Φ (G ++ [g]) x).getD (x.length + G.length) dflt =
    Φ g (g.inputs.map fun i => (fo dflt Φ G x).getD i dflt)
  rw [hA_fo_append]
  show ((fo dflt Φ G x) ++ [Φ g (g.inputs.map fun i => (fo dflt Φ G x).getD i dflt)]).getD
    (x.length + G.length) dflt = _
  rw [← hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

theorem gv_gate {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α)
    (hrb : ∀ j < G.length, ∀ i ∈ (G.getD j gd).inputs, i < x.length + j) (j : ℕ) (hj : j < G.length) :
    gv dflt Φ G x (x.length + j) = Φ (G.getD j gd) ((G.getD j gd).inputs.map (gv dflt Φ G x)) := by
  have hsplit : (G.take j ++ [G.getD j gd]) ++ G.drop (j + 1) = G := by
    have hg : G.getD j gd = G[j] := by simp [List.getD_eq_getElem?_getD, hj]
    rw [hg]
    simp
  have hlen : (G.take j).length = j := by
    rw [List.length_take]
    omega
  have h1 : gv dflt Φ ((G.take j ++ [G.getD j gd]) ++ G.drop (j + 1)) x (x.length + j) =
      gv dflt Φ (G.take j ++ [G.getD j gd]) x (x.length + j) :=
    gv_stable dflt Φ _ _ x _ (by rw [List.length_append, hlen, List.length_singleton]; omega)
  rw [hsplit] at h1
  have h2 := gv_snoc dflt Φ (G.take j) (G.getD j gd) x
  rw [hlen] at h2
  rw [h1, h2]
  congr 1
  apply List.map_congr_left
  intro i hi
  have h3 := gv_stable dflt Φ (G.take j) (G.drop j) x i (by rw [hlen]; exact hrb j hj i hi)
  rw [List.take_append_drop] at h3
  exact h3.symm
theorem hA_getD_lt (G : List Gate) (g : Gate) (j : ℕ) (h : j < G.length) :
    (G ++ [g]).getD j gd = G.getD j gd := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem hA_getD_eq (G : List Gate) (g : Gate) : (G ++ [g]).getD G.length gd = g := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

def Rep (N : ℕ) (H : List Gate) (v : Option ℕ) (φ : (Fin (N + N) → Bool) → Bool) : Prop :=
  match v with
  | none => ∀ z, φ z = false
  | some w => w < N + N + H.length ∧ ∀ z, gv false Φb H (List.ofFn z) w = φ z

def memv (S : Finset ℕ) (v : Option ℕ) : Prop := ∀ w, v = some w → w ∈ S

def addv (S : Finset ℕ) : Option ℕ → Finset ℕ
  | none => S
  | some w => insert w S

def Inv (N : ℕ) (H : List Gate) (P L : Finset ℕ) : Prop :=
  (∀ w ∈ P, w < N ∨ ∃ i < H.length, w = N + N + i ∧ (H.getD i gd).op = GateOp.or ∧
      ∀ u ∈ (H.getD i gd).inputs, u ∈ P) ∧
  (∀ w ∈ L, (N ≤ w ∧ w < N + N) ∨ ∃ i < H.length, w = N + N + i ∧
      (H.getD i gd).op = GateOp.or ∧ ∀ u ∈ (H.getD i gd).inputs, u ∈ L) ∧
  (∀ i < H.length, (H.getD i gd).op = GateOp.and → ∃ a b : ℕ, (H.getD i gd).inputs = [a, b] ∧
      ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) ∧
  (∀ g ∈ H, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ i < H.length, ∀ u ∈ (H.getD i gd).inputs, u < N + N + i)

theorem memv_mono {S S' : Finset ℕ} {v : Option ℕ} (h : memv S v) (hs : S ⊆ S') : memv S' v :=
  fun w hw => hs (h w hw)

theorem addv_of_memv {S : Finset ℕ} {v : Option ℕ} (h : memv S v) : addv S v = S := by
  cases v with
  | none => rfl
  | some w => exact Finset.insert_eq_of_mem (h w rfl)

theorem rep_ext {N : ℕ} {H : List Gate} {v : Option ℕ} {φ : (Fin (N + N) → Bool) → Bool}
    (E : List Gate) (h : Rep N H v φ) : Rep N (H ++ E) v φ := by
  cases v with
  | none => exact h
  | some w =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨by rw [List.length_append]; omega, fun z => ?_⟩
    rw [← h2 z]
    exact gv_stable false Φb H E _ w (by rw [List.length_ofFn]; exact h1)

theorem rep_congr {N : ℕ} {H : List Gate} {v : Option ℕ} {φ ψ : (Fin (N + N) → Bool) → Bool}
    (h : Rep N H v φ) (e : ∀ z, φ z = ψ z) : Rep N H v ψ := by
  cases v with
  | none => exact fun z => (e z) ▸ h z
  | some w => exact ⟨h.1, fun z => (h.2 z).trans (e z)⟩

theorem inv_snoc {N : ℕ} {H : List Gate} {P L : Finset ℕ} (hI : Inv N H P L) (op : GateOp)
    (wa wb : ℕ) (P' L' : Finset ℕ) (hP : P ⊆ P') (hL : L ⊆ L')
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (ha : wa < N + N + H.length) (hb : wb < N + N + H.length)
    (hP' : ∀ w ∈ P', w ∈ P ∨ (w = N + N + H.length ∧ op = GateOp.or ∧ wa ∈ P' ∧ wb ∈ P'))
    (hL' : ∀ w ∈ L', w ∈ L ∨ (w = N + N + H.length ∧ op = GateOp.or ∧ wa ∈ L' ∧ wb ∈ L'))
    (hand : op = GateOp.and → (wa ∈ P' ∧ wb ∈ L') ∨ (wa ∈ L' ∧ wb ∈ P')) :
    Inv N (H ++ [⟨op, [wa, wb]⟩]) P' L' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  have hlen : (H ++ [(⟨op, [wa, wb]⟩ : Gate)]).length = H.length + 1 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rcases hP' w hw with hw | ⟨rfl, hor, hA, hB⟩
    · rcases h1 w hw with hlt | ⟨i, hi, rfl, hor, hin⟩
      · exact Or.inl hlt
      · right
        refine ⟨i, by rw [hlen]; omega, rfl, ?_, ?_⟩
        · rw [hA_getD_lt _ _ _ hi]; exact hor
        · rw [hA_getD_lt _ _ _ hi]; exact fun u hu => hP (hin u hu)
    · right
      refine ⟨H.length, by rw [hlen]; omega, rfl, ?_, ?_⟩
      · rw [hA_getD_eq]; exact hor
      · rw [hA_getD_eq]
        intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact hA
        · exact hB
  · intro w hw
    rcases hL' w hw with hw | ⟨rfl, hor, hA, hB⟩
    · rcases h2 w hw with hlt | ⟨i, hi, rfl, hor, hin⟩
      · exact Or.inl hlt
      · right
        refine ⟨i, by rw [hlen]; omega, rfl, ?_, ?_⟩
        · rw [hA_getD_lt _ _ _ hi]; exact hor
        · rw [hA_getD_lt _ _ _ hi]; exact fun u hu => hL (hin u hu)
    · right
      refine ⟨H.length, by rw [hlen]; omega, rfl, ?_, ?_⟩
      · rw [hA_getD_eq]; exact hor
      · rw [hA_getD_eq]
        intro u hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact hA
        · exact hB
  · intro i hi hand'
    rw [hlen] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · rw [hA_getD_lt _ _ _ hi] at hand' ⊢
      obtain ⟨a, b, hab, hc⟩ := h3 i hi hand'
      refine ⟨a, b, hab, ?_⟩
      rcases hc with ⟨x, y⟩ | ⟨x, y⟩
      · exact Or.inl ⟨hP x, hL y⟩
      · exact Or.inr ⟨hL x, hP y⟩
    · subst hi
      rw [hA_getD_eq] at hand' ⊢
      exact ⟨wa, wb, rfl, hand hand'⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h4 g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨hop, rfl⟩
  · intro i hi u hu
    rw [hlen] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · rw [hA_getD_lt _ _ _ hi] at hu
      have := h5 i hi u hu
      omega
    · subst hi
      rw [hA_getD_eq] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega

def orG : Option ℕ → Option ℕ → ℕ → List Gate × Option ℕ
  | none, v, _ => ([], v)
  | some w, none, _ => ([], some w)
  | some a, some b, k => ([⟨GateOp.or, [a, b]⟩], some k)

def andG : Option ℕ → Option ℕ → ℕ → List Gate × Option ℕ
  | none, _, _ => ([], none)
  | some _, none, _ => ([], none)
  | some a, some b, k => ([⟨GateOp.and, [a, b]⟩], some k)

structure Tr where
  p : Option ℕ
  l : Option ℕ
  r : Option ℕ

structure Sx where
  H : List Gate
  P : Finset ℕ
  L : Finset ℕ

def sOr (N role : ℕ) (s : Sx) (va vb : Option ℕ) : Sx × Option ℕ :=
  (⟨s.H ++ (orG va vb (N + N + s.H.length)).1,
    if role = 0 then addv s.P (orG va vb (N + N + s.H.length)).2 else s.P,
    if role = 1 then addv s.L (orG va vb (N + N + s.H.length)).2 else s.L⟩,
   (orG va vb (N + N + s.H.length)).2)

def sAnd (N : ℕ) (s : Sx) (va vb : Option ℕ) : Sx × Option ℕ :=
  (⟨s.H ++ (andG va vb (N + N + s.H.length)).1, s.P, s.L⟩, (andG va vb (N + N + s.H.length)).2)

theorem gv_or2 {N : ℕ} (H : List Gate) (op : GateOp) (a b : ℕ) (z : Fin (N + N) → Bool) :
    gv false Φb (H ++ [⟨op, [a, b]⟩]) (List.ofFn z) (N + N + H.length) =
      op.eval [gv false Φb H (List.ofFn z) a, gv false Φb H (List.ofFn z) b] := by
  have := gv_snoc false Φb H ⟨op, [a, b]⟩ (List.ofFn z)
  rw [List.length_ofFn] at this
  rw [this]
  rfl

theorem sOr_ok {N : ℕ} (role : ℕ) (s : Sx) (va vb : Option ℕ)
    {φ ψ : (Fin (N + N) → Bool) → Bool}
    (hI : Inv N s.H s.P s.L) (ha : Rep N s.H va φ) (hb : Rep N s.H vb ψ)
    (hmP : role = 0 → memv s.P va ∧ memv s.P vb) (hmL : role = 1 → memv s.L va ∧ memv s.L vb) :
    Inv N (sOr N role s va vb).1.H (sOr N role s va vb).1.P (sOr N role s va vb).1.L ∧
    Rep N (sOr N role s va vb).1.H (sOr N role s va vb).2 (fun z => φ z || ψ z) ∧
    (∃ E : List Gate, (sOr N role s va vb).1.H = s.H ++ E ∧ E.length ≤ 1) ∧
    s.P ⊆ (sOr N role s va vb).1.P ∧ s.L ⊆ (sOr N role s va vb).1.L ∧
    (role = 0 → memv (sOr N role s va vb).1.P (sOr N role s va vb).2) ∧
    (role = 1 → memv (sOr N role s va vb).1.L (sOr N role s va vb).2) := by
  obtain ⟨H, P, L⟩ := s
  cases va with
  | none =>
    have eP : (if role = 0 then addv P vb else P) = P := by
      split_ifs with h
      · exact addv_of_memv (hmP h).2
      · rfl
    have eL : (if role = 1 then addv L vb else L) = L := by
      split_ifs with h
      · exact addv_of_memv (hmL h).2
      · rfl
    simp only [sOr, orG, List.append_nil, eP, eL]
    refine ⟨hI, rep_congr hb (fun z => by simp [show φ z = false from ha z]), ⟨[], by simp, by simp⟩,
      subset_refl _, subset_refl _, fun h => (hmP h).2, fun h => (hmL h).2⟩
  | some wa =>
    cases vb with
    | none =>
      have eP : (if role = 0 then addv P (some wa) else P) = P := by
        split_ifs with h
        · exact addv_of_memv (hmP h).1
        · rfl
      have eL : (if role = 1 then addv L (some wa) else L) = L := by
        split_ifs with h
        · exact addv_of_memv (hmL h).1
        · rfl
      simp only [sOr, orG, List.append_nil, eP, eL]
      refine ⟨hI, rep_congr ha (fun z => by simp [show ψ z = false from hb z]),
        ⟨[], by simp, by simp⟩, subset_refl _, subset_refl _, fun h => (hmP h).1,
        fun h => (hmL h).1⟩
    | some wb =>
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      simp only [sOr, orG, addv]
      refine ⟨?_, ⟨by simp, fun z => ?_⟩, ⟨_, rfl, by simp⟩, ?_, ?_, ?_, ?_⟩
      · apply inv_snoc hI GateOp.or wa wb _ _ ?_ ?_ (Or.inr rfl) ha1 hb1 ?_ ?_ (fun h => by cases h)
        · split_ifs
          · exact Finset.subset_insert _ _
          · exact subset_refl _
        · split_ifs
          · exact Finset.subset_insert _ _
          · exact subset_refl _
        · intro w hw
          split_ifs at hw ⊢ with h
          · rcases Finset.mem_insert.1 hw with rfl | hw
            · exact Or.inr ⟨rfl, rfl, Finset.mem_insert_of_mem ((hmP h).1 wa rfl),
                Finset.mem_insert_of_mem ((hmP h).2 wb rfl)⟩
            · exact Or.inl hw
          · exact Or.inl hw
        · intro w hw
          split_ifs at hw ⊢ with h
          · rcases Finset.mem_insert.1 hw with rfl | hw
            · exact Or.inr ⟨rfl, rfl, Finset.mem_insert_of_mem ((hmL h).1 wa rfl),
                Finset.mem_insert_of_mem ((hmL h).2 wb rfl)⟩
            · exact Or.inl hw
          · exact Or.inl hw
      · rw [gv_or2, ha2, hb2]
        simp [GateOp.eval]
      · split_ifs
        · exact Finset.subset_insert _ _
        · exact subset_refl _
      · split_ifs
        · exact Finset.subset_insert _ _
        · exact subset_refl _
      · intro h w hw
        cases hw
        simp only [h, ↓reduceIte]
        exact Finset.mem_insert_self _ _
      · intro h w hw
        cases hw
        simp only [h, ↓reduceIte]
        exact Finset.mem_insert_self _ _

theorem sAnd_ok {N : ℕ} (s : Sx) (va vb : Option ℕ) {φ ψ : (Fin (N + N) → Bool) → Bool}
    (hI : Inv N s.H s.P s.L) (ha : Rep N s.H va φ) (hb : Rep N s.H vb ψ)
    (hm : (memv s.P va ∧ memv s.L vb) ∨ (memv s.L va ∧ memv s.P vb)) :
    Inv N (sAnd N s va vb).1.H (sAnd N s va vb).1.P (sAnd N s va vb).1.L ∧
    Rep N (sAnd N s va vb).1.H (sAnd N s va vb).2 (fun z => φ z && ψ z) ∧
    (∃ E : List Gate, (sAnd N s va vb).1.H = s.H ++ E ∧ E.length ≤ 1) ∧
    (sAnd N s va vb).1.P = s.P ∧ (sAnd N s va vb).1.L = s.L := by
  obtain ⟨H, P, L⟩ := s
  cases va with
  | none =>
    simp only [sAnd, andG, List.append_nil]
    exact ⟨hI, fun z => by simp [show φ z = false from ha z], ⟨[], by simp, by simp⟩, by simp, by simp⟩
  | some wa =>
    cases vb with
    | none =>
      simp only [sAnd, andG, List.append_nil]
      exact ⟨hI, fun z => by simp [show ψ z = false from hb z], ⟨[], by simp, by simp⟩, by simp, by simp⟩
    | some wb =>
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      simp only [sAnd, andG]
      refine ⟨?_, ⟨by simp, fun z => ?_⟩, ⟨_, rfl, by simp⟩, by simp, by simp⟩
      · apply inv_snoc hI GateOp.and wa wb _ _ (subset_refl _) (subset_refl _) (Or.inl rfl) ha1 hb1
          (fun w hw => Or.inl hw) (fun w hw => Or.inl hw)
        intro _
        rcases hm with ⟨x, y⟩ | ⟨x, y⟩
        · exact Or.inl ⟨x wa rfl, y wb rfl⟩
        · exact Or.inr ⟨x wa rfl, y wb rfl⟩
      · rw [gv_or2, ha2, hb2]
        simp [GateOp.eval]


def ep (N : ℕ) (p : Fin N) : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p)

def el (N : ℕ) (l : Fin N) : Fin (N + N) → Bool := fun k => decide (k = Fin.natAdd N l)

def epl (N : ℕ) (p l : Fin N) : Fin (N + N) → Bool :=
  fun k => decide (k = Fin.castAdd N p) || decide (k = Fin.natAdd N l)

def PFf (N : ℕ) (G : (Fin (N + N) → Bool) → Bool) (z : Fin (N + N) → Bool) : Bool :=
  decide (∃ p : Fin N, z (Fin.castAdd N p) = true ∧ G (ep N p) = true)

def LFf (N : ℕ) (G : (Fin (N + N) → Bool) → Bool) (z : Fin (N + N) → Bool) : Bool :=
  decide (∃ l : Fin N, z (Fin.natAdd N l) = true ∧ G (el N l) = true)

def FF (N : ℕ) (I : Fin N → Fin N → Prop) (z : Fin (N + N) → Bool) : Prop :=
  ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

def WOk (N : ℕ) (I : Fin N → Fin N → Prop) (H : List Gate) (P L : Finset ℕ) (t : Tr)
    (G : (Fin (N + N) → Bool) → Bool) : Prop :=
  Rep N H t.p (PFf N G) ∧ memv P t.p ∧ Rep N H t.l (LFf N G) ∧ memv L t.l ∧
  ∃ φ : (Fin (N + N) → Bool) → Bool, Rep N H t.r φ ∧ (∀ z, φ z = true → FF N I z) ∧
    ∀ p l, I p l → G (epl N p l) = true → G (ep N p) = false → G (el N l) = false →
      φ (epl N p l) = true

theorem wok_ext {N : ℕ} {I : Fin N → Fin N → Prop} {H : List Gate} {P L P' L' : Finset ℕ}
    {t : Tr} {G : (Fin (N + N) → Bool) → Bool} (h : WOk N I H P L t G) (E : List Gate)
    (hP : P ⊆ P') (hL : L ⊆ L') : WOk N I (H ++ E) P' L' t G := by
  obtain ⟨a, b, c, d, φ, e, f, g⟩ := h
  exact ⟨rep_ext E a, memv_mono b hP, rep_ext E c, memv_mono d hL, φ, rep_ext E e, f, g⟩

theorem epl_c {N : ℕ} (p l : Fin N) : epl N p l (Fin.castAdd N p) = true := by
  simp [epl]

theorem epl_n {N : ℕ} (p l : Fin N) : epl N p l (Fin.natAdd N l) = true := by
  simp [epl]

theorem ep_le {N : ℕ} (p l : Fin N) : ∀ k, ep N p k = true → epl N p l k = true := by
  intro k hk
  simp only [ep, decide_eq_true_eq] at hk
  subst hk
  exact epl_c p l

theorem el_le {N : ℕ} (p l : Fin N) : ∀ k, el N l k = true → epl N p l k = true := by
  intro k hk
  simp only [el, decide_eq_true_eq] at hk
  subst hk
  exact epl_n p l

theorem pf_or {N : ℕ} (Ga Gb : (Fin (N + N) → Bool) → Bool) (z : Fin (N + N) → Bool) :
    PFf N (fun z => Ga z || Gb z) z = (PFf N Ga z || PFf N Gb z) := by
  apply Bool.eq_iff_iff.2
  simp only [PFf, decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨p, h1, h2 | h2⟩
    · exact Or.inl ⟨p, h1, h2⟩
    · exact Or.inr ⟨p, h1, h2⟩
  · rintro (⟨p, h1, h2⟩ | ⟨p, h1, h2⟩)
    · exact ⟨p, h1, Or.inl h2⟩
    · exact ⟨p, h1, Or.inr h2⟩

theorem lf_or {N : ℕ} (Ga Gb : (Fin (N + N) → Bool) → Bool) (z : Fin (N + N) → Bool) :
    LFf N (fun z => Ga z || Gb z) z = (LFf N Ga z || LFf N Gb z) := by
  apply Bool.eq_iff_iff.2
  simp only [LFf, decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨p, h1, h2 | h2⟩
    · exact Or.inl ⟨p, h1, h2⟩
    · exact Or.inr ⟨p, h1, h2⟩
  · rintro (⟨p, h1, h2⟩ | ⟨p, h1, h2⟩)
    · exact ⟨p, h1, Or.inl h2⟩
    · exact ⟨p, h1, Or.inr h2⟩

def orStep (N : ℕ) (s : Sx) (A B : Tr) : Sx × Tr :=
  ((sOr N 2 (sOr N 1 (sOr N 0 s A.p B.p).1 A.l B.l).1 A.r B.r).1,
   ⟨(sOr N 0 s A.p B.p).2, (sOr N 1 (sOr N 0 s A.p B.p).1 A.l B.l).2,
    (sOr N 2 (sOr N 1 (sOr N 0 s A.p B.p).1 A.l B.l).1 A.r B.r).2⟩)

def andStep (N : ℕ) (s : Sx) (A B : Tr) : Sx × Tr :=
  ((sOr N 2 (sOr N 2 (sOr N 2 (sAnd N (sAnd N s A.p B.l).1 A.l B.p).1 (sAnd N s A.p B.l).2
      (sAnd N (sAnd N s A.p B.l).1 A.l B.p).2).1 A.r B.r).1
      (sOr N 2 (sAnd N (sAnd N s A.p B.l).1 A.l B.p).1 (sAnd N s A.p B.l).2
        (sAnd N (sAnd N s A.p B.l).1 A.l B.p).2).2
      (sOr N 2 (sOr N 2 (sAnd N (sAnd N s A.p B.l).1 A.l B.p).1 (sAnd N s A.p B.l).2
        (sAnd N (sAnd N s A.p B.l).1 A.l B.p).2).1 A.r B.r).2).1,
   ⟨none, none,
    (sOr N 2 (sOr N 2 (sOr N 2 (sAnd N (sAnd N s A.p B.l).1 A.l B.p).1 (sAnd N s A.p B.l).2
      (sAnd N (sAnd N s A.p B.l).1 A.l B.p).2).1 A.r B.r).1
      (sOr N 2 (sAnd N (sAnd N s A.p B.l).1 A.l B.p).1 (sAnd N s A.p B.l).2
        (sAnd N (sAnd N s A.p B.l).1 A.l B.p).2).2
      (sOr N 2 (sOr N 2 (sAnd N (sAnd N s A.p B.l).1 A.l B.p).1 (sAnd N s A.p B.l).2
        (sAnd N (sAnd N s A.p B.l).1 A.l B.p).2).1 A.r B.r).2).2⟩)

theorem or_case {N : ℕ} {I : Fin N → Fin N → Prop} (s : Sx) (A B : Tr)
    {Ga Gb : (Fin (N + N) → Bool) → Bool} (hI : Inv N s.H s.P s.L)
    (hA : WOk N I s.H s.P s.L A Ga) (hB : WOk N I s.H s.P s.L B Gb) :
    Inv N (orStep N s A B).1.H (orStep N s A B).1.P (orStep N s A B).1.L ∧
    (∃ E : List Gate, (orStep N s A B).1.H = s.H ++ E ∧ E.length ≤ 5) ∧
    s.P ⊆ (orStep N s A B).1.P ∧ s.L ⊆ (orStep N s A B).1.L ∧
    WOk N I (orStep N s A B).1.H (orStep N s A B).1.P (orStep N s A B).1.L (orStep N s A B).2
      (fun z => Ga z || Gb z) := by
  obtain ⟨hAp, hAmp, hAl, hAml, φa, hAr, hAs, hAc⟩ := hA
  obtain ⟨hBp, hBmp, hBl, hBml, φb, hBr, hBs, hBc⟩ := hB
  unfold orStep
  obtain ⟨I1, R1, ⟨E1, hE1, hl1⟩, sP1, sL1, m1, -⟩ :=
    sOr_ok 0 s A.p B.p hI hAp hBp (fun _ => ⟨hAmp, hBmp⟩) (fun h => absurd h (by decide))
  generalize sOr N 0 s A.p B.p = o1 at I1 R1 hE1 sP1 sL1 m1 ⊢
  obtain ⟨I2, R2, ⟨E2, hE2, hl2⟩, sP2, sL2, -, m2⟩ :=
    sOr_ok 1 o1.1 A.l B.l I1 (by rw [hE1]; exact rep_ext _ hAl) (by rw [hE1]; exact rep_ext _ hBl)
      (fun h => absurd h (by decide)) (fun _ => ⟨memv_mono hAml sL1, memv_mono hBml sL1⟩)
  generalize sOr N 1 o1.1 A.l B.l = o2 at I2 R2 hE2 sP2 sL2 m2 ⊢
  obtain ⟨I3, R3, ⟨E3, hE3, hl3⟩, sP3, sL3, -, -⟩ :=
    sOr_ok 2 o2.1 A.r B.r I2 (by rw [hE2, hE1]; exact rep_ext _ (rep_ext _ hAr))
      (by rw [hE2, hE1]; exact rep_ext _ (rep_ext _ hBr))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
  generalize sOr N 2 o2.1 A.r B.r = o3 at I3 R3 hE3 sP3 sL3 ⊢
  refine ⟨I3, ⟨E1 ++ E2 ++ E3, by rw [hE3, hE2, hE1]; simp, by simp; omega⟩,
    sP1.trans (sP2.trans sP3), sL1.trans (sL2.trans sL3), ?_, ?_, ?_, ?_, ?_⟩
  · have := rep_congr R1 (fun z => (pf_or Ga Gb z).symm)
    rw [hE3, hE2]
    exact rep_ext _ (rep_ext _ this)
  · exact memv_mono (m1 rfl) (sP2.trans sP3)
  · have := rep_congr R2 (fun z => (lf_or Ga Gb z).symm)
    rw [hE3]
    exact rep_ext _ this
  · exact memv_mono (m2 rfl) sL3
  · refine ⟨_, R3, fun z hz => ?_, fun p l hpl hG hp hl => ?_⟩
    · simp only [Bool.or_eq_true] at hz
      rcases hz with hz | hz
      · exact hAs z hz
      · exact hBs z hz
    · simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at hG hp hl ⊢
      rcases hG with hG | hG
      · exact Or.inl (hAc p l hpl hG hp.1 hl.1)
      · exact Or.inr (hBc p l hpl hG hp.2 hl.2)


theorem and_case {N : ℕ} {I : Fin N → Fin N → Prop} (s : Sx) (A B : Tr)
    {Ga Gb : (Fin (N + N) → Bool) → Bool} (hI : Inv N s.H s.P s.L)
    (hA : WOk N I s.H s.P s.L A Ga) (hB : WOk N I s.H s.P s.L B Gb)
    (hmA : ∀ z z' : Fin (N + N) → Bool, (∀ k, z k = true → z' k = true) → Ga z = true →
      Ga z' = true)
    (hmB : ∀ z z' : Fin (N + N) → Bool, (∀ k, z k = true → z' k = true) → Gb z = true →
      Gb z' = true)
    (hsP : ∀ p, (Ga (ep N p) && Gb (ep N p)) = false)
    (hsL : ∀ l, (Ga (el N l) && Gb (el N l)) = false)
    (hcl : ∀ p l, (Ga (epl N p l) && Gb (epl N p l)) = true → I p l) :
    Inv N (andStep N s A B).1.H (andStep N s A B).1.P (andStep N s A B).1.L ∧
    (∃ E : List Gate, (andStep N s A B).1.H = s.H ++ E ∧ E.length ≤ 5) ∧
    s.P ⊆ (andStep N s A B).1.P ∧ s.L ⊆ (andStep N s A B).1.L ∧
    WOk N I (andStep N s A B).1.H (andStep N s A B).1.P (andStep N s A B).1.L
      (andStep N s A B).2 (fun z => Ga z && Gb z) := by
  obtain ⟨hAp, hAmp, hAl, hAml, φa, hAr, hAs, hAc⟩ := hA
  obtain ⟨hBp, hBmp, hBl, hBml, φb, hBr, hBs, hBc⟩ := hB
  unfold andStep
  obtain ⟨I1, R1, ⟨E1, hE1, hl1⟩, eP1, eL1⟩ := sAnd_ok s A.p B.l hI hAp hBl (Or.inl ⟨hAmp, hBml⟩)
  generalize sAnd N s A.p B.l = o1 at I1 R1 hE1 eP1 eL1 ⊢
  obtain ⟨I2, R2, ⟨E2, hE2, hl2⟩, eP2, eL2⟩ := sAnd_ok o1.1 A.l B.p I1
    (by rw [hE1]; exact rep_ext _ hAl) (by rw [hE1]; exact rep_ext _ hBp)
    (Or.inr ⟨by rw [eL1]; exact hAml, by rw [eP1]; exact hBmp⟩)
  generalize sAnd N o1.1 A.l B.p = o2 at I2 R2 hE2 eP2 eL2 ⊢
  obtain ⟨I3, R3, ⟨E3, hE3, hl3⟩, sP3, sL3, -, -⟩ :=
    sOr_ok 2 o2.1 o1.2 o2.2 I2 (by rw [hE2]; exact rep_ext _ R1) R2
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
  generalize sOr N 2 o2.1 o1.2 o2.2 = o3 at I3 R3 hE3 sP3 sL3 ⊢
  obtain ⟨I4, R4, ⟨E4, hE4, hl4⟩, sP4, sL4, -, -⟩ :=
    sOr_ok 2 o3.1 A.r B.r I3 (by rw [hE3, hE2, hE1]; exact rep_ext _ (rep_ext _ (rep_ext _ hAr)))
      (by rw [hE3, hE2, hE1]; exact rep_ext _ (rep_ext _ (rep_ext _ hBr)))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
  generalize sOr N 2 o3.1 A.r B.r = o4 at I4 R4 hE4 sP4 sL4 ⊢
  obtain ⟨I5, R5, ⟨E5, hE5, hl5⟩, sP5, sL5, -, -⟩ :=
    sOr_ok 2 o4.1 o3.2 o4.2 I4 (by rw [hE4]; exact rep_ext _ R3) R4
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
  generalize sOr N 2 o4.1 o3.2 o4.2 = o5 at I5 R5 hE5 sP5 sL5 ⊢
  refine ⟨I5, ⟨E1 ++ E2 ++ E3 ++ E4 ++ E5, by rw [hE5, hE4, hE3, hE2, hE1]; simp,
    by simp; omega⟩, by rw [← eP1, ← eP2]; exact sP3.trans (sP4.trans sP5),
    by rw [← eL1, ← eL2]; exact sL3.trans (sL4.trans sL5), ?_, (fun w hw => by cases hw), ?_,
    (fun w hw => by cases hw), ?_⟩
  · intro z
    simp [PFf, hsP]
  · intro z
    simp [LFf, hsL]
  · refine ⟨_, R5, fun z hz => ?_, fun p l hpl hG hp hl => ?_⟩
    · simp only [Bool.or_eq_true, Bool.and_eq_true] at hz
      rcases hz with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h | h
      · simp only [PFf, LFf, decide_eq_true_eq] at h1 h2
        obtain ⟨p, hzp, hGa⟩ := h1
        obtain ⟨l, hzl, hGb⟩ := h2
        refine ⟨p, l, hcl p l ?_, hzp, hzl⟩
        rw [Bool.and_eq_true]
        exact ⟨hmA _ _ (ep_le p l) hGa, hmB _ _ (el_le p l) hGb⟩
      · simp only [PFf, LFf, decide_eq_true_eq] at h1 h2
        obtain ⟨l, hzl, hGa⟩ := h1
        obtain ⟨p, hzp, hGb⟩ := h2
        refine ⟨p, l, hcl p l ?_, hzp, hzl⟩
        rw [Bool.and_eq_true]
        exact ⟨hmA _ _ (el_le p l) hGa, hmB _ _ (ep_le p l) hGb⟩
      · exact hAs z h
      · exact hBs z h
    · simp only [Bool.and_eq_true] at hG
      simp only [Bool.or_eq_true, Bool.and_eq_true]
      by_cases ha0 : Ga (ep N p) = false ∧ Ga (el N l) = false
      · exact Or.inr (Or.inl (hAc p l hpl hG.1 ha0.1 ha0.2))
      by_cases hb0 : Gb (ep N p) = false ∧ Gb (el N l) = false
      · exact Or.inr (Or.inr (hBc p l hpl hG.2 hb0.1 hb0.2))
      have ha1 : Ga (ep N p) = true ∨ Ga (el N l) = true := by
        by_contra hc
        simp only [not_or, Bool.not_eq_true] at hc
        exact ha0 hc
      have hb1 : Gb (ep N p) = true ∨ Gb (el N l) = true := by
        by_contra hc
        simp only [not_or, Bool.not_eq_true] at hc
        exact hb0 hc
      have hpc : PFf N Ga (epl N p l) = true ∨ True := Or.inr trivial
      clear hpc
      rcases ha1 with ha1 | ha1 <;> rcases hb1 with hb1 | hb1
      · simp [ha1, hb1] at hp
      · refine Or.inl (Or.inl ⟨?_, ?_⟩)
        · simp only [PFf, decide_eq_true_eq]
          exact ⟨p, epl_c p l, ha1⟩
        · simp only [LFf, decide_eq_true_eq]
          exact ⟨l, epl_n p l, hb1⟩
      · refine Or.inl (Or.inr ⟨?_, ?_⟩)
        · simp only [LFf, decide_eq_true_eq]
          exact ⟨l, epl_n p l, ha1⟩
        · simp only [PFf, decide_eq_true_eq]
          exact ⟨p, epl_c p l, hb1⟩
      · simp [ha1, hb1] at hl

theorem wok_none {N : ℕ} {I : Fin N → Fin N → Prop} {H : List Gate} {P L : Finset ℕ}
    {G : (Fin (N + N) → Bool) → Bool} (h1 : ∀ p, G (ep N p) = false)
    (h2 : ∀ l, G (el N l) = false) (h3 : ∀ p l, G (epl N p l) = true → False) :
    WOk N I H P L ⟨none, none, none⟩ G := by
  refine ⟨fun z => by simp [PFf, h1], (fun w hw => by cases hw), fun z => by simp [LFf, h2],
    (fun w hw => by cases hw), fun _ => false, fun z => rfl, (fun z hz => by cases hz),
    fun p l _ hG _ _ => (h3 p l hG).elim⟩

theorem mono_fo (G : List Gate) (hG : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ x y : List Bool, x.length = y.length → (∀ i, x.getD i false = true → y.getD i false = true) →
    ∀ i, (fo false Φb G x).getD i false = true → (fo false Φb G y).getD i false = true := by
  induction G with
  | nil => intro x y _ hxy; simpa [fo] using hxy
  | cons g G ih =>
    intro x y hl hxy
    have hg := hG g List.mem_cons_self
    have key : Φb g (g.inputs.map fun i => x.getD i false) = true →
        Φb g (g.inputs.map fun i => y.getD i false) = true := by
      rcases hg with h | h
      · simp only [Φb, h, GateOp.eval, List.all_eq_true, List.mem_map]
        intro H b hb
        obtain ⟨a, ha, rfl⟩ := hb
        exact hxy a (H _ ⟨a, ha, rfl⟩)
      · simp only [Φb, h, GateOp.eval, List.any_eq_true, List.mem_map]
        rintro ⟨b, ⟨a, ha, rfl⟩, hb⟩
        exact ⟨_, ⟨a, ha, rfl⟩, hxy a hb⟩
    show ∀ i, (fo false Φb G (x ++ [Φb g (g.inputs.map fun i => x.getD i false)])).getD i false = true →
      (fo false Φb G (y ++ [Φb g (g.inputs.map fun i => y.getD i false)])).getD i false = true
    apply ih (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · intro i hi
      rcases lt_trichotomy i x.length with h | h | h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h] at hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
        exact hxy i hi
      · subst h
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self] at hi
        rw [List.getD_eq_getElem?_getD, hl, List.getElem?_append_right (le_refl _), Nat.sub_self]
        exact key hi
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
        cases hi

theorem ofFn_le {n : ℕ} (z z' : Fin n → Bool) (h : ∀ k, z k = true → z' k = true) :
    ∀ i, (List.ofFn z).getD i false = true → (List.ofFn z').getD i false = true := by
  intro i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
  by_cases hin : i < n
  · simp only [hin, ↓reduceDIte] at hi ⊢
    exact h _ hi
  · simp [hin] at hi

theorem mono_gv (G : List Gate) (hG : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or) {n : ℕ}
    (w : ℕ) (z z' : Fin n → Bool) (h : ∀ k, z k = true → z' k = true) :
    gv false Φb G (List.ofFn z) w = true → gv false Φb G (List.ofFn z') w = true :=
  mono_fo G hG _ _ (by simp) (ofFn_le z z' h) w


def gstep (N : ℕ) (s : Sx) (M : ℕ → Tr) (g : Gate) : Sx × Tr :=
  match g with
  | ⟨GateOp.or, [a, b]⟩ => orStep N s (M a) (M b)
  | ⟨GateOp.and, [a, b]⟩ => andStep N s (M a) (M b)
  | ⟨GateOp.or, [a]⟩ => (s, M a)
  | ⟨GateOp.and, [a]⟩ => (s, M a)
  | _ => (s, ⟨none, none, none⟩)

def T0 (N w : ℕ) : Tr :=
  if w < N then ⟨some w, none, none⟩ else if w < N + N then ⟨none, some w, none⟩
  else ⟨none, none, none⟩

def build (N : ℕ) (C : Circuit) : ℕ → Sx × (ℕ → Tr)
  | 0 => (⟨[], Finset.range N, Finset.Ico N (N + N)⟩, T0 N)
  | j + 1 => ((gstep N (build N C j).1 (build N C j).2 (C.gates.getD j gd)).1,
      fun w => if w = N + N + j then (gstep N (build N C j).1 (build N C j).2 (C.gates.getD j gd)).2
        else (build N C j).2 w)

def gC (C : Circuit) {n : ℕ} (z : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn z)).getD w false

theorem gC_eq (C : Circuit) {n : ℕ} (z : Fin n → Bool) (w : ℕ) :
    gC C z w = gv false Φb C.gates (List.ofFn z) w := rfl

def Good (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) (s : Sx) (M : ℕ → Tr) : Prop :=
  Inv N s.H s.P s.L ∧ s.H.length ≤ 5 * j ∧
  ∀ w < N + N + j, WOk N I s.H s.P s.L (M w) (fun z => gC C z w)

theorem eval_and2 (x y : Bool) : GateOp.and.eval [x, y] = (x && y) := by
  cases x <;> cases y <;> rfl

theorem eval_or2 (x y : Bool) : GateOp.or.eval [x, y] = (x || y) := by
  cases x <;> cases y <;> rfl

theorem eval_and1 (x : Bool) : GateOp.and.eval [x] = x := by
  cases x <;> rfl

theorem eval_or1 (x : Bool) : GateOp.or.eval [x] = x := by
  cases x <;> rfl

theorem getD_ofFn {n : ℕ} (z : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn z).getD w false = z ⟨w, hw⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hw]

theorem pf_input_lt {N : ℕ} (k : Fin (N + N)) (hk : k.val < N) (z : Fin (N + N) → Bool) :
    PFf N (fun z => z k) z = z k := by
  apply Bool.eq_iff_iff.2
  simp only [PFf, ep, decide_eq_true_eq]
  constructor
  · rintro ⟨p, h1, rfl⟩
    exact h1
  · intro h
    have e : Fin.castAdd N (⟨k.val, hk⟩ : Fin N) = k := Fin.ext rfl
    exact ⟨⟨k.val, hk⟩, by rw [e]; exact h, e.symm⟩

theorem pf_input_ge {N : ℕ} (k : Fin (N + N)) (hk : N ≤ k.val) (z : Fin (N + N) → Bool) :
    PFf N (fun z => z k) z = false := by
  simp only [PFf, ep, decide_eq_true_eq, decide_eq_false_iff_not, not_exists, not_and]
  intro p _ h
  rw [h] at hk
  simp only [Fin.val_castAdd] at hk
  have := p.isLt
  omega

theorem lf_input_ge {N : ℕ} (k : Fin (N + N)) (hk : N ≤ k.val) (z : Fin (N + N) → Bool) :
    LFf N (fun z => z k) z = z k := by
  apply Bool.eq_iff_iff.2
  simp only [LFf, el, decide_eq_true_eq]
  constructor
  · rintro ⟨p, h1, rfl⟩
    exact h1
  · intro h
    have e : Fin.natAdd N (⟨k.val - N, by omega⟩ : Fin N) = k := Fin.ext (by simp; omega)
    exact ⟨⟨k.val - N, by omega⟩, by rw [e]; exact h, e.symm⟩

theorem lf_input_lt {N : ℕ} (k : Fin (N + N)) (hk : k.val < N) (z : Fin (N + N) → Bool) :
    LFf N (fun z => z k) z = false := by
  simp only [LFf, el, decide_eq_true_eq, decide_eq_false_iff_not, not_exists, not_and]
  intro p _ h
  rw [h] at hk
  simp only [Fin.val_natAdd] at hk
  omega

theorem rnone_input {N : ℕ} {I : Fin N → Fin N → Prop} (k : Fin (N + N)) :
    ∀ p l, I p l → (fun z : Fin (N + N) → Bool => z k) (epl N p l) = true →
      (fun z : Fin (N + N) → Bool => z k) (ep N p) = false →
      (fun z : Fin (N + N) → Bool => z k) (el N l) = false →
      (fun _ : Fin (N + N) → Bool => false) (epl N p l) = true := by
  intro p l _ hG hp hl
  simp only [epl, ep, el, Bool.or_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] at hG hp hl
  rcases hG with h | h
  · exact absurd h hp
  · exact absurd h hl

theorem base_good {N : ℕ} {I : Fin N → Fin N → Prop} (C : Circuit) :
    Good N I C 0 (build N C 0).1 (build N C 0).2 := by
  refine ⟨⟨fun w hw => Or.inl (Finset.mem_range.1 hw),
    fun w hw => Or.inl (by simpa using Finset.mem_Ico.1 hw), fun i hi => by simp [build] at hi,
    fun g hg => by simp [build] at hg, fun i hi => by simp [build] at hi⟩, le_refl _, fun w hw => ?_⟩
  have hw' : w < N + N := by omega
  have hin : ∀ z : Fin (N + N) → Bool, gC C z w = z ⟨w, hw'⟩ := by
    intro z
    rw [gC_eq, gv_input false Φb C.gates (List.ofFn z) w (by simp; omega), getD_ofFn z w hw']
  have hfun : (fun z => gC C z w) = fun z => z ⟨w, hw'⟩ := funext hin
  rw [hfun]
  show WOk N I [] (Finset.range N) (Finset.Ico N (N + N)) (T0 N w) _
  have hgv : ∀ z : Fin (N + N) → Bool, gv false Φb [] (List.ofFn z) w = z ⟨w, hw'⟩ := by
    intro z
    rw [gv_input false Φb [] (List.ofFn z) w (by simp; omega), getD_ofFn z w hw']
  by_cases h1 : w < N
  · have e : T0 N w = ⟨some w, none, none⟩ := by simp [T0, h1]
    rw [e]
    refine ⟨⟨by simp; omega, fun z => ?_⟩, fun v hv => ?_,
      fun z => lf_input_lt ⟨w, hw'⟩ h1 z, (fun v hv => by cases hv), fun _ => false,
      fun z => rfl, (fun z hz => by cases hz), rnone_input ⟨w, hw'⟩⟩
    · rw [hgv, pf_input_lt ⟨w, hw'⟩ h1 z]
    · cases hv
      exact Finset.mem_range.2 h1
  · have e : T0 N w = ⟨none, some w, none⟩ := by simp [T0, h1, hw']
    rw [e]
    refine ⟨fun z => pf_input_ge ⟨w, hw'⟩ (by simp; omega) z, (fun v hv => by cases hv),
      ⟨by simp; omega, fun z => ?_⟩, fun v hv => ?_, fun _ => false,
      fun z => rfl, (fun z hz => by cases hz), rnone_input ⟨w, hw'⟩⟩
    · rw [hgv, lf_input_ge ⟨w, hw'⟩ (by simp; omega) z]
    · cases hv
      exact Finset.mem_Ico.2 ⟨by omega, hw'⟩

theorem step_ok {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} (j : ℕ) (s : Sx) (M : ℕ → Tr)
    (hG : Good N I C j s M) (hj : j < C.gates.length)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C)
    (hS : (C.gates.getD j gd).op = GateOp.and →
      (∀ p, gC C (ep N p) (N + N + j) = false) ∧ ∀ l, gC C (el N l) (N + N + j) = false)
    (hK : (C.gates.getD j gd).op = GateOp.and → ∀ p l,
      gC C (epl N p l) (N + N + j) = true → I p l) :
    Good N I C (j + 1) (gstep N s M (C.gates.getD j gd)).1
      (fun w => if w = N + N + j then (gstep N s M (C.gates.getD j gd)).2 else M w) := by
  obtain ⟨hI, hlen, hW⟩ := hG
  have hval : ∀ z : Fin (N + N) → Bool, gC C z (N + N + j) =
      (C.gates.getD j gd).op.eval ((C.gates.getD j gd).inputs.map (fun u => gC C z u)) := by
    intro z
    have := gv_gate false Φb C.gates (List.ofFn z) (by rw [List.length_ofFn]; exact hrb) j hj
    rw [List.length_ofFn] at this
    exact this
  have hin : ∀ u ∈ (C.gates.getD j gd).inputs, u < N + N + j := hrb j hj
  have hmem : C.gates.getD j gd ∈ C.gates := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hmono g hg).1
    simpa using this
  have hmonoC : ∀ u (z z' : Fin (N + N) → Bool), (∀ k, z k = true → z' k = true) →
      gC C z u = true → gC C z' u = true := fun u z z' h => mono_gv C.gates hops u z z' h
  have hmon2 := hmono _ hmem
  have key : Inv N (gstep N s M (C.gates.getD j gd)).1.H (gstep N s M (C.gates.getD j gd)).1.P
        (gstep N s M (C.gates.getD j gd)).1.L ∧
      (∃ E : List Gate, (gstep N s M (C.gates.getD j gd)).1.H = s.H ++ E ∧ E.length ≤ 5) ∧
      s.P ⊆ (gstep N s M (C.gates.getD j gd)).1.P ∧ s.L ⊆ (gstep N s M (C.gates.getD j gd)).1.L ∧
      WOk N I (gstep N s M (C.gates.getD j gd)).1.H (gstep N s M (C.gates.getD j gd)).1.P
        (gstep N s M (C.gates.getD j gd)).1.L (gstep N s M (C.gates.getD j gd)).2
        (fun z => gC C z (N + N + j)) := by
    generalize C.gates.getD j gd = g at hval hin hmon2 hS hK
    obtain ⟨op, ins⟩ := g
    obtain ⟨hop, hl2⟩ := hmon2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · refine ⟨hI, ⟨[], (List.append_nil _).symm, by simp⟩, subset_refl _, subset_refl _, ?_⟩
      apply wok_none (fun p => (hS rfl).1 p) (fun l => (hS rfl).2 l)
      intro p l _
      have := (hS rfl).1 p
      rw [hval] at this
      simp [GateOp.eval] at this
    · refine ⟨hI, ⟨[], (List.append_nil _).symm, by simp⟩, subset_refl _, subset_refl _, ?_⟩
      have hf : (fun z : Fin (N + N) → Bool => gC C z (N + N + j)) = fun z : Fin (N + N) → Bool => gC C z a := by
        funext z
        rw [hval]
        simp only [List.map_cons, List.map_nil, eval_and1]
      rw [hf]
      exact hW a (hin a (by simp))
    · have hf : (fun z : Fin (N + N) → Bool => gC C z (N + N + j)) = fun z : Fin (N + N) → Bool => gC C z a && gC C z b := by
        funext z
        rw [hval]
        simp only [List.map_cons, List.map_nil, eval_and2]
      have ha := hin a (by simp)
      have hb := hin b (by simp)
      rw [hf]
      exact and_case s (M a) (M b) hI (hW a ha) (hW b hb) (hmonoC a) (hmonoC b)
        (fun p => by
          have := (hS rfl).1 p
          rw [hval] at this
          simp only [List.map_cons, List.map_nil, eval_and2] at this
          exact this)
        (fun l => by
          have := (hS rfl).2 l
          rw [hval] at this
          simp only [List.map_cons, List.map_nil, eval_and2] at this
          exact this)
        (fun p l h => hK rfl p l (by
          rw [hval]
          simp only [List.map_cons, List.map_nil, eval_and2]
          exact h))
    · simp at hl2
    · refine ⟨hI, ⟨[], (List.append_nil _).symm, by simp⟩, subset_refl _, subset_refl _, ?_⟩
      apply wok_none
      · intro p
        rw [hval]
        rfl
      · intro l
        rw [hval]
        rfl
      · intro p l h
        rw [hval] at h
        cases h
    · refine ⟨hI, ⟨[], (List.append_nil _).symm, by simp⟩, subset_refl _, subset_refl _, ?_⟩
      have hf : (fun z : Fin (N + N) → Bool => gC C z (N + N + j)) = fun z : Fin (N + N) → Bool => gC C z a := by
        funext z
        rw [hval]
        simp only [List.map_cons, List.map_nil, eval_or1]
      rw [hf]
      exact hW a (hin a (by simp))
    · have hf : (fun z : Fin (N + N) → Bool => gC C z (N + N + j)) = fun z : Fin (N + N) → Bool => gC C z a || gC C z b := by
        funext z
        rw [hval]
        simp only [List.map_cons, List.map_nil, eval_or2]
      have ha := hin a (by simp)
      have hb := hin b (by simp)
      rw [hf]
      exact or_case s (M a) (M b) hI (hW a ha) (hW b hb)
    · simp at hl2
  obtain ⟨kI, ⟨E, hE, hEl⟩, kP, kL, kW⟩ := key
  refine ⟨kI, by rw [hE, List.length_append]; omega, fun w hw => ?_⟩
  show WOk N I _ _ _ (if w = N + N + j then _ else M w) _
  by_cases hw' : w = N + N + j
  · subst hw'
    simp only [↓reduceIte]
    exact kW
  · simp only [hw', ↓reduceIte]
    rw [hE]
    exact wok_ext (hW w (by omega)) E kP kL

theorem build_good {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit}
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C)
    (hS : ∀ j < C.gates.length, (C.gates.getD j gd).op = GateOp.and →
      (∀ p, gC C (ep N p) (N + N + j) = false) ∧ ∀ l, gC C (el N l) (N + N + j) = false)
    (hK : ∀ j < C.gates.length, (C.gates.getD j gd).op = GateOp.and → ∀ p l,
      gC C (epl N p l) (N + N + j) = true → I p l) :
    ∀ j ≤ C.gates.length, Good N I C j (build N C j).1 (build N C j).2 := by
  intro j
  induction j with
  | zero => intro _; exact base_good C
  | succ j ih =>
    intro hj
    exact step_ok j _ _ (ih (by omega)) (by omega) hmono hrb (hS j (by omega)) (hK j (by omega))


theorem pp_epl {N : ℕ} (p l : Fin N) :
    (fun ka : Fin (N + N) => decide (ka.val < N) && epl N p l ka) = ep N p := by
  funext ka
  apply Bool.eq_iff_iff.2
  simp only [epl, ep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff,
    Fin.val_castAdd, Fin.val_natAdd]
  have := p.isLt
  omega

theorem lp_epl {N : ℕ} (p l : Fin N) :
    (fun kb : Fin (N + N) => decide (N ≤ kb.val) && epl N p l kb) = el N l := by
  funext kb
  apply Bool.eq_iff_iff.2
  simp only [epl, el, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff,
    Fin.val_castAdd, Fin.val_natAdd]
  have := p.isLt
  omega

theorem epl_cast {N : ℕ} (p l p' : Fin N) (h : epl N p l (Fin.castAdd N p') = true) : p' = p := by
  simp only [epl, Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd,
    Fin.val_natAdd] at h
  have := p'.isLt
  apply Fin.ext
  omega

theorem epl_nat {N : ℕ} (p l l' : Fin N) (h : epl N p l (Fin.natAdd N l') = true) : l' = l := by
  simp only [epl, Bool.or_eq_true, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd,
    Fin.val_natAdd] at h
  have := p.isLt
  apply Fin.ext
  omega

theorem ep_nat {N : ℕ} (p l : Fin N) : ep N p (Fin.natAdd N l) = false := by
  simp only [ep, decide_eq_false_iff_not, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
  have := p.isLt
  omega

theorem el_cast {N : ℕ} (p l : Fin N) : el N l (Fin.castAdd N p) = false := by
  simp only [el, decide_eq_false_iff_not, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
  have := p.isLt
  omega

theorem rep_mono {N : ℕ} {H : List Gate} {P L : Finset ℕ} {t : Option ℕ}
    {φ : (Fin (N + N) → Bool) → Bool} (hI : Inv N H P L) (hR : Rep N H t φ)
    (z z' : Fin (N + N) → Bool) (h : ∀ k, z k = true → z' k = true) :
    φ z = true → φ z' = true := by
  cases t with
  | none =>
    intro hz
    rw [show φ z = false from hR z] at hz
    cases hz
  | some w =>
    obtain ⟨_, h2⟩ := hR
    rw [← h2 z, ← h2 z']
    exact mono_gv H (fun g hg => (hI.2.2.2.1 g hg).1) w z z' h

def outOf (N : ℕ) (H : List Gate) : Option ℕ → ℕ
  | none => N + N + H.length
  | some w => w

theorem out_eval {N : ℕ} {H : List Gate} {t : Option ℕ} {φ : (Fin (N + N) → Bool) → Bool}
    (hR : Rep N H t φ) (y : Fin (N + N) → Bool) :
    PEqualNP.MetaComplexity.circuitFun (N + N) ⟨H, outOf N H t⟩ y = φ y := by
  cases t with
  | none =>
    rw [show φ y = false from hR y]
    show gv false Φb H (List.ofFn y) (N + N + H.length) = false
    exact gv_oob false Φb H _ _ (by simp)
  | some w =>
    exact hR.2 y

end PEqualNP.Outside.L_meta_2052

open PEqualNP.Outside.L_meta_2052

theorem PEqualNP.Outside.L_meta_2052 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → (C.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j) false = true ∨ (C.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (C.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ 5 * C.size ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = true ↔ ∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true) ∧ (∀ w ∈ P, w < N ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (N ≤ w ∧ w < N + N) ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  intro N I _ C _ hmono hrb hfun hclean hsing
  have hS : ∀ j < C.gates.length, (C.gates.getD j gd).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (∀ p, gC C (ep N p) (N + N + j) = false) ∧ ∀ l, gC C (el N l) (N + N + j) = false :=
    fun j hj h => hsing j hj h
  have hK : ∀ j < C.gates.length, (C.gates.getD j gd).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ p l, gC C (epl N p l) (N + N + j) = true → I p l := by
    intro j hj hand p l h
    rcases hclean j hj hand (epl N p l) h with h' | h' | ⟨p', l', hI', h1, h2⟩
    · rw [pp_epl] at h'
      have := (hsing j hj hand).1 p
      exact absurd h' (by rw [Bool.not_eq_true]; exact this)
    · rw [lp_epl] at h'
      have := (hsing j hj hand).2 l
      exact absurd h' (by rw [Bool.not_eq_true]; exact this)
    · rw [epl_cast p l p' h1] at hI'
      rw [epl_nat p l l' h2] at hI'
      exact hI'
  obtain ⟨hI, hlen, hW⟩ := build_good (I := I) hmono hrb hS hK C.gates.length le_rfl
  have hf : ∀ z : Fin (N + N) → Bool, gC C z C.output = true ↔ FF N I z := hfun
  have hout : ∃ (t : Option ℕ) (φ : (Fin (N + N) → Bool) → Bool),
      Rep N (build N C C.gates.length).1.H t φ ∧ ∀ y, φ y = true ↔ FF N I y := by
    by_cases ho : C.output < N + N + C.gates.length
    · obtain ⟨-, -, -, -, φ, hR, hsd, hcp⟩ := hW C.output ho
      refine ⟨_, φ, hR, fun y => ⟨hsd y, fun hy => ?_⟩⟩
      obtain ⟨p, l, hpl, hyp, hyl⟩ := hy
      have h1 : φ (epl N p l) = true := by
        apply hcp p l hpl ((hf _).2 ⟨p, l, hpl, epl_c p l, epl_n p l⟩)
        · rw [← Bool.not_eq_true, hf]
          rintro ⟨p', l', -, -, h2⟩
          rw [ep_nat] at h2
          cases h2
        · rw [← Bool.not_eq_true, hf]
          rintro ⟨p', l', -, h2, -⟩
          rw [el_cast] at h2
          cases h2
      refine rep_mono hI hR (epl N p l) y (fun k hk => ?_) h1
      simp only [epl, Bool.or_eq_true, decide_eq_true_eq] at hk
      rcases hk with rfl | rfl
      · exact hyp
      · exact hyl
    · refine ⟨none, fun _ => false, fun _ => rfl, fun y => ⟨(fun h => by cases h), fun hy => ?_⟩⟩
      exfalso
      have h1 : gC C y C.output = true := (hf y).2 hy
      rw [gC_eq, gv_oob false Φb C.gates _ _ (by simp; omega)] at h1
      cases h1
  obtain ⟨t, φ, hR, hφ⟩ := hout
  refine ⟨⟨(build N C C.gates.length).1.H, outOf N (build N C C.gates.length).1.H t⟩,
    (build N C C.gates.length).1.P, (build N C C.gates.length).1.L, ?_, hI.2.2.2.2, hlen,
    fun y => ?_, hI.1, hI.2.1, hI.2.2.1⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hI.2.2.2.1 g hg
    refine ⟨?_, by rw [h2]⟩
    rcases h1 with h | h <;> simp [h]
  · rw [out_eval hR y]
    exact hφ y
