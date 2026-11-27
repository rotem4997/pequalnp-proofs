import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19221_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_stepWire_len (gs : List Gate) :
    ∀ xs : List Bool, (gs.foldl stepWire xs).length = xs.length + gs.length := by
  induction gs with
  | nil => intro xs; simp
  | cons g gs ih =>
      intro xs
      simp only [List.foldl_cons, List.length_cons, ih, stepWire, List.length_append, List.length_nil]
      omega

theorem foldl_stepWire_getD_lt (gs : List Gate) :
    ∀ (xs : List Bool) (i : ℕ), i < xs.length →
      (gs.foldl stepWire xs).getD i false = xs.getD i false := by
  induction gs with
  | nil => intro xs i _; rfl
  | cons g gs ih =>
      intro xs i hi
      simp only [List.foldl_cons]
      rw [ih (stepWire xs g) i (by simp [stepWire]; omega)]
      exact List.getD_append _ _ _ _ hi

theorem getD_append_add (p w : List Bool) (i : ℕ) :
    (p ++ w).getD (i + p.length) false = w.getD i false := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
    rw [List.getD_eq_getElem _ _ hi]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_self (l : List Bool) (x : Bool) (n : ℕ) (h : l.length = n) :
    (l ++ [x]).getD n false = x := by
  subst h; simp

theorem oneEach_len (n : ℕ) (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]; omega

theorem oneEach_getD_left (n : ℕ) (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.1) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  by_cases h : i = u.1
  · rw [decide_eq_true (Fin.ext h : (⟨i, hi⟩ : Fin n) = u), decide_eq_true h]
  · rw [decide_eq_false (fun he => h (congrArg Fin.val he)), decide_eq_false h]

theorem oneEach_getD_right (n : ℕ) (u v : Fin n) (i : ℕ) (hi1 : n ≤ i) (hi2 : i < 2 * n) :
    (oneEach u v).getD i false = decide (i - n = v.1) := by
  unfold oneEach
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp; omega)]
  simp only [List.length_ofFn, List.getElem_ofFn]
  have hj : i - n < n := by omega
  by_cases h : i - n = v.1
  · rw [decide_eq_true (Fin.ext h : (⟨i - n, hj⟩ : Fin n) = v), decide_eq_true h]
  · rw [decide_eq_false (fun he => h (congrArg Fin.val he)), decide_eq_false h]


abbrev Sig (α : Type) := α → Bool

structure Net {α : Type} (input : α → List Bool) (N : ℕ) where
  gates : List Gate
  mono : Monotone2 ⟨gates, 0⟩
  len : ∀ z, (input z).length = N

variable {α : Type} {input : α → List Bool} {N : ℕ}

def Has (s : Net input N) (f : Sig α) : Prop :=
  ∃ w < N + s.gates.length, ∀ z, (s.gates.foldl stepWire (input z)).getD w false = f z

def Keeps (s t : Net input N) : Prop := ∀ {f : Sig α}, Has s f → Has t f

structure Ext (s t : Net input N) (cost : ℕ) : Prop where
  count : t.gates.length ≤ s.gates.length + cost
  keep : Keeps s t

theorem Ext.refl (s : Net input N) : Ext s s 0 :=
  ⟨by simp, fun h => h⟩

theorem Ext.trans {s t u : Net input N} {a b : ℕ} (h : Ext s t a) (g : Ext t u b) :
    Ext s u (a+b) :=
  ⟨by have := h.count; have := g.count; omega, fun hf => g.keep (h.keep hf)⟩

theorem Ext.mono {s t : Net input N} {a b : ℕ} (h : Ext s t a) (hle : a ≤ b) :
    Ext s t b := ⟨by have := h.count; omega, h.keep⟩

theorem gate_bin (s : Net input N) {a b : Sig α} (ha : Has s a) (hb : Has s b)
    (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∃ t, Ext s t 1 ∧ Has t (fun z => op.eval [a z, b z]) := by
  obtain ⟨i, hi, hvi⟩ := ha
  obtain ⟨j, hj, hvj⟩ := hb
  let g : Gate := ⟨op, [i,j]⟩
  let t : Net input N := ⟨s.gates ++ [g], by
    intro e he
    change e ∈ s.gates ++ [g] at he
    rcases List.mem_append.mp he with old | new
    · exact s.mono e old
    · have eq : e = g := by simpa using new
      subst e
      exact ⟨hop, by simp [g]⟩, s.len⟩
  refine ⟨t, ⟨by simp [t], ?_⟩, ?_⟩
  · intro f hf
    obtain ⟨w, hw, hv⟩ := hf
    refine ⟨w, by simp [t]; omega, ?_⟩
    intro z
    simpa only [t,List.foldl_append] using
      (foldl_stepWire_getD_lt [g] (s.gates.foldl stepWire (input z)) w
        (by simpa [foldl_stepWire_len,s.len] using hw)).trans (hv z)
  · refine ⟨N+s.gates.length, by simp [t], ?_⟩
    intro z
    change ((s.gates ++ [g]).foldl stepWire (input z)).getD _ false = _
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire]
    rw [getD_snoc_self _ _ _ (by simp [foldl_stepWire_len,s.len])]
    change op.eval [(s.gates.foldl stepWire (input z)).getD i false, (s.gates.foldl stepWire (input z)).getD j false] = _
    rw [hvi,hvj]

theorem gate_or (s : Net input N) {a b : Sig α} (ha : Has s a) (hb : Has s b) :
    ∃ t, Ext s t 1 ∧ Has t (fun z => a z || b z) := by
  simpa [GateOp.eval] using gate_bin s ha hb .or (by simp)

theorem gate_and (s : Net input N) {a b : Sig α} (ha : Has s a) (hb : Has s b) :
    ∃ t, Ext s t 1 ∧ Has t (fun z => a z && b z) := by
  simpa [GateOp.eval] using gate_bin s ha hb .and (by simp)

theorem many {ι : Type} [Fintype ι] (s : Net input N) (f : ι → Sig α) (c : ℕ)
    (step : ∀ (i : ι) (u : Net input N), Keeps s u →
      ∃ v, Ext u v c ∧ Has v (f i)) :
    ∃ t, Ext s t (Fintype.card ι * c) ∧ ∀ i, Has t (f i) := by
  classical
  have loop (l : List ι) : ∃ t, Ext s t (l.length*c) ∧ ∀ i ∈ l, Has t (f i) := by
    induction l with
    | nil => exact ⟨s, by simpa using Ext.refl s, by simp⟩
    | cons a l ih =>
      obtain ⟨u,hu,hl⟩ := ih
      obtain ⟨v,hv,ha⟩ := step a u hu.keep
      refine ⟨v,by simpa [Nat.succ_mul] using hu.trans hv,?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ha
      · exact hv.keep (hl i hi)
  obtain ⟨v,hv,ha⟩ := loop (Finset.univ : Finset ι).toList
  exact ⟨v, by simpa using hv, fun i => ha i (by simp)⟩

theorem any_list {ι : Type} (s : Net input N) (f : ι → Sig α) (l : List ι)
    (hne : l ≠ []) (hs : ∀ i ∈ l, Has s (f i)) :
    ∃ t, Ext s t (l.length-1) ∧ Has t (fun z => l.any (fun i => f i z)) := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    cases l with
    | nil => exact ⟨s, by simpa using Ext.refl s, by simpa using hs a (by simp)⟩
    | cons b bs =>
      obtain ⟨u,hu,hl⟩ := ih (by simp) (fun i hi => hs i (by simp [hi]))
      obtain ⟨v,hv,hh⟩ := gate_or u (hu.keep (hs a (by simp))) hl
      exact ⟨v, by simpa using hu.trans hv, by simpa using hh⟩

theorem any_family {ι : Type} [Fintype ι] [Nonempty ι] (s : Net input N)
    (f : ι → Sig α) (hs : ∀ i, Has s (f i)) :
    ∃ t, Ext s t (Fintype.card ι - 1) ∧
      Has t (fun z => decide (∃ i, f i z = true)) := by
  classical
  have hn : (Finset.univ : Finset ι).toList ≠ [] := by simpa using (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty).ne_empty
  obtain ⟨t,ht,hf⟩ := any_list s f _ hn (fun i _ => hs i)
  refine ⟨t, by simpa using ht, ?_⟩
  convert hf using 2
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true]

end PEqualNP.Outside.L_meta_19221_aux

namespace PEqualNP.Outside.L_meta_19221_aux

def addr (k b i j : Nat) := 2*b*(k*k) + i*k + j

private def point (k q i j : Nat) := (k*k)*q + (k*i + j)

private theorem lowPoint (k b i j : Nat) :
    addr k b i j = point k (2*b) i j := by unfold addr point; ring

private theorem highPoint (k b i j : Nat) :
    addr k b i j + k*k = point k (2*b+1) i j := by unfold addr point; ring

private theorem cell_lt {k : Nat} (i j : Fin k) : k*i.val+j.val < k*k := by
  calc k*i.val+j.val < k*i.val+k := Nat.add_lt_add_left j.isLt _
       _ = k*(i.val+1) := by ring
       _ ≤ k*k := Nat.mul_le_mul_left _ i.isLt

private theorem point_lt {k p q : Nat} (hq : q < 2*p) (i j : Fin k) :
    point k q i j < 2*p*(k*k) := by
  calc (k*k)*q + (k*i.val+j.val) < (k*k)*q + k*k := Nat.add_lt_add_left (cell_lt i j) _
       _ = (k*k)*(q+1) := by ring
       _ ≤ (k*k)*(2*p) := Nat.mul_le_mul_left _ hq
       _ = 2*p*(k*k) := Nat.mul_comm _ _

theorem addr_bounds {k p : Nat} (hk : 2 ≤ k) (b : Fin p) (i j : Fin k) :
    addr k b i j < 2*p*(k*k) ∧ addr k b i j + k*k < 2*p*(k*k) := by
  rw [highPoint, lowPoint]
  exact ⟨point_lt (by have := b.isLt; omega) i j, point_lt (by have := b.isLt; omega) i j⟩

private theorem point_components {k : Nat} (hk : 0 < k) (q : Nat) (i j : Fin k) :
    point k q i j / (k*k) = q ∧ point k q i j % (k*k) = k*i.val+j.val := by
  have hh := Nat.mul_pos hk hk
  exact ⟨by unfold point; rw [Nat.mul_add_div hh, Nat.div_eq_of_lt (cell_lt i j), Nat.add_zero],
    by unfold point; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (cell_lt i j)]⟩

private theorem cell_ne {k : Nat} (hk : 0 < k) (i j r c : Fin k)
    (hd : i ≠ r ∨ j ≠ c) : k*i.val+j.val ≠ k*r.val+c.val := by
  intro h
  have e := congrArg (fun z : Nat => z/k) h
  have f := congrArg (fun z : Nat => z%k) h
  simp only [Nat.mul_add_div hk, Nat.div_eq_of_lt j.isLt, Nat.div_eq_of_lt c.isLt, Nat.add_zero] at e
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt c.isLt] at f
  exact hd.elim (fun h => h (Fin.ext e)) (fun h => h (Fin.ext f))

private theorem decode (k x : Nat) (hk : 0 < k) : ∃ i j : Fin k,
    x = point k (x/(k*k)) i j ∧ x%(k*k) = k*i.val+j.val := by
  let d := x%(k*k)
  have dd : d < k*k := Nat.mod_lt _ (Nat.mul_pos hk hk)
  refine ⟨⟨d/k,(Nat.div_lt_iff_lt_mul hk).2 dd⟩, ⟨d%k,Nat.mod_lt _ hk⟩, ?_, ?_⟩
  · change x = (k*k)*(x/(k*k))+(k*(d/k)+d%k)
    rw [Nat.div_add_mod]; exact (Nat.div_add_mod x (k*k)).symm
  · exact (Nat.div_add_mod d k).symm

theorem index_iff {k p : Nat} (hk : 2 ≤ k) (u v : Fin (2*p*(k*k))) :
    (∃ (b : Fin p) (i j r c : Fin k),
      (u.val=addr k b i j ∨ v.val=addr k b i j+k*k) ∧
      (v.val=addr k b r c ∨ u.val=addr k b r c+k*k) ∧ (i≠r ∨ j≠c)) ↔
    u.val/(k*k)=v.val/(k*k) ∧ u.val % (k*k)≠v.val % (k*k) := by
  have hk' : 0 < k := by omega
  constructor
  · rintro ⟨b,i,j,r,c,hx,hy,hd⟩
    rw [highPoint,lowPoint] at hx hy
    have J0 := point_components hk' (2*b.val) i j
    have J1 := point_components hk' (2*b.val+1) i j
    have C0 := point_components hk' (2*b.val) r c
    have C1 := point_components hk' (2*b.val+1) r c
    have ne := cell_ne hk' i j r c hd
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hx,hy,J0.1,C0.1,J0.2,C0.2]; exact ⟨rfl,ne⟩
    · have impossible := congrArg (fun x : Nat => x/(k*k)) (hx.symm.trans hy)
      change point k (2*b.val) i j / (k*k) = point k (2*b.val+1) r c / (k*k) at impossible
      rw [J0.1,C1.1] at impossible; omega
    · have impossible := congrArg (fun x : Nat => x/(k*k)) (hx.symm.trans hy)
      change point k (2*b.val+1) i j / (k*k) = point k (2*b.val) r c / (k*k) at impossible
      rw [J1.1,C0.1] at impossible; omega
    · rw [hy,hx,C1.1,J1.1,C1.2,J1.2]; exact ⟨rfl,ne.symm⟩
  · rintro ⟨same,ne⟩
    obtain ⟨i,j,eu,um⟩ := decode k u.val hk'
    obtain ⟨r,c,ev,vm⟩ := decode k v.val hk'
    have diff : i ≠ r ∨ j ≠ c := by
      by_contra! h; exact ne (by rw [um,vm,h.1,h.2])
    have small : u.val/(k*k) < 2*p := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hk' hk')).2 u.isLt
    let b : Fin p := ⟨u.val/(k*k)/2, by omega⟩
    rcases (show u.val/(k*k) = 2*b.val ∨ u.val/(k*k) = 2*b.val+1 by dsimp [b]; omega) with q | q
    · refine ⟨b,i,j,r,c,Or.inl ?_,Or.inl ?_,diff⟩
      · exact eu.trans (by rw [lowPoint,q])
      · exact ev.trans (by rw [lowPoint,← same,q])
    · refine ⟨b,r,c,i,j,Or.inr ?_,Or.inr ?_,diff.imp Ne.symm Ne.symm⟩
      · exact ev.trans (by rw [highPoint,← same,q])
      · exact eu.trans (by rw [highPoint,q])

end PEqualNP.Outside.L_meta_19221_aux

namespace PEqualNP.Outside.L_meta_19221_aux
variable {α : Type} {input : α → List Bool} {N : ℕ}

private def omitted {k : ℕ} (f : Fin k → Sig α) (i : Fin k) : Sig α :=
  fun z => decide (∃ j : Fin k, j ≠ i ∧ f j z = true)

private theorem exceptAux (n : ℕ) (s : Net input N) (f : Fin (n+2) → Sig α)
    (hs : ∀ i, Has s (f i)) :
    ∃ t, Ext s t (3*n) ∧ ∀ i, Has t (omitted f i) := by
  induction n generalizing s with
  | zero =>
    refine ⟨s, by simpa using Ext.refl s, ?_⟩
    intro i
    fin_cases i
    · convert hs (1 : Fin 2) using 1
      funext z
      apply Bool.eq_iff_iff.mpr
      simp [omitted, Fin.exists_fin_succ]
    · convert hs (0 : Fin 2) using 1
      funext z
      apply Bool.eq_iff_iff.mpr
      simp [omitted, Fin.exists_fin_succ]
  | succ n ih =>
    let g : Fin (n+2) → Sig α := Fin.cases
        (fun z => f 0 z || f (Fin.succ 0) z)
        (fun i => f i.succ.succ)
    obtain ⟨a, ha, h01⟩ := gate_or s (hs 0) (hs (Fin.succ 0))
    have hg : ∀ i, Has a (g i) := by
      refine Fin.cases ?_ (fun i => ?_)
      · exact h01
      · exact ha.keep (hs i.succ.succ)
    obtain ⟨b, hb, hbank⟩ := ih a g hg
    obtain ⟨c, hc, h0⟩ := gate_or b (hb.keep (ha.keep (hs (Fin.succ 0)))) (hbank 0)
    obtain ⟨d, hd, h1⟩ := gate_or c (hc.keep (hb.keep (ha.keep (hs 0)))) (hc.keep (hbank 0))
    refine ⟨d, ((ha.trans hb).trans hc |>.trans hd).mono (by omega), ?_⟩
    refine Fin.cases ?_ (Fin.cases ?_ (fun i => ?_))
    · convert hd.keep h0 using 1
      funext z
      apply Bool.eq_iff_iff.mpr
      simp [omitted, g, Fin.exists_fin_succ]
    · convert h1 using 1
      funext z
      apply Bool.eq_iff_iff.mpr
      have two : (2 : Fin (n+3)) ≠ 1 := by
        intro e
        have q := congrArg Fin.val e
        simp only [Fin.val_two, Fin.val_one] at q
        omega
      have tri (j : Fin n) : j.succ.succ.succ ≠ (1 : Fin (n+3)) := by
        intro e
        have q := congrArg Fin.val e
        simp only [Fin.val_succ, Fin.val_one] at q
        omega
      simp [omitted, g, Fin.exists_fin_succ, two, tri]
    · convert hd.keep (hc.keep (hbank i.succ)) using 1
      funext z
      apply Bool.eq_iff_iff.mpr
      have nz {m : ℕ} (j : Fin m) : (0 : Fin (m+1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
      simp [omitted, g, Fin.exists_fin_succ, nz, or_assoc]

theorem all_except {k : ℕ} (hk : 2 ≤ k) (s : Net input N) (f : Fin k → Sig α)
    (hs : ∀ i, Has s (f i)) :
    ∃ t, Ext s t (3*k-6) ∧ ∀ i, Has t (fun z => decide (∃ j : Fin k, j ≠ i ∧ f j z = true)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n+2 := ⟨k-2, by omega⟩
  obtain ⟨t, ht, hb⟩ := exceptAux n s f hs
  exact ⟨t, ht.mono (by omega), hb⟩

end PEqualNP.Outside.L_meta_19221_aux

namespace PEqualNP.Outside.L_meta_19221_aux

variable {α : Type} {input : α → List Bool} {N k : ℕ}

theorem strict_crown (s : Net input N) (hk : 2 ≤ k) (A B : Fin k → Sig α)
    (hA : ∀ i, Has s (A i)) (hB : ∀ i, Has s (B i)) :
    ∃ t, Ext s t (5*k-7) ∧ Has t (fun z =>
      decide (∃ i j : Fin k, i ≠ j ∧ A i z = true ∧ B j z = true)) := by
  classical
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let side (i : Fin k) (z : α) := decide (∃ j : Fin k, j ≠ i ∧ B j z = true)
  let term (i : Fin k) (z : α) := A i z && side i z
  obtain ⟨u,hu,allB⟩ := all_except hk s B hB
  obtain ⟨v,hv,allT⟩ := many u term 1 (by
    intro i w hw
    exact gate_and w (hw (hu.keep (hA i))) (hw (allB i)))
  obtain ⟨t,ht,final⟩ := any_family v term allT
  refine ⟨t, ((hu.trans hv).trans ht).mono (by simp; omega), ?_⟩
  obtain ⟨w,hw,hval⟩ := final
  refine ⟨w,hw,?_⟩
  intro z
  rw [hval z]
  apply Bool.eq_iff_iff.mpr
  simp only [term,side,decide_eq_true_eq,Bool.and_eq_true]
  constructor
  · rintro ⟨i, hAi, j, hji, hBj⟩
    exact ⟨i, j, hji.symm, hAi, hBj⟩
  · rintro ⟨i, j, hij, hAi, hBj⟩
    exact ⟨i, hAi, j, hij.symm, hBj⟩


end PEqualNP.Outside.L_meta_19221_aux

namespace PEqualNP.Outside.L_meta_19221_aux

variable {α : Type} {input : α → List Bool} {N k : ℕ}
abbrev Grid (k : ℕ) (α : Type) := Fin k → Fin k → Sig α

def rowAny (A : Grid k α) (i : Fin k) (z : α) : Bool :=
  decide (∃ j, A i j z = true)
def colAny (A : Grid k α) (j : Fin k) (z : α) : Bool :=
  decide (∃ i, A i j z = true)
def diffSig (A B : Fin k → Sig α) (z : α) : Bool :=
  decide (∃ i j, i ≠ j ∧ A i z = true ∧ B j z = true)
def pairSig (A B : Grid k α) (z : α) : Bool :=
  decide (∃ i j r c, A i j z = true ∧ B r c z = true ∧ (i ≠ r ∨ j ≠ c))

theorem bundles (s : Net input N) (hk : 2 ≤ k) (A : Grid k α)
    (ha : ∀ i j, Has s (A i j)) :
    ∃ t, Ext s t (k*(k-1)+k*(k-1)) ∧
      (∀ i, Has t (rowAny A i)) ∧ ∀ j, Has t (colAny A j) := by
  haveI : NeZero k := ⟨by omega⟩
  obtain ⟨u,hu,hr⟩ := many s (rowAny A) (k-1) (by
    intro i u keep
    obtain ⟨v,hv,w,hw,he⟩ := any_family u (A i) (fun j => keep (ha i j))
    refine ⟨v,by simpa using hv,w,hw,?_⟩
    intro z
    rw [he]
    apply Bool.eq_iff_iff.mpr
    simp [rowAny])
  obtain ⟨t,ht,hc⟩ := many u (colAny A) (k-1) (by
    intro j v keep
    obtain ⟨v,hv,w,hw,he⟩ := any_family v (fun i => A i j) (fun i => keep (hu.keep (ha i j)))
    refine ⟨v,by simpa using hv,w,hw,?_⟩
    intro z
    rw [he]
    apply Bool.eq_iff_iff.mpr
    simp [colAny])
  exact ⟨t, by simpa using hu.trans ht, fun i => ht.keep (hr i), hc⟩

theorem pairBool (A B : Grid k α) (z : α) :
    (diffSig (rowAny A) (rowAny B) z || diffSig (colAny A) (colAny B) z) =
    pairSig A B z := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, diffSig, rowAny, colAny, pairSig, decide_eq_true_eq]
  constructor
  · rintro (⟨i,r,hir,⟨j,hj⟩,⟨c,hc⟩⟩ | ⟨j,c,hjc,⟨i,hi⟩,⟨r,hr⟩⟩)
    · exact ⟨i,j,r,c,hj,hc,Or.inl hir⟩
    · exact ⟨i,j,r,c,hi,hr,Or.inr hjc⟩
  · rintro ⟨i,j,r,c,ha,hb,h | h⟩
    · exact Or.inl ⟨i,r,h,⟨j,ha⟩,⟨c,hb⟩⟩
    · exact Or.inr ⟨j,c,h,⟨i,ha⟩,⟨r,hb⟩⟩

theorem grid_component
    (strict : ∀ (s : Net input N) (A B : Fin k → Sig α),
      (∀ i, Has s (A i)) → (∀ i, Has s (B i)) →
      ∃ t, Ext s t (5*k-7) ∧ Has t (diffSig A B))
    (s : Net input N) (hk : 2 ≤ k) (A B : Grid k α)
    (mkA : ∀ i j (u : Net input N), Keeps s u → ∃ t, Ext u t 1 ∧ Has t (A i j))
    (mkB : ∀ i j (u : Net input N), Keeps s u → ∃ t, Ext u t 1 ∧ Has t (B i j)) :
    ∃ t, Ext s t (6*k*k+6*k-13) ∧ Has t (pairSig A B) := by
  obtain ⟨t1,h1,a1⟩ := many s (fun q : Fin k × Fin k => A q.1 q.2) 1
    (fun q u keep => mkA q.1 q.2 u keep)
  obtain ⟨t2,h2,b2⟩ := many t1 (fun q : Fin k × Fin k => B q.1 q.2) 1
    (fun q u keep => mkB q.1 q.2 u (fun h => keep (h1.keep h)))
  obtain ⟨t3,h3,ar,ac⟩ := bundles t2 hk A (fun i j => h2.keep (a1 (i,j)))
  obtain ⟨t4,h4,br,bc⟩ := bundles t3 hk B (fun i j => h3.keep (b2 (i,j)))
  obtain ⟨t5,h5,dr⟩ := strict t4 (rowAny A) (rowAny B) (fun i => h4.keep (ar i)) br
  obtain ⟨t6,h6,dc⟩ := strict t5 (colAny A) (colAny B)
    (fun i => h5.keep (h4.keep (ac i))) (fun i => h5.keep (bc i))
  obtain ⟨t7,h7,hh⟩ := gate_or t6 (h6.keep dr) dc
  refine ⟨t7, ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).mono ?_, ?_⟩
  · have hk2 : k ≤ k*k := Nat.le_mul_of_pos_right k (by omega)
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.mul_one,Nat.mul_sub]
    simp only [Nat.mul_assoc]
    omega
  · simpa only [pairBool] using hh

end PEqualNP.Outside.L_meta_19221_aux

namespace PEqualNP.Outside.L_meta_19221_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev blockN (k p : ℕ) := 2*p*(k*k)
abbrev Tests (k p : ℕ) := Fin (blockN k p) × Fin (blockN k p)
def wireIn (k p : ℕ) (z : Tests k p) : List Bool := oneEach z.1 z.2
def leftWire (k p d : ℕ) (z : Tests k p) : Bool := decide (z.1.val = d)
def rightWire (k p d : ℕ) (z : Tests k p) : Bool := decide (z.2.val = d)
def X {k p : ℕ} (b : Fin p) (i j : Fin k) (z : Tests k p) : Bool :=
  leftWire k p (addr k b i j) z || rightWire k p (addr k b i j + k*k) z
def Y {k p : ℕ} (b : Fin p) (i j : Fin k) (z : Tests k p) : Bool :=
  rightWire k p (addr k b i j) z || leftWire k p (addr k b i j + k*k) z

theorem finish (k p : ℕ) (hk : 2 ≤ k) (hp : 1 ≤ p)
    (strict : ∀ (s : Net (wireIn k p) (2*blockN k p)) (A B : Fin k → Sig (Tests k p)),
      (∀ i, Has s (A i)) → (∀ i, Has s (B i)) →
      ∃ t, Ext s t (5*k-7) ∧ Has t (diffSig A B)) :
    RepSizeAtMost (fun u v : Fin (2*p*(k*k)) => decide
      (u.val/(k*k) = v.val/(k*k) ∧ u.val % (k*k) ≠ v.val % (k*k)))
      (p*(6*k*k+6*k-13)+p-1) := by
  let base : Net (wireIn k p) (2*blockN k p) :=
    ⟨[], (by intro g hg; cases hg), fun z => oneEach_len _ z.1 z.2⟩
  have left_raw (d : ℕ) (hd : d < blockN k p) : Has base (leftWire k p d) := by
    refine ⟨d, by change d < 2 * blockN k p + 0; omega, ?_⟩
    intro z
    change (oneEach z.1 z.2).getD d false = decide (z.1.val = d)
    simpa only [eq_comm] using oneEach_getD_left _ z.1 z.2 d hd
  have right_raw (d : ℕ) (hd : d < blockN k p) : Has base (rightWire k p d) := by
    refine ⟨blockN k p + d, by change blockN k p + d < 2*blockN k p + 0; omega, ?_⟩
    intro z
    change (oneEach z.1 z.2).getD (blockN k p+d) false = decide (z.2.val = d)
    simpa only [Nat.add_sub_cancel_left, eq_comm] using
      oneEach_getD_right _ z.1 z.2 (blockN k p+d) (by omega) (by omega)
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨u,bu,all⟩ := many base (fun b : Fin p => pairSig (X b) (Y b))
    (6*k*k+6*k-13) (by
      intro b s keep
      apply grid_component strict s hk
      · intro i j w kw
        obtain ⟨hl,hh⟩ := addr_bounds hk b i j
        exact gate_or w (kw (keep (left_raw _ hl))) (kw (keep (right_raw _ hh)))
      · intro i j w kw
        obtain ⟨hl,hh⟩ := addr_bounds hk b i j
        exact gate_or w (kw (keep (right_raw _ hl))) (kw (keep (left_raw _ hh))))
  obtain ⟨t,last,tf⟩ := any_family u _ all
  rcases tf with ⟨w,hw,heval⟩
  refine ⟨⟨t.gates,w⟩,t.mono, ?_, ?_⟩
  · change t.gates.length ≤ _
    have hc := (bu.trans last).count
    simp only [base,List.length_nil,Nat.zero_add,Fintype.card_fin] at hc
    omega
  · intro row col
    change (t.gates.foldl stepWire (wireIn k p (row,col))).getD w false = _
    rw [heval]
    apply Bool.eq_iff_iff.mpr
    simpa only [pairSig,X,Y,leftWire,rightWire,decide_eq_true_eq,Bool.or_eq_true]
      using index_iff hk row col

end PEqualNP.Outside.L_meta_19221_aux

theorem PEqualNP.Outside.L_meta_19221 : ∀ k p : ℕ, 2 ≤ k → 1 ≤ p → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (2 * p * (k * k)) => decide (u.val / (k * k) = v.val / (k * k) ∧ u.val % (k * k) ≠ v.val % (k * k))) (p * (6 * k * k + 6 * k - 13) + p - 1) := by
  intro k p hk hp
  apply PEqualNP.Outside.L_meta_19221_aux.finish k p hk hp
  intro s A B hA hB
  exact PEqualNP.Outside.L_meta_19221_aux.strict_crown s hk A B hA hB
