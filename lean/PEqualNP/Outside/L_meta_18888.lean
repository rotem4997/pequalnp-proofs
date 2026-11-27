import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18888.CoverCost

open PEqualNP.BicliqueBlockCost

noncomputable def small {n : ℕ} (p : Block n) : Finset (Fin n) :=
  if p.1.card ≤ 1 then p.1 else p.2

noncomputable def pairs {n : ℕ} (p : Block n) : Finset (Sym2 (Fin n)) :=
  (p.1 ×ˢ p.2).image (fun ab => s(ab.1, ab.2))

lemma small_card {n : ℕ} (p : Block n) (h : p.1.card ≤ 1 ∨ p.2.card ≤ 1) :
    (small p).card ≤ 1 := by
  unfold small
  split_ifs with h1
  · exact h1
  · rcases h with h | h
    · exact absurd h h1
    · exact h

lemma pairs_card {n : ℕ} (G : SimpleGraph (Fin n)) (p : Block n) (hb : IsBlock G p)
    (h : p.1.card ≤ 1 ∨ p.2.card ≤ 1) : (pairs p).card ≤ blockCost p := by
  obtain ⟨_, h1, h2, _⟩ := hb
  have a1 : 1 ≤ p.1.card := Finset.card_pos.mpr h1
  have a2 : 1 ≤ p.2.card := Finset.card_pos.mpr h2
  have hc : (pairs p).card ≤ p.1.card * p.2.card := by
    unfold pairs
    exact Finset.card_image_le.trans (le_of_eq (Finset.card_product _ _))
  unfold blockCost
  rcases h with h | h
  · have e : p.1.card = 1 := le_antisymm h a1
    rw [e] at hc ⊢
    omega
  · have e : p.2.card = 1 := le_antisymm h a2
    rw [e] at hc ⊢
    omega

lemma main {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Block n))
    (hF : IsBlockCover G F) (hs : ∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1) :
    ∃ X : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G X ∧
      G.edgeSet.ncard + X.card ≤ familyCost F + 1 := by
  classical
  obtain ⟨hblk, hcov⟩ := hF
  refine ⟨F.biUnion small, ?_, ?_⟩
  · intro u v huv
    obtain ⟨p, hp, hc⟩ := hcov u v huv
    have key : ∀ a b : Fin n, a ∈ p.1 → b ∈ p.2 → a ∈ small p ∨ b ∈ small p := by
      intro a b ha hb
      unfold small
      split_ifs
      · exact Or.inl ha
      · exact Or.inr hb
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases key u v h1 h2 with h | h
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
    · rcases key v u h1 h2 with h | h
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
  · have hsub : G.edgeSet ⊆ ((F.biUnion pairs : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) := by
      intro e
      refine Sym2.ind (fun u v => ?_) e
      intro he
      have huv : G.Adj u v := he
      obtain ⟨p, hp, hc⟩ := hcov u v huv
      refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩)
      unfold pairs
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨h1, h2⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_product.mpr ⟨h1, h2⟩, Sym2.eq_swap⟩
    have hE : G.edgeSet.ncard ≤ ∑ p ∈ F, blockCost p := by
      calc G.edgeSet.ncard
          ≤ ((F.biUnion pairs : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = (F.biUnion pairs).card := Set.ncard_coe_finset _
        _ ≤ ∑ p ∈ F, (pairs p).card := Finset.card_biUnion_le
        _ ≤ ∑ p ∈ F, blockCost p :=
            Finset.sum_le_sum (fun p hp => pairs_card G p (hblk p hp) (hs p hp))
    have hX : (F.biUnion small).card ≤ F.card := by
      calc (F.biUnion small).card ≤ ∑ p ∈ F, (small p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ F, 1 := Finset.sum_le_sum (fun p hp => small_card p (hs p hp))
        _ = F.card := by simp
    unfold familyCost
    omega

end PEqualNP.Outside.L_meta_18888.CoverCost

namespace PEqualNP.Outside.L_meta_18888
theorem CoverCost : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (PEqualNP.BicliqueBlockCost.Block x1)), PEqualNP.BicliqueBlockCost.IsBlockCover x2 x3 → (∀ x5 ∈ x3, x5.1.card ≤ (1 : ℕ) ∨ x5.2.card ≤ (1 : ℕ)) → ∃ (x6 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x6 ∧ x2.edgeSet.ncard + x6.card ≤ PEqualNP.BicliqueBlockCost.familyCost x3 + (1 : ℕ) := by
  intro n G F hF hs
  exact PEqualNP.Outside.L_meta_18888.CoverCost.main G F hF hs

end PEqualNP.Outside.L_meta_18888

namespace PEqualNP.Outside.L_meta_18888.CleanGates

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

def gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

def firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 0 (w-1))

def secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w-1)))

def andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  match (gateAtPos n gs w).op with
  | GateOp.and => true
  | _ => false

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
  unfold clampWire
  split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
    (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]
  split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i+1) x = x ⟨i,hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

lemma edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ¬ edgeTrue G (singletonBits u) := by
  rintro ⟨i,j,h,hi,hj⟩
  simp only [singletonBits, decide_eq_true_eq] at hi hj
  subst i
  subst j
  exact G.loopless.irrefl u h

lemma edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    edgeTrue G (pairBits u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    simp only [pairBits, decide_eq_true_eq] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (G.loopless.irrefl _ h).elim
    · exact h
    · exact h.symm
    · exact (G.loopless.irrefl _ h).elim
  · intro h
    exact ⟨u,v,h,by simp [pairBits],by simp [pairBits]⟩

lemma binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
    (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
    op.eval (l.map v) =
      (if (match op with | GateOp.and => true | _ => false) then
        v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
       else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact (nonempty rfl rfl).elim
    · simp [GateOp.eval,vd]
  | cons i t =>
    cases t with
    | nil => rcases hop with rfl | rfl <;> simp [GateOp.eval]
    | cons j t =>
      have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst t
      rcases hop with rfl | rfl <;> simp [GateOp.eval]

def supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => posRead gs w (singletonBits u) = true

lemma mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (u : Fin n) :
    u ∈ supports gs w ↔ posRead gs w (singletonBits u) = true := by simp [supports]

def cleanOn {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ (j : Fin gs.length) (x : Fin n → Bool),
    (x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) →
    (gs.get j).op = GateOp.and →
    (wiresFrom gs (List.ofFn x)).getD (n + j.val) false = true → edgeTrue G x

def binaryOps (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n+j+1) = gs[j] := by
  unfold gateAtPos
  rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs)
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
    intro ha hempty
    let z : Fin n → Bool := fun _ => false
    have eqg := getD_wiresFrom_gate gs (List.ofFn z) j hj
    simp only [List.length_ofFn, hempty, List.map_nil, ha, GateOp.eval, List.all_nil] at eqg
    obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z (Or.inl rfl) ha eqg
    contradiction
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

lemma pos_clean {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) (x : Fin n → Bool)
    (hx : x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) :
    posRead gs w x = true → edgeTrue G x := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  rw [hw] at ha ⊢
  simp only [andPos, gateAt_index gs j hj] at ha
  have hop : gs[j].op = GateOp.and := by
    cases h : gs[j].op <;> simp_all
  exact clean ⟨j,hj⟩ x hx hop

lemma support_base {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n+1) :
    (supports (n:=n) gs w).card ≤ 1 := by
  cases w with
  | zero => simp [supports,posRead]
  | succ i =>
    have hi : i < n := by omega
    have hs : supports gs (i+1) = {⟨i,hi⟩} := by
      ext u
      simp [mem_support,pos_input gs i hi,singletonBits,eq_comm]
    simp [hs]

lemma hit_base {n : ℕ} (gs : List Gate) (w : ℕ) (u v : Fin n) (hw : w < n+1) :
    posRead gs w (pairBits u v) = true → u ∈ supports gs w ∨ v ∈ supports gs w := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    have hi : i<n := by omega
    simp [mem_support,pos_input gs i hi,pairBits,singletonBits]

lemma support_and {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) : supports (n:=n) gs w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact edge_single G u (pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inl ⟨u, rfl⟩)) ((mem_support gs w u).mp hu))

lemma support_or {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
    supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
  ext u
  simp only [Finset.mem_union,mem_support,pos_gate G gs ops clean w lo hi,ha]
  simp

lemma cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
    (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
    (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
  apply (edge_pair G u v).mp
  apply pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inr ⟨u, v, rfl⟩))
  rw [pos_gate G gs ops clean w lo hi,ha]
  simp only [ite_true, Bool.and_eq_true]
  have hm := pos_mono (n:=n) gs (fun g h => (ops g h).1)
  constructor
  · apply hm (firstWire n gs w) (singletonBits u) (pairBits u v) _ ((mem_support _ _ _).mp hu)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]
  · apply hm (secondWire n gs w) (singletonBits v) (pairBits u v) _ ((mem_support _ _ _).mp hv)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]

lemma root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [pos_clamp]
  change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
  split_ifs with h
  · rfl
  · symm
    apply List.getD_eq_default
    simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

lemma root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
  unfold clampWire
  split <;> omega

lemma root_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    supports (n:=n) gs (clampWire (n+gs.length) out) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u h
  apply edge_single G u
  apply (heval _).mp
  rw [← root_read]
  exact (mem_support _ _ _).mp h

lemma root_hits {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    ∀ u v, G.Adj u v → posRead gs (clampWire (n+gs.length) out) (pairBits u v) = true := by
  intro u v h
  rw [root_read,heval]
  exact (edge_pair G u v).mpr h

theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

theorem gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2
      simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2
      exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

theorem cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
      (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
      (R.biUnion f).card ≤ R.card + B.card) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]
            tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]
            tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨
        (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
      simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using hdag f {r} B hstep

theorem edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

theorem edge_finset_gate_bound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
        have hw : w ∈ AS := by simp [AS,hN,hk,hA]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]

theorem total_from_model (n k N r L : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hr : r < N) (hrS : S r = ∅) (hrH : ∀ u v, G.Adj u v → H r u v)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hpartition :
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card ≤ L) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ L + 1 := by
  classical
  have hd (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) : Disjoint (S (a w)) (S (b w)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact G.loopless.irrefl t (hjoin w hk hN hA t ht t ht')
  have hside (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
    by_contra! hf
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hf.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hf.2
    have hJ := hjoin w hk hN hA
    exact hc4 u x v y huv hxy ⟨hJ u hu x hx, (hJ v hv x hx).symm, hJ v hv y hy, (hJ u hu y hy).symm⟩
  have births (u v) (huv : G.Adj u v) := edge_birth n k N r S H a b A u v hr
    (hrH u v huv) (by simp [hrS]) (by simp [hrS]) hinput ha hb horS horH handH hd
  have edgeCount := edge_finset_gate_bound n k N G S a b A hc4 hsmall
    (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) hzero horS hjoin hside births
  obtain ⟨T,hT,hcard⟩ := cover_half n k N r G S H a b A hr hrS hrH hinput ha hb
    horS horH hside handH (fun f R B step => dag_union_bound f R B step)
  exact ⟨T,hT,by omega⟩

theorem pairCleanBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (x = (fun _ => false) ∨ (∃ u : Fin n, x = fun z => decide (z = u)) ∨ (∃ u v : Fin n, x = fun z => decide (z = u ∨ z = v))) → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G inst hc4 gs out ops eval clean
  have he : ∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x := by
    intro x
    rw [eval]
    exact decide_eq_true_iff
  apply total_from_model n (n+1) (n+1+gs.length) (clampWire (n+gs.length) out) gs.length G
    (supports gs) (fun w u v => posRead gs w (pairBits u v) = true)
    (firstWire n gs) (secondWire n gs) (andPos n gs) hc4 (root_bound n gs.length out)
    (root_support_empty G gs out he) (root_hits G gs out he) (support_base gs) (hit_base gs)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · exact support_or G gs ops clean
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,Bool.false_eq_true,ite_false,Bool.or_eq_true]
      using h
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,ite_true,Bool.and_eq_true] using h
  · exact support_and G gs clean
  · exact cross_support G gs ops clean
  · exact gate_partition_count n gs.length (andPos n gs) (supports gs)

open PEqualNP.BicliqueBlockCost

theorem starBridge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hc : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) (e : ∃ u v, G.Adj u v) :
    HasBlockCost G (G.edgeFinset.card + T.card - 1) := by
  classical
  let leaves (u : Fin n) := Finset.univ.filter (fun v => G.Adj u v ∧ (v ∉ T ∨ u < v))
  have leaf (u v) : v ∈ leaves u ↔ G.Adj u v ∧ (v ∉ T ∨ u < v) := by simp [leaves]
  let centres := T.filter (fun u => (leaves u).Nonempty)
  let star (u : Fin n) : Block n := ({u}, leaves u)
  have inj : Function.Injective star := by
    intro u v h
    have eq : ({u} : Finset (Fin n)) = {v} := congrArg Prod.fst h
    simpa using eq
  have covers (u v : Fin n) (h : G.Adj u v) :
      (u ∈ T ∧ v ∈ leaves u) ∨ (v ∈ T ∧ u ∈ leaves v) := by
    by_cases hu : u ∈ T
    · by_cases hv : v ∈ T
      · rcases lt_or_gt_of_ne h.ne with hlt | hgt
        · exact Or.inl ⟨hu, (leaf _ _).2 ⟨h, Or.inr hlt⟩⟩
        · exact Or.inr ⟨hv, (leaf _ _).2 ⟨h.symm, Or.inr hgt⟩⟩
      · exact Or.inl ⟨hu, (leaf _ _).2 ⟨h, Or.inl hv⟩⟩
    · exact Or.inr ⟨(hc u v h).resolve_left hu, (leaf _ _).2 ⟨h.symm, Or.inl hu⟩⟩
  have centre {u v} (hu : u ∈ T) (hv : v ∈ leaves u) : u ∈ centres :=
    Finset.mem_filter.mpr ⟨hu, v, hv⟩
  refine ⟨centres.image star, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨Finset.disjoint_singleton_left.mpr (fun h => G.irrefl ((leaf u u).1 h).1),
      Finset.singleton_nonempty u, (Finset.mem_filter.mp hu).2, ?_⟩
    intro a ha b hb
    have ea : a = u := Finset.mem_singleton.mp ha
    exact ea ▸ ((leaf u b).1 hb).1
  · intro u v h
    rcases covers u v h with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact ⟨star u, Finset.mem_image_of_mem _ (centre hu hv), Or.inl ⟨Finset.mem_singleton_self _, hv⟩⟩
    · exact ⟨star v, Finset.mem_image_of_mem _ (centre hv hu), Or.inr ⟨Finset.mem_singleton_self _, hu⟩⟩
  · have bound : (centres.sigma leaves).card ≤ G.edgeFinset.card := by
      apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
      · intro p hp
        exact SimpleGraph.mem_edgeFinset.mpr ((leaf _ _).1 (Finset.mem_sigma.mp hp).2).1
      · rintro ⟨u,v⟩ h₁ ⟨w,z⟩ h₂ heq
        obtain ⟨hu, hv⟩ := Finset.mem_sigma.mp h₁
        obtain ⟨hw, hz⟩ := Finset.mem_sigma.mp h₂
        rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · rfl
        · have lt₁ := ((leaf _ _).1 hv).2.resolve_left (not_not_intro (Finset.mem_filter.mp hw).1)
          have lt₂ := ((leaf _ _).1 hz).2.resolve_left (not_not_intro (Finset.mem_filter.mp hu).1)
          exact False.elim ((not_lt_of_gt lt₁) lt₂)
    rw [Finset.card_sigma] at bound
    have cardLe : centres.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have pos : 0 < T.card := by
      obtain ⟨u, v, h⟩ := e
      rcases hc u v h with hu | hv
      · exact Finset.card_pos.mpr ⟨u, hu⟩
      · exact Finset.card_pos.mpr ⟨v, hv⟩
    unfold familyCost
    rw [Finset.sum_image inj.injOn, Finset.card_image_of_injective _ inj]
    have cost (u) : blockCost (star u) = (leaves u).card := by simp [blockCost, star]
    simp_rw [cost]
    omega

end PEqualNP.Outside.L_meta_18888.CleanGates

namespace PEqualNP.Outside.L_meta_18888.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.BicliqueBlockCost

def incident (p : Fin 12) (l : Fin 13) : Prop :=
  p.succ = l ∨ p.succ = l + 1 ∨ p.succ = l + 3 ∨ p.succ = l + 9

instance (p : Fin 12) (l : Fin 13) : Decidable (incident p l) := by
  unfold incident
  infer_instance

def direction (a b : Fin 25) : Bool :=
  decide (a.val < 12 ∧ 12 ≤ b.val ∧
    (a.val + 14 - (b.val - 12)) % 13 ∈ ({0,1,3,9} : Finset ℕ))

def G : SimpleGraph (Fin 25) where
  Adj i j := direction i j = true ∨ direction j i = true
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel G.Adj := fun i j =>
  inferInstanceAs (Decidable (direction i j = true ∨ direction j i = true))

abbrev P : Fin 12 → Fin 25 := Fin.castAdd 13
abbrev L : Fin 13 → Fin 25 := Fin.natAdd 12

def target (x : Fin 25 → Bool) : Prop :=
  ∃ p l, incident p l ∧ x (P p) = true ∧ x (L l) = true

theorem graphTarget (x : Fin 25 → Bool) : target x ↔ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by
  have inc : ∀ p l, incident p l → G.Adj (P p) (L l) := by decide +kernel
  have decode : ∀ i j, direction i j = true →
      ∃ p l, i = P p ∧ j = L l ∧ incident p l := by decide +kernel
  constructor
  · rintro ⟨p,l,e,hp,hl⟩
    exact ⟨_,_,inc _ _ e,hp,hl⟩
  · rintro ⟨i,j,(e|e),hi,hj⟩
    · obtain ⟨p,l,rfl,rfl,adj⟩ := decode _ _ e
      exact ⟨p,l,adj,hi,hj⟩
    · obtain ⟨p,l,rfl,rfl,adj⟩ := decode _ _ e
      exact ⟨p,l,adj,hj,hi⟩

set_option maxRecDepth 20000 in
theorem edgeCount : G.edgeSet.ncard = 48 := by
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem noFour : PEqualNP.TopForm.NoFourCycle G := by
  unfold PEqualNP.TopForm.NoFourCycle
  decide +kernel

theorem coverLower (S : Finset (Fin 25)) (covers : CoverPromise.IsVertexCover G S) : 12 ≤ S.card := by
  classical
  let pick := fun i : Fin 12 => if P i ∈ S then P i else L i.succ
  have edges : ∀ i, G.Adj (P i) (L i.succ) := by decide +kernel
  have pickMem (i) : pick i ∈ S := by
    unfold pick
    split_ifs with h
    · exact h
    · exact (covers _ _ (edges i)).resolve_left h
  have disjoint : ∀ i j : Fin 12, P i ≠ L j.succ := by decide +kernel
  have inj : Function.Injective pick := by
    intro i j eq
    dsimp only [pick] at eq
    split_ifs at eq with hi hj hj
    · exact Fin.ext (congrArg (fun t : Fin 25 => t.val) eq)
    · exact False.elim (disjoint _ _ eq)
    · exact False.elim (disjoint _ _ eq.symm)
    · have facts : ∀ i j : Fin 12, L i.succ = L j.succ → i = j := by decide +kernel
      exact facts i j eq
  have bound := Finset.card_le_card (show Finset.univ.image pick ⊆ S from by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact pickMem j)
  simpa [Finset.card_image_of_injective _ inj] using bound

theorem blockLower {s : ℕ} (cost : HasBlockCost G s) : 59 ≤ s := by
  obtain ⟨F,hF,hcost⟩ := cost
  have stars : ∀ p ∈ F, p.1.card ≤ 1 ∨ p.2.card ≤ 1 := by
    intro p hp
    by_contra! big
    obtain ⟨i,j,hi,hj,ij⟩ := Finset.one_lt_card_iff.mp big.1
    obtain ⟨a,b,ha,hb,ab⟩ := Finset.one_lt_card_iff.mp big.2
    have link := (hF.1 p hp).2.2.2
    have uni := Finset.card_le_one.mp (noFour i j ij)
    exact ab (uni a (by simp [link i hi a ha,link j hj a ha])
      b (by simp [link i hi b hb,link j hj b hb]))
  obtain ⟨S,cov,count⟩ := PEqualNP.Outside.L_meta_18888.CoverCost 25 G F hF stars
  have low := coverLower S cov
  rw [edgeCount] at count
  omega

end PEqualNP.Outside.L_meta_18888.Plane

namespace PEqualNP.Outside.L_meta_18888.Plane

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pair (a b : Fin 25) (i : Fin 25) : Bool := decide (i = a ∨ i = b)

theorem internalNonedge (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 25 → Bool, C.eval (List.ofFn x) = true ↔ target x) (small : C.size < 59) :
    ∃ (j : Fin C.gates.length) (a b : Fin 25), a ≠ b ∧ ¬G.Adj a b ∧
      (C.gates.get j).op = .and ∧ 25+j.val ≠ C.output ∧
      (C.wires (List.ofFn (pair a b))).getD (25+j.val) false = true := by
  classical
  have ops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => by simpa using (mono g h).1
  have up (w : ℕ) (x y : Fin 25 → Bool) (le : ∀ i, x i = true → y i = true) :
      (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true :=
    PEqualNP.Outside.L_meta_18888.CleanGates.pos_mono C.gates ops (w+1) x y le
  have other : ∀ a : Fin 25, ∃ b, a ≠ b ∧ ¬G.Adj a b := by decide +kernel
  have pairHit (a b) : target (pair a b) ↔ G.Adj a b := by
    rw [graphTarget]
    constructor
    · rintro ⟨i,j,e,hi,hj⟩
      simp only [pair,decide_eq_true_eq] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with eq | eq <;> subst eq <;>
        first | exact e | exact e.symm | exact False.elim (e.ne rfl)
    · exact fun e => ⟨a,b,e,by simp [pair],by simp [pair]⟩
  by_contra! none
  have cannot (j : Fin C.gates.length) (a b : Fin 25) (ab : a ≠ b) (na : ¬ G.Adj a b)
      (op : (C.gates.get j).op = .and) :
      (C.wires (List.ofFn (pair a b))).getD (25+j.val) false ≠ true := by
    intro on
    have diff : 25+j.val ≠ C.output := by
      intro eq
      rw [eq] at on
      exact na ((pairHit a b).mp ((correct _).mp on))
    exact none j a b ab na op diff on
  have rect : ∀ a b c d : Fin 25, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d ac bd ⟨ab,bc,cd,da⟩
    exact bd (Finset.card_le_one.mp (noFour a c ac) b (by simp [ab,bc.symm]) d (by simp [da.symm,cd]))
  obtain ⟨S,cov,count⟩ := PEqualNP.Outside.L_meta_18888.CleanGates.pairCleanBound 25 G rect C.gates C.output
    (fun g h => ⟨ops g h,(mono g h).2⟩)
    (fun x => Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using (correct x).trans (graphTarget x)))
    (by
      intro j x input op on
      change (C.wires _).getD (25+j.val) false = true at on
      have single (a : Fin 25) (le : ∀ i, x i = true → i = a) : False := by
        obtain ⟨b,ab,na⟩ := other a
        exact cannot j a b ab na op (up _ _ _ (fun i hi => by simp [pair,le i hi]) on)
      rcases input with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
      · exact (single 0 (by simp)).elim
      · exact (single a (by simp)).elim
      · by_cases eq : a = b
        · subst b
          exact (single a (by simp)).elim
        by_cases e : G.Adj a b
        · exact (graphTarget _).mp ((pairHit a b).mpr e)
        · exact (cannot j a b eq e op on).elim)
  have twelve := coverLower S cov
  have ec : G.edgeFinset.card = 48 := by
    rw [← Set.ncard_coe_finset, G.coe_edgeFinset]
    exact edgeCount
  rw [ec] at count
  change C.gates.length < 59 at small
  omega

end PEqualNP.Outside.L_meta_18888.Plane

namespace PEqualNP.Outside.L_meta_18888.Plane.Orbit

private def generators : List (List (Fin 25)) := [
  [0, 7, 2, 4, 6, 10, 3, 11, 8, 5, 9, 1, 12, 17, 19, 14, 16, 23, 20, 15, 21, 18, 22, 13, 24],
  [0, 1, 8, 3, 6, 10, 4, 11, 2, 9, 5, 7, 12, 13, 18, 20, 16, 23, 14, 21, 15, 19, 22, 17, 24],
  [2, 11, 0, 3, 6, 9, 4, 7, 8, 5, 10, 1, 12, 15, 23, 13, 16, 19, 21, 17, 20, 18, 22, 14, 24],
  [0, 9, 2, 3, 6, 11, 4, 10, 8, 1, 7, 5, 12, 13, 19, 15, 16, 23, 21, 14, 20, 18, 24, 17, 22],
  [0, 7, 2, 5, 9, 3, 10, 1, 8, 4, 6, 11, 12, 17, 19, 15, 22, 13, 20, 14, 18, 21, 16, 23, 24],
  [3, 1, 4, 0, 2, 5, 8, 11, 6, 9, 10, 7, 16, 13, 14, 17, 12, 15, 18, 21, 23, 19, 22, 20, 24]]
private def gen (g : Fin 6) (z : Fin 25) := (generators.getD g.val []).getD z.val z

private def routes : List (List (List (Fin 6))) := [
  [[], [], [], [4, 3, 0], [4, 3], [3, 0], [4, 0, 3], [4], [1], [3], [0, 3], [0], [], [], [], [0], [], [], [1], [3], [1, 0], [0, 1], [4], [], [3, 4]],
  [[], [], [2, 0], [5], [5, 2, 0], [4, 5, 0], [0, 5, 0], [3, 0, 4, 5], [1, 2, 0], [4, 5, 2], [1, 4, 5, 0], [3, 4, 5], [3, 4, 5, 2], [], [], [3, 2, 4, 5, 0], [3, 4, 5, 4, 2], [3, 0, 4, 5, 0], [], [3, 0, 4, 5], [3, 2, 4, 5, 1], [3, 4, 5, 2], [4, 5, 3, 4, 5], [3, 2, 4, 5], []],
  [[], [], [], [4, 3, 2], [4, 3, 2, 0], [3, 2], [2, 4, 3], [0, 2], [2, 1], [3, 2, 0], [3, 0, 2], [2], [], [2, 0], [], [], [2], [0, 2], [2, 0, 1], [], [2, 1, 0], [2, 1], [4, 2], [2], [3, 4, 2]],
  [[], [], [], [], [5], [5, 3, 0], [5, 1], [5, 0], [1, 4, 3, 2], [5, 3], [3, 5, 0], [5, 4], [5], [], [5], [], [], [5, 0], [5, 1], [3, 5], [], [5, 3], [5, 4], [2, 5], [5, 3, 4]],
  [[], [], [], [], [], [5, 3, 2], [5, 2, 1], [5, 2], [1, 2, 4, 3], [5, 3, 2, 0], [5, 3, 0, 2], [5, 0, 2], [5, 2], [5, 2, 0], [], [5, 0, 2], [], [], [5, 2, 0, 1], [5, 2, 1], [5, 2], [], [5, 4, 2], [5, 2, 1, 0], [5, 3, 4, 2]],
  [[], [], [], [], [], [], [0, 3, 5, 0], [4, 5], [3, 1, 0, 2], [4, 5], [4, 5, 1], [4, 5, 4], [4, 5], [4, 5, 0], [4, 3, 5], [], [4, 5, 4], [], [], [4, 5], [4, 5, 1], [4, 5, 3], [], [4, 2, 5], [4, 5, 3, 4]],
  [[], [], [], [], [], [], [], [2, 5, 2], [4, 3, 1, 2], [3, 5, 2, 0], [3, 5, 2], [0, 5], [0, 5], [0, 5, 0], [0, 3, 5], [0, 5], [], [0, 2, 5], [], [], [2, 5, 2], [0, 5, 1], [0, 5, 4], [], [3, 5, 4, 2]],
  [[], [], [], [], [], [], [], [], [1, 2], [2, 4, 5], [4, 0, 5, 0], [3, 4, 5, 1], [3, 4, 0, 5], [3, 1, 4, 5, 0], [5, 3, 4, 5], [3, 4, 0, 5], [5, 3, 4, 5], [], [3, 1, 4, 5], [], [], [3, 4, 2, 5, 2], [3, 4, 3, 5, 4, 2], [3, 4, 0, 5, 0], []],
  [[], [], [], [], [], [], [], [], [], [3, 1, 2, 0], [3, 1, 2], [1, 0, 2], [], [1, 2, 0], [1, 2, 0, 1], [1, 2, 1, 0], [1, 2], [1, 2], [], [1, 2, 1], [], [], [4, 1, 2], [1, 0, 2], [3, 4, 1, 2]],
  [[], [], [], [], [], [], [], [], [], [], [0, 4, 5], [0, 4, 5, 0], [4, 5, 2], [], [0, 4, 5], [2, 4, 5, 0], [4, 5, 4, 2], [2, 4, 5], [4, 5, 2], [], [2, 4, 5, 1], [], [], [0, 4, 5, 0], [4, 5, 3, 4, 2]],
  [[], [], [], [], [], [], [], [], [], [], [], [4, 0, 5], [4, 0, 5], [1, 4, 5, 0], [], [4, 0, 5], [4, 0, 5, 4], [4, 0, 5, 0], [4, 2, 5, 2], [1, 4, 5, 3], [], [1, 4, 5], [], [], [4, 3, 5, 4, 2]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [3, 4, 5], [3, 4, 5, 0], [3, 4, 5], [], [3, 4, 5, 4], [3, 4, 2, 5], [3, 4, 5, 3], [3, 4, 3, 5], [3, 4, 5, 1], [], [3, 4, 5, 3, 4], [], []],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [2, 0], [2], [], [4], [1, 2, 0], [0, 2], [1, 2], [1, 0, 2], [4], [0], [3, 4]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [4, 3, 0], [5], [5, 4, 3, 0], [1], [3], [1, 4, 3, 0], [3, 1], [4, 5, 2], [2, 5, 4, 3], [3, 4, 5, 2]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5, 4, 3], [5, 2, 0], [4, 3], [2, 0, 1], [0, 5, 4, 3, 1], [5, 0, 3], [2, 1, 4, 3], [1, 4, 5, 0], [0, 3], [3, 2, 4, 5]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5, 4], [3, 0], [3, 2, 1], [5, 4, 3, 1], [4, 3, 2, 1], [2, 1], [4, 5, 4], [0], [3, 4, 5, 4]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5, 2], [0, 5, 0], [2, 5, 2], [5, 0], [5, 0, 2], [5, 4], [0, 5], [5, 3, 4]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [3, 0, 1], [4], [1, 0], [4, 3, 1], [4, 5], [5, 4, 3, 2, 1], [3, 4, 0, 5]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [2, 4, 3, 1], [5, 1, 4, 3], [5, 2, 4, 3, 1], [4, 5, 0], [1, 4, 3], [3, 0, 4, 5, 0]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [2, 1, 0], [3, 2, 0, 1], [2, 4, 5], [4, 0, 3], [3, 1, 4, 5, 0]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5, 4, 0, 3], [4, 0, 5, 0], [3, 1, 0], [5, 3, 4, 5]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 4, 5, 0], [0, 1], [3, 4, 5, 0]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [4, 0, 5], [4, 5, 3, 4]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [3, 4, 5]],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]]
private def path (a b : Fin 25) := (routes.getD a.val []).getD b.val []
private def walk (w : List (Fin 6)) (z : Fin 25) := w.foldl (fun i g => gen g i) z

def representatives : List (Fin 25 × Fin 25) := [(0,1), (0,2), (0,14), (0,16), (12,13), (12,16), (13,14)]
def canonical (a b : Fin 25) : Prop := (min a b, max a b) ∈ representatives

private theorem genInj : ∀ g, Function.Injective (gen g) := by
  unfold Function.Injective
  decide +kernel

private theorem genAdj : ∀ g a b, G.Adj (gen g a) (gen g b) ↔ G.Adj a b := by
  decide +kernel

private theorem valid (w : List (Fin 6)) : Function.Injective (walk w) ∧
    ∀ a b, G.Adj (walk w a) (walk w b) ↔ G.Adj a b := by
  induction w with
  | nil => exact ⟨Function.injective_id, fun _ _ => Iff.rfl⟩
  | cons g w ih =>
    exact ⟨ih.1.comp (genInj g), fun a b => (ih.2 _ _).trans (genAdj g a b)⟩

private theorem hit : ∀ a b, a < b → ¬G.Adj a b →
    canonical (walk (path a b) a) (walk (path a b) b) := by
  unfold canonical
  decide +kernel

theorem normalize (a b : Fin 25) (ab : a ≠ b) (nonedge : ¬G.Adj a b) :
    ∃ σ : Equiv.Perm (Fin 25), (∀ i j, G.Adj (σ i) (σ j) ↔ G.Adj i j) ∧ canonical (σ a) (σ b) := by
  have ordered (i j : Fin 25) (lt : i < j) (h : ¬G.Adj i j) :
      ∃ σ : Equiv.Perm (Fin 25), (∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v) ∧ canonical (σ i) (σ j) := by
    let w := path i j
    have good := valid w
    exact ⟨Equiv.ofBijective (walk w) ((Finite.injective_iff_bijective).mp good.1),good.2,hit i j lt h⟩
  rcases lt_or_gt_of_ne ab with lt | gt
  · exact ordered a b lt nonedge
  · obtain ⟨σ,g,h⟩ := ordered b a gt fun e => nonedge e.symm
    exact ⟨σ,g,by simpa only [canonical,min_comm (σ a) (σ b), max_comm (σ a) (σ b)] using h⟩

end PEqualNP.Outside.L_meta_18888.Plane.Orbit

namespace PEqualNP.Outside.L_meta_18888.Plane.Orbit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem relabel (n : ℕ) (C : Circuit) (f : Equiv.Perm (Fin n)) (mono : Monotone2 C) :
    ∃ D : Circuit, D.size = C.size ∧ Monotone2 D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ f))) ∧
      ∀ j : Fin C.gates.length, ∃ k : Fin D.gates.length,
        (D.gates.get k).op = (C.gates.get j).op ∧
        (n+k.val = D.output ↔ n+j.val = C.output) ∧
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n+k.val) false =
          (C.wires (List.ofFn (x ∘ f))).getD (n+j.val) false := by
  let wire (f : Fin n → Fin n) (i : ℕ) := if h : i < n then (f ⟨i, h⟩).val else i
  let renameGate (f : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op, g.inputs.map (wire f)⟩
  let D (f : Fin n → Fin n) : Circuit := ⟨C.gates.map (renameGate f), wire f C.output⟩
  have dSize (f : Fin n → Fin n) : (D f).size = C.size := by
    change (C.gates.map (renameGate f)).length = C.gates.length
    exact List.length_map _
  have wireAgree {A : Type} (defaultVal : A) (op : Gate → List A → A)
      (consistent : ∀ g xs ys, (∀ i, xs.getD (wire f i) defaultVal = ys.getD i defaultVal) →
        op (renameGate f g) xs = op g ys)
      (gates : List Gate) (xs ys : List A)
      (hlen : xs.length = ys.length) (hn : n ≤ xs.length)
      (hbits : ∀ i, xs.getD (wire f i) defaultVal = ys.getD i defaultVal) :
      let step := fun (xs : List A) (g : Gate) => xs ++ [op g xs];
      ∀ i, (List.foldl step xs (gates.map (renameGate f))).getD (wire f i) defaultVal =
        (List.foldl step ys gates).getD i defaultVal := by
    let step := fun (xs : List A) (g : Gate) => xs ++ [op g xs]
    change ∀ i, (List.foldl step xs _).getD (wire f i) defaultVal = (List.foldl step ys gates).getD i defaultVal
    induction gates generalizing xs ys with
    | nil => exact hbits
    | cons g gates ih =>
      have hv := consistent g xs ys hbits
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp [step, hlen]
      · simp [step]; omega
      · intro i
        dsimp only [step]
        rw [hv]
        by_cases h : i < n
        · have hw : wire f i < xs.length := by
            have hh : wire f i < n := by simp [wire, h]
            omega
          have hy : i < ys.length := by omega
          rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hy]
          exact hbits i
        · have hw : wire f i = i := by simp [wire, h]
          rw [hw]
          by_cases hi : i < ys.length
          · rw [List.getD_append _ _ _ _ (hlen.symm ▸ hi), List.getD_append _ _ _ _ hi]
            simpa only [hw] using hbits i
          · rw [List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), hlen]

  have agree (x : Fin n → Bool) (i : ℕ) :
      ((D f).wires (List.ofFn x)).getD (wire f i) false = (C.wires (List.ofFn (x ∘ f))).getD i false := by
    let op := fun (g : Gate) (xs : List Bool) => g.op.eval (g.inputs.map fun i => xs.getD i false)
    refine wireAgree false op (fun g xs ys agree => ?_) _ _ _ (by simp) (by simp) ?_ i
    · simp only [op,renameGate,List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => agree i)
    · intro i
      by_cases h : i < n
      · have hs := (f ⟨i,h⟩).isLt
        simp only [wire,dite_eq_left h,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
          dite_eq_left hs,Option.getD_some,Function.comp_apply]
      · simp only [wire,dite_eq_right h,List.getD_eq_getElem?_getD,List.getElem?_ofFn,Option.getD_none]

  refine ⟨D f,dSize _,?_,fun x => agree x C.output,?_⟩
  · intro h mem
    obtain ⟨g,m,rfl⟩ := List.mem_map.mp mem
    simpa [renameGate] using mono g m
  · intro j
    have lt : j.val < (D f).gates.length := by simp [D]
    refine ⟨⟨j.val,lt⟩,by simp [D,renameGate],?_,?_⟩
    · change (n+j.val = wire f C.output ↔ n+j.val = C.output)
      by_cases h : C.output < n
      · have smaller := (f ⟨C.output,h⟩).isLt
        simp only [wire,dite_eq_left h]
        omega
      · simp [wire,h]
    · intro x
      simpa only [wire,show ¬ n+j.val < n by omega,dite_false] using agree x (n+j.val)

theorem canonicalCircuit (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 25 → Bool, C.eval (List.ofFn x) = true ↔ target x) (small : C.size < 59) :
    ∃ D : Circuit, D.size = C.size ∧ Monotone2 D ∧
      (∀ x : Fin 25 → Bool, D.eval (List.ofFn x) = true ↔ target x) ∧
      ∃ (j : Fin D.gates.length) (a b : Fin 25), canonical a b ∧
        (D.gates.get j).op = .and ∧ 25+j.val ≠ D.output ∧
        (D.wires (List.ofFn (pair a b))).getD (25+j.val) false = true := by
  obtain ⟨j,a,b,distinct,nonedge,opj,internal,on⟩ := internalNonedge C mono correct small
  obtain ⟨f,adj,rep⟩ := normalize a b distinct nonedge
  obtain ⟨D,sz,mon,eval,gate⟩ := relabel 25 C f mono
  obtain ⟨k,opk,output,wire⟩ := gate j
  refine ⟨D,sz,mon,?_,k,f a,f b,rep,opk.trans opj,fun h => internal (output.mp h),?_⟩
  · intro x
    rw [eval, correct, graphTarget, graphTarget]
    constructor
    · rintro ⟨i,j,e,hi,hj⟩
      exact ⟨f i,f j,(adj i j).mpr e,hi,hj⟩
    · rintro ⟨i,j,e,hi,hj⟩
      refine ⟨f.symm i,f.symm j,(adj _ _).mp (by simpa using e),?_,?_⟩
      · simpa using hi
      · simpa using hj
  · have same : pair (f a) (f b) ∘ f = pair a b := by
      funext i
      simp [pair]
    rw [wire,same]
    exact on

end PEqualNP.Outside.L_meta_18888.Plane.Orbit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover in
theorem PEqualNP.Outside.L_meta_18888 :
have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (13 : ℕ)), x3.succ ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x3 : Fin x2.gates.length), ∃ x4 ∈ [(1 : ℕ), (2 : ℕ), (14 : ℕ), (16 : ℕ), (313 : ℕ), (316 : ℕ), (339 : ℕ)], (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (25 : ℕ) + ↑x3 ≠ x2.output ∧ (x2.wires (List.ofFn fun (x5 : Fin (25 : ℕ)) => Decidable.decide (↑x5 = x4 / (25 : ℕ) ∨ ↑x5 = x4 % (25 : ℕ)))).getD ((25 : ℕ) + ↑x3) Bool.false = Bool.true; (∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x1 x3 ∧ x3.size < (59 : ℕ)) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x1 x4 ∧ x4.size < (59 : ℕ) ∧ x2 x4 := by
  dsimp only
  rintro ⟨C,mon,correct,small⟩
  have relate (x : Fin 25 → Bool) : PEqualNP.Outside.L_meta_18888.Plane.target x ↔
      ∃ (p : Fin 12) (l : Fin 13), p.succ ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true := by
    have eq : ∀ p l, PEqualNP.Outside.L_meta_18888.Plane.incident p l ↔ p.succ ∈ singerLines3 l := by decide +kernel
    simp only [PEqualNP.Outside.L_meta_18888.Plane.target,PEqualNP.Outside.L_meta_18888.Plane.P,PEqualNP.Outside.L_meta_18888.Plane.L,eq]
  obtain ⟨D,sz,md,cd,j,a,b,rep,op,internal,on⟩ :=
    PEqualNP.Outside.L_meta_18888.Plane.Orbit.canonicalCircuit C mon (fun x => (correct x).trans (relate x).symm) small
  have code : ∀ a b : Fin 25, PEqualNP.Outside.L_meta_18888.Plane.Orbit.canonical a b →
      ∃ t ∈ ([1,2,14,16,313,316,339] : List ℕ),
        ∀ i : Fin 25, (i = a ∨ i = b) ↔ (i.val = t/25 ∨ i.val = t%25) := by
    intro u v
    have finite : ∀ u v : Fin 25, PEqualNP.Outside.L_meta_18888.Plane.Orbit.canonical u v →
        let t := 25*(min u v).val+(max u v).val
        t ∈ ([1,2,14,16,313,316,339] : List ℕ) ∧
        ∀ i : Fin 25, (i = u ∨ i = v) ↔ (i.val = t/25 ∨ i.val = t%25) := by
      unfold PEqualNP.Outside.L_meta_18888.Plane.Orbit.canonical
      decide +kernel
    intro h
    exact ⟨_,(finite u v h).1,(finite u v h).2⟩
  obtain ⟨t,mem,repr⟩ := code a b rep
  have bits : (fun i : Fin 25 => decide (i.val = t/25 ∨ i.val = t%25)) = PEqualNP.Outside.L_meta_18888.Plane.pair a b := by
    funext i
    simp only [PEqualNP.Outside.L_meta_18888.Plane.pair,repr]
  exact ⟨D,md,fun x => (cd x).trans (relate x),sz ▸ small,j,t,mem,op,internal,bits ▸ on⟩
