import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_653

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen])]
  exact getD_snoc_eq _ _ _ _ hlen.symm

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma list_any_congr_mem {α : Type*} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hpx⟩; exact ⟨x, hx, by rw [← h x hx]; exact hpx⟩
  · rintro ⟨x, hx, hqx⟩; exact ⟨x, hx, by rw [h x hx]; exact hqx⟩

private def pushOrList (m : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: ws => pushOrList m (gs ++ [⟨GateOp.or, [acc, w]⟩]) (m + gs.length) ws

private lemma pushOrList_props (m : ℕ) (ws : List ℕ) :
    ∀ (gs : List Gate) (acc : ℕ),
      (∀ g ∈ gs, OkGate g) →
      acc < m + gs.length →
      (∀ w ∈ ws, w < m + gs.length) →
      (∀ g ∈ (pushOrList m gs acc ws).1, OkGate g) ∧
      (pushOrList m gs acc ws).1.length = gs.length + ws.length ∧
      (pushOrList m gs acc ws).2 < m + (pushOrList m gs acc ws).1.length ∧
      (∀ x : List Bool, x.length = m →
        (∀ i < m + gs.length,
          (wiresFrom (pushOrList m gs acc ws).1 x).getD i false = (wiresFrom gs x).getD i false) ∧
        (wiresFrom (pushOrList m gs acc ws).1 x).getD (pushOrList m gs acc ws).2 false =
          ((wiresFrom gs x).getD acc false ||
            ws.any (fun w => (wiresFrom gs x).getD w false))) := by
  induction ws with
  | nil =>
    intro gs acc hok hacc _
    refine ⟨hok, by simp [pushOrList], hacc, fun x _ => ⟨fun _ _ => rfl, by simp [pushOrList]⟩⟩
  | cons w ws ih =>
    intro gs acc hok hacc hws
    set gs' := gs ++ [⟨GateOp.or, [acc, w]⟩] with hgs'
    have hok' : ∀ g ∈ gs', OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hok g h
      · simp at h; subst h; simp [OkGate]
    have hlen' : gs'.length = gs.length + 1 := by simp [hgs']
    have hacc' : m + gs.length < m + gs'.length := by omega
    have hws' : ∀ u ∈ ws, u < m + gs'.length := by
      intro u hu
      have := hws u (List.mem_cons_of_mem _ hu)
      omega
    obtain ⟨hok2, hlen2, hlt2, hev2⟩ := ih gs' (m + gs.length) hok' hacc' hws'
    refine ⟨hok2, ?_, hlt2, ?_⟩
    · show (pushOrList m gs' (m + gs.length) ws).1.length = gs.length + (w :: ws).length
      rw [hlen2, hlen']
      simp
      omega
    · intro x hx
      obtain ⟨hpres, hval⟩ := hev2 x hx
      have hstep_pres : ∀ i < m + gs.length,
          (wiresFrom gs' x).getD i false = (wiresFrom gs x).getD i false := by
        intro i hi
        rw [hgs', wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
        exact getD_snoc_lt _ _ _ _ (by rw [wiresFrom_length, hx]; exact hi)
      have hstep_new : (wiresFrom gs' x).getD (m + gs.length) false =
          ((wiresFrom gs x).getD acc false || (wiresFrom gs x).getD w false) := by
        rw [hgs', wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length, hx])]
        simp [GateOp.eval]
      refine ⟨fun i hi => (hpres i (by omega)).trans (hstep_pres i hi), ?_⟩
      show (wiresFrom (pushOrList m gs' (m + gs.length) ws).1 x).getD
          (pushOrList m gs' (m + gs.length) ws).2 false = _
      rw [hval, hstep_new]
      have hany : ws.any (fun u => (wiresFrom gs' x).getD u false) =
          ws.any (fun u => (wiresFrom gs x).getD u false) :=
        list_any_congr_mem fun u hu => hstep_pres u (hws u (List.mem_cons_of_mem _ hu))
      rw [hany]
      simp [Bool.or_assoc]

private def pushStarStep (m : ℕ) (gs : List Gate) (acc : ℕ) (u : ℕ) (vs : List ℕ) :
    List Gate × ℕ :=
  match vs with
  | [] => (gs, acc)
  | v₀ :: vs' =>
    let r1 := pushOrList m gs v₀ vs'
    let gs1 := r1.1 ++ [⟨GateOp.and, [u, r1.2]⟩]
    let w_and := m + r1.1.length
    let gs2 := gs1 ++ [⟨GateOp.or, [acc, w_and]⟩]
    (gs2, m + gs1.length)

private lemma pushStarStep_props (m : ℕ) (gs : List Gate) (acc u : ℕ) (vs : List ℕ)
    (hok : ∀ g ∈ gs, OkGate g) (hacc : acc < m + gs.length) (hu : u < m + gs.length)
    (hvs : ∀ v ∈ vs, v < m + gs.length) :
    (∀ g ∈ (pushStarStep m gs acc u vs).1, OkGate g) ∧
    (pushStarStep m gs acc u vs).1.length ≤ gs.length + vs.length + 1 ∧
    (pushStarStep m gs acc u vs).2 < m + (pushStarStep m gs acc u vs).1.length ∧
    (∀ x : List Bool, x.length = m →
      (∀ i < m + gs.length,
        (wiresFrom (pushStarStep m gs acc u vs).1 x).getD i false = (wiresFrom gs x).getD i false) ∧
      (wiresFrom (pushStarStep m gs acc u vs).1 x).getD (pushStarStep m gs acc u vs).2 false =
        ((wiresFrom gs x).getD acc false ||
          ((wiresFrom gs x).getD u false && vs.any (fun v => (wiresFrom gs x).getD v false)))) := by
  cases vs with
  | nil =>
    refine ⟨hok, by simp [pushStarStep], hacc, fun x _ => ⟨fun _ _ => rfl, by simp [pushStarStep]⟩⟩
  | cons v₀ vs' =>
    obtain ⟨hok1, hlen1, hlt1, hev1⟩ := pushOrList_props m vs' gs v₀ hok
      (hvs v₀ List.mem_cons_self) (fun v hv => hvs v (List.mem_cons_of_mem _ hv))
    set r1 := pushOrList m gs v₀ vs' with hr1
    set gs1 := r1.1 ++ [⟨GateOp.and, [u, r1.2]⟩] with hgs1
    set w_and := m + r1.1.length with hwand
    set gs2 := gs1 ++ [⟨GateOp.or, [acc, w_and]⟩] with hgs2
    have hok1' : ∀ g ∈ gs1, OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hok1 g h
      · simp at h; subst h; simp [OkGate]
    have hok2 : ∀ g ∈ gs2, OkGate g := by
      intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hok1' g h
      · simp at h; subst h; simp [OkGate]
    have hlen_gs2 : gs2.length = gs.length + (v₀ :: vs').length + 1 := by
      simp [hgs2, hgs1, hlen1]; omega
    refine ⟨hok2, ?_, ?_, ?_⟩
    · show gs2.length ≤ gs.length + (v₀ :: vs').length + 1; omega
    · show m + gs1.length < m + gs2.length; simp [hgs2]
    · intro x hx
      obtain ⟨hpres1, hval1⟩ := hev1 x hx
      have hpres_and : ∀ i < m + r1.1.length,
          (wiresFrom gs1 x).getD i false = (wiresFrom r1.1 x).getD i false := by
        intro i hi
        rw [hgs1, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
        exact getD_snoc_lt _ _ _ _ (by rw [wiresFrom_length, hx]; exact hi)
      have hpres_or : ∀ i < m + gs1.length,
          (wiresFrom gs2 x).getD i false = (wiresFrom gs1 x).getD i false := by
        intro i hi
        rw [hgs2, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
        exact getD_snoc_lt _ _ _ _ (by rw [wiresFrom_length, hx]; exact hi)
      have hval_and : (wiresFrom gs1 x).getD w_and false =
          ((wiresFrom r1.1 x).getD u false && (wiresFrom r1.1 x).getD r1.2 false) := by
        rw [hgs1, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length, hx])]
        simp [GateOp.eval]
      have hval_or : (wiresFrom gs2 x).getD (m + gs1.length) false =
          ((wiresFrom gs1 x).getD acc false || (wiresFrom gs1 x).getD w_and false) := by
        rw [hgs2, wiresFrom_append, wiresFrom_cons, wiresFrom_nil,
            getD_snoc_eq _ _ _ _ (by rw [wiresFrom_length, hx])]
        simp [GateOp.eval]
      refine ⟨?_, ?_⟩
      · intro i hi
        have hlen_le : gs.length ≤ r1.1.length := by omega
        have hlen_le1 : r1.1.length ≤ gs1.length := by simp [hgs1]
        exact (hpres_or i (by omega)).trans ((hpres_and i (by omega)).trans (hpres1 i hi))
      · show (wiresFrom gs2 x).getD (m + gs1.length) false = _
        rw [hval_or, hpres_and acc (by omega), hpres1 acc hacc,
            hval_and, hpres1 u hu, hval1]
        simp

private def pushStars (m : ℕ) (gs : List Gate) (acc : ℕ) : List (ℕ × List ℕ) → List Gate × ℕ
  | [] => (gs, acc)
  | (u, vs) :: rest =>
    let r := pushStarStep m gs acc u vs
    pushStars m r.1 r.2 rest

private lemma pushStars_props (m : ℕ) (stars : List (ℕ × List ℕ)) :
    ∀ (gs : List Gate) (acc : ℕ),
      (∀ g ∈ gs, OkGate g) →
      acc < m + gs.length →
      (∀ p ∈ stars, p.1 < m ∧ ∀ v ∈ p.2, v < m) →
      (∀ g ∈ (pushStars m gs acc stars).1, OkGate g) ∧
      (pushStars m gs acc stars).1.length ≤
        gs.length + (stars.map (fun p => p.2.length + 1)).sum ∧
      (pushStars m gs acc stars).2 < m + (pushStars m gs acc stars).1.length ∧
      (∀ x : List Bool, x.length = m →
        (∀ i < m + gs.length,
          (wiresFrom (pushStars m gs acc stars).1 x).getD i false = (wiresFrom gs x).getD i false) ∧
        (wiresFrom (pushStars m gs acc stars).1 x).getD (pushStars m gs acc stars).2 false =
          ((wiresFrom gs x).getD acc false ||
            stars.any (fun p => (wiresFrom gs x).getD p.1 false &&
              p.2.any (fun v => (wiresFrom gs x).getD v false)))) := by
  induction stars with
  | nil =>
    intro gs acc hok hacc _
    refine ⟨hok, by simp [pushStars], hacc, fun x _ => ⟨fun _ _ => rfl, by simp [pushStars]⟩⟩
  | cons st rest ih =>
    obtain ⟨u, vs⟩ := st
    intro gs acc hok hacc hst
    have hst0 := hst (u, vs) List.mem_cons_self
    obtain ⟨hok1, hlen1, hlt1, hev1⟩ := pushStarStep_props m gs acc u vs hok hacc
      (by omega) (fun v hv => by have := hst0.2 v hv; omega)
    set r := pushStarStep m gs acc u vs with hr
    obtain ⟨hok2, hlen2, hlt2, hev2⟩ := ih r.1 r.2 hok1 hlt1
      (fun p hp => hst p (List.mem_cons_of_mem _ hp))
    refine ⟨hok2, ?_, hlt2, ?_⟩
    · show (pushStars m r.1 r.2 rest).1.length ≤
        gs.length + (((u, vs) :: rest).map (fun p => p.2.length + 1)).sum
      simp only [List.map_cons, List.sum_cons]
      omega
    · intro x hx
      obtain ⟨hpres1, hval1⟩ := hev1 x hx
      obtain ⟨hpres2, hval2⟩ := hev2 x hx
      have hlen_le : gs.length ≤ r.1.length := by
        cases vs with
        | nil => simp [hr, pushStarStep]
        | cons v₀ vs' =>
          have := (pushOrList_props m vs' gs v₀ hok (by have := hst0.2 v₀ List.mem_cons_self; omega)
            (fun v hv => by have := hst0.2 v (List.mem_cons_of_mem _ hv); omega)).2.1
          simp [hr, pushStarStep]
          omega
      refine ⟨fun i hi => (hpres2 i (by omega)).trans (hpres1 i hi), ?_⟩
      show (wiresFrom (pushStars m r.1 r.2 rest).1 x).getD (pushStars m r.1 r.2 rest).2 false = _
      rw [hval2, hval1]
      have hany : rest.any (fun p => (wiresFrom r.1 x).getD p.1 false &&
            p.2.any (fun v => (wiresFrom r.1 x).getD v false)) =
          rest.any (fun p => (wiresFrom gs x).getD p.1 false &&
            p.2.any (fun v => (wiresFrom gs x).getD v false)) := by
        refine list_any_congr_mem fun p hp => ?_
        have hpm := hst p (List.mem_cons_of_mem _ hp)
        rw [hpres1 p.1 (by omega)]
        congr 1
        exact list_any_congr_mem fun v hv => hpres1 v (by have := hpm.2 v hv; omega)
      rw [hany]
      simp [Bool.or_assoc]

private lemma L653_getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma L653_getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma L653_getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact L653_getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private def L653_step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def L653_mapGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

-- Renaming wires: inputs are sent anywhere, gate wires keep their order.
private lemma L653_wires (r : ℕ → ℕ) (m m' : ℕ) (hr1 : ∀ i, i < m → r i < m')
    (hr2 : ∀ j, r (m + j) = m' + j) (gs : List Gate) :
    ∀ (w w' : List Bool) (j : ℕ), w.length = m + j → w'.length = m' + j →
      (∀ i, w.getD i false = w'.getD (r i) false) →
      ∀ i, (gs.foldl L653_step w).getD i false =
        ((gs.map (L653_mapGate r)).foldl L653_step w').getD (r i) false := by
  induction gs with
  | nil => intro w w' j _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' j hlen hlen' hinv
    have hv : (L653_mapGate r g).op.eval ((L653_mapGate r g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [L653_mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      exact (hinv i).symm
    simp only [List.map_cons, List.foldl_cons]
    refine ih _ _ (j + 1) ?_ ?_ ?_
    · simp only [L653_step, List.length_append, List.length_singleton, hlen]
      omega
    · simp only [L653_step, List.length_append, List.length_singleton, hlen']
      omega
    · intro i
      show (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false =
        (w' ++ [(L653_mapGate r g).op.eval ((L653_mapGate r g).inputs.map fun i => w'.getD i false)]).getD
          (r i) false
      rw [hv]
      by_cases hi : i = w.length
      · have hri : r i = w'.length := by rw [hi, hlen, hr2, hlen']
        rw [L653_getD_snoc_eq _ _ _ _ hi, L653_getD_snoc_eq _ _ _ _ hri]
      · have hri : r i ≠ w'.length := by
          by_cases him : i < m
          · have := hr1 i him
            omega
          · obtain ⟨j0, rfl⟩ : ∃ j0, i = m + j0 := ⟨i - m, by omega⟩
            rw [hr2]
            omega
        rw [L653_getD_snoc_ne _ _ _ _ hi, L653_getD_snoc_ne _ _ _ _ hri]
        exact hinv i

-- Substituting inputs for inputs does not increase circuit size.
private lemma L653_subst {m m' : ℕ} (e : Fin m → Fin m') (f : (Fin m → Bool) → Bool) (s : ℕ)
    (h : HasCircuitSize m f s) : HasCircuitSize m' (fun x => f (fun i => x (e i))) s := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  let r : ℕ → ℕ := fun i => if h : i < m then (e ⟨i, h⟩ : ℕ) else i - m + m'
  have hr1 : ∀ i, i < m → r i < m' := by
    intro i hi
    simp only [r, dif_pos hi]
    exact (e ⟨i, hi⟩).isLt
  have hr2 : ∀ j, r (m + j) = m' + j := by
    intro j
    have hnot : ¬ (m + j < m) := by omega
    simp only [r, dif_neg hnot]
    omega
  refine ⟨⟨C.gates.map (L653_mapGate r), r C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have h0 := hfan g0 hg0
    exact ⟨h0.1, by simpa [L653_mapGate] using h0.2⟩
  · simpa [Circuit.size] using hsz
  · intro x
    show (⟨C.gates.map (L653_mapGate r), r C.output⟩ : Circuit).eval (List.ofFn x) = f (fun i => x (e i))
    rw [← hev (fun i => x (e i))]
    have hbase : ∀ i, (List.ofFn fun i => x (e i)).getD i false = (List.ofFn x).getD (r i) false := by
      intro i
      by_cases hi : i < m
      · have hri : r i = (e ⟨i, hi⟩ : ℕ) := by simp only [r, dif_pos hi]
        rw [List.getD_eq_getElem _ _ (by simpa using hi), hri,
          List.getD_eq_getElem _ _ (by simp)]
        simp
      · obtain ⟨j0, rfl⟩ : ∃ j0, i = m + j0 := ⟨i - m, by omega⟩
        rw [hr2, List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp)]
    have key := L653_wires r m m' hr1 hr2 C.gates (List.ofFn fun i => x (e i)) (List.ofFn x) 0
      (by simp) (by simp) hbase C.output
    exact key.symm

-- Appending star gates (centre AND an OR of leaves, then OR into the output) to a circuit.
private lemma L653_core (m : ℕ) (C : Circuit) (hfan : FanInTwo C) (hout : C.output < m + C.gates.length)
    (stars : List (ℕ × List ℕ)) (hst : ∀ p ∈ stars, p.1 < m ∧ ∀ v ∈ p.2, v < m) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size + (stars.map (fun p => p.2.length + 1)).sum ∧
      ∀ X : List Bool, X.length = m →
        D.eval X = (C.eval X ||
          stars.any (fun p => X.getD p.1 false && p.2.any (fun v => X.getD v false))) := by
  obtain ⟨hok, hlen, hlt, hev⟩ := pushStars_props m stars C.gates C.output hfan hout hst
  refine ⟨⟨(pushStars m C.gates C.output stars).1, (pushStars m C.gates C.output stars).2⟩, hok, hlen, ?_⟩
  intro X hX
  obtain ⟨_, hval⟩ := hev X hX
  show (wiresFrom (pushStars m C.gates C.output stars).1 X).getD (pushStars m C.gates C.output stars).2 false = _
  rw [hval]
  congr 1
  refine list_any_congr_mem fun p hp => ?_
  have hp' := hst p hp
  rw [wiresFrom_getD_lt _ _ _ (by omega)]
  congr 1
  exact list_any_congr_mem fun v hv => wiresFrom_getD_lt _ _ _ (by have := hp'.2 v hv; omega)

theorem main_aux : ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), 1 ≤ h → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x u.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x v.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) := by
  intro N h u v g hh s
  have h2 : 0 < 2 * h := by omega
  have hvalP : ∀ (x : Fin (N + 2 * h) → Bool) (i : ℕ) (hi : i < 2 * h),
      (List.ofFn x).getD (N + i) false = x (Fin.natAdd N ⟨i, hi⟩) := by
    intro x i hi
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp [Fin.natAdd]
  have hvalV : ∀ (x : Fin (N + 2 * h) → Bool) (w : Fin N),
      (List.ofFn x).getD (w : ℕ) false = x (Fin.castAdd (2 * h) w) := by
    intro x w
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_ofFn]
    exact congrArg x (Fin.ext rfl)
  constructor
  · intro hA
    let e : Fin (N + 1) → Fin (N + 2 * h) := fun i =>
      if hi : (i : ℕ) < N then Fin.castAdd (2 * h) ⟨i, hi⟩ else Fin.natAdd N ⟨0, h2⟩
    have he1 : ∀ i : Fin N, e i.castSucc = Fin.castAdd (2 * h) i := by
      intro i
      simp [e]
      exact Fin.ext rfl
    have he2 : e (Fin.last N) = Fin.natAdd N ⟨0, h2⟩ := by
      simp [e]
    obtain ⟨C, hfan, hsz, hev⟩ := L653_subst e _ s hA
    have hev' : ∀ x : Fin (N + 2 * h) → Bool, C.eval (List.ofFn x) =
        (g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) ||
          (x (Fin.castAdd (2 * h) u) && x (Fin.natAdd N ⟨0, h2⟩))) := by
      intro x
      rw [hev x]
      simp only [he1, he2]
    have hout : C.output < (N + 2 * h) + C.gates.length := by
      by_contra hge
      have h1 := hev' (fun _ => true)
      have h0 : C.eval (List.ofFn (fun _ : Fin (N + 2 * h) => true)) = false := by
        show (wiresFrom C.gates _).getD C.output false = false
        exact List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)
      rw [h0] at h1
      simp at h1
    obtain ⟨D, hfanD, hszD, hevD⟩ := L653_core (N + 2 * h) C hfan hout
      ((List.range h).map (fun k => (N + (2 * k + 1), [N + 2 * k, if k + 1 < h then N + (2 * k + 2) else (v : ℕ)])))
      (by
        intro p hp
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
        rw [List.mem_range] at hk
        refine ⟨by omega, ?_⟩
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · omega
        · have := v.isLt
          split_ifs <;> omega)
    refine ⟨D, hfanD, ?_, ?_⟩
    · have hsum : (((List.range h).map (fun k => (N + (2 * k + 1), [N + 2 * k, if k + 1 < h then N + (2 * k + 2) else (v : ℕ)]))).map
          (fun p => p.2.length + 1)).sum = 3 * h := by
        simp [List.map_map, Function.comp_def, mul_comm]
      have hC : C.size ≤ s := hsz
      rw [hsum] at hszD
      omega
    · intro x
      rw [hevD (List.ofFn x) (by simp), hev' x, Bool.or_assoc]
      congr 1
      apply Bool.eq_iff_iff.mpr
      rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
      constructor
      · rintro (⟨hu', hp0⟩ | ⟨p, hp, hpv⟩)
        · exact ⟨⟨0, h2⟩, hp0, Or.inl ⟨rfl, hu'⟩⟩
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
          rw [List.mem_range] at hk
          simp only [Bool.and_eq_true, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hpv
          obtain ⟨hc, hl | hr⟩ := hpv
          · refine ⟨⟨2 * k, by omega⟩, ?_, Or.inr (Or.inr ⟨⟨2 * k + 1, by omega⟩, rfl, ?_⟩)⟩
            · rw [← hvalP x (2 * k) (by omega)]
              exact hl
            · rw [← hvalP x (2 * k + 1) (by omega)]
              exact hc
          · by_cases hk1 : k + 1 < h
            · rw [if_pos hk1] at hr
              refine ⟨⟨2 * k + 1, by omega⟩, ?_, Or.inr (Or.inr ⟨⟨2 * k + 2, by omega⟩, rfl, ?_⟩)⟩
              · rw [← hvalP x (2 * k + 1) (by omega)]
                exact hc
              · rw [← hvalP x (2 * k + 2) (by omega)]
                exact hr
            · rw [if_neg hk1] at hr
              refine ⟨⟨2 * k + 1, by omega⟩, ?_, Or.inr (Or.inl ⟨by simp only []; omega, ?_⟩)⟩
              · rw [← hvalP x (2 * k + 1) (by omega)]
                exact hc
              · rw [← hvalV x v]
                exact hr
      · rintro ⟨i, hi, hcase⟩
        rcases hcase with ⟨hi0, hxu⟩ | ⟨hilast, hxv⟩ | ⟨j, hj, hxj⟩
        · left
          have hi' : i = ⟨0, h2⟩ := Fin.ext hi0
          subst hi'
          exact ⟨hxu, hi⟩
        · right
          refine ⟨_, List.mem_map.mpr ⟨h - 1, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
          simp only [Bool.and_eq_true, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
          refine ⟨?_, Or.inr ?_⟩
          · rw [hvalP x (2 * (h - 1) + 1) (by omega)]
            have hi' : (⟨2 * (h - 1) + 1, by omega⟩ : Fin (2 * h)) = i := Fin.ext (by simp only []; omega)
            rw [hi']
            exact hi
          · rw [if_neg (by omega), hvalV x v]
            exact hxv
        · right
          obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (i : ℕ)
          · refine ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr (by have := j.isLt; omega), rfl⟩, ?_⟩
            simp only [Bool.and_eq_true, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
            refine ⟨?_, Or.inl ?_⟩
            · rw [hvalP x (2 * k + 1) (by have := j.isLt; omega)]
              have hj' : (⟨2 * k + 1, by have := j.isLt; omega⟩ : Fin (2 * h)) = j := Fin.ext (by simp only []; omega)
              rw [hj']
              exact hxj
            · rw [hvalP x (2 * k) (by have := i.isLt; omega)]
              have hi' : (⟨2 * k, by have := i.isLt; omega⟩ : Fin (2 * h)) = i := Fin.ext (by simp only []; omega)
              rw [hi']
              exact hi
          · refine ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr (by have := j.isLt; omega), rfl⟩, ?_⟩
            simp only [Bool.and_eq_true, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
            refine ⟨?_, Or.inr ?_⟩
            · rw [hvalP x (2 * k + 1) (by have := i.isLt; omega)]
              have hi' : (⟨2 * k + 1, by have := i.isLt; omega⟩ : Fin (2 * h)) = i := Fin.ext (by simp only []; omega)
              rw [hi']
              exact hi
            · rw [if_pos (by have := j.isLt; omega), hvalP x (2 * k + 2) (by have := j.isLt; omega)]
              have hj' : (⟨2 * k + 2, by have := j.isLt; omega⟩ : Fin (2 * h)) = j := Fin.ext (by simp only []; omega)
              rw [hj']
              exact hxj
  · intro hB
    let e : Fin (N + 1) → Fin (N + 2 * h) := fun i =>
      if hi : (i : ℕ) < N then Fin.castAdd (2 * h) ⟨i, hi⟩ else Fin.natAdd N ⟨2 * h - 1, by omega⟩
    have he1 : ∀ i : Fin N, e i.castSucc = Fin.castAdd (2 * h) i := by
      intro i
      simp [e]
      exact Fin.ext rfl
    have he2 : e (Fin.last N) = Fin.natAdd N ⟨2 * h - 1, by omega⟩ := by
      simp [e]
    obtain ⟨C, hfan, hsz, hev⟩ := L653_subst e _ s hB
    have hev' : ∀ x : Fin (N + 2 * h) → Bool, C.eval (List.ofFn x) =
        (g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) ||
          (x (Fin.castAdd (2 * h) v) && x (Fin.natAdd N ⟨2 * h - 1, by omega⟩))) := by
      intro x
      rw [hev x]
      simp only [he1, he2]
    have hout : C.output < (N + 2 * h) + C.gates.length := by
      by_contra hge
      have h1 := hev' (fun _ => true)
      have h0 : C.eval (List.ofFn (fun _ : Fin (N + 2 * h) => true)) = false := by
        show (wiresFrom C.gates _).getD C.output false = false
        exact List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)
      rw [h0] at h1
      simp at h1
    obtain ⟨D, hfanD, hszD, hevD⟩ := L653_core (N + 2 * h) C hfan hout
      ((List.range h).map (fun k => (N + 2 * k, [if k = 0 then (u : ℕ) else N + (2 * k - 1), N + (2 * k + 1)])))
      (by
        intro p hp
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
        rw [List.mem_range] at hk
        refine ⟨by omega, ?_⟩
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · have := u.isLt
          split_ifs <;> omega
        · omega)
    refine ⟨D, hfanD, ?_, ?_⟩
    · have hsum : (((List.range h).map (fun k => (N + 2 * k, [if k = 0 then (u : ℕ) else N + (2 * k - 1), N + (2 * k + 1)]))).map
          (fun p => p.2.length + 1)).sum = 3 * h := by
        simp [List.map_map, Function.comp_def, mul_comm]
      have hC : C.size ≤ s := hsz
      rw [hsum] at hszD
      omega
    · intro x
      rw [hevD (List.ofFn x) (by simp), hev' x, Bool.or_assoc]
      congr 1
      apply Bool.eq_iff_iff.mpr
      rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
      constructor
      · rintro (⟨hxv, hpl⟩ | ⟨p, hp, hpv⟩)
        · exact ⟨⟨2 * h - 1, by omega⟩, hpl, Or.inr (Or.inl ⟨by simp only []; omega, hxv⟩)⟩
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
          rw [List.mem_range] at hk
          simp only [Bool.and_eq_true, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hpv
          obtain ⟨hc, hl | hr⟩ := hpv
          · by_cases hk0 : k = 0
            · subst hk0
              rw [if_pos rfl] at hl
              refine ⟨⟨0, h2⟩, ?_, Or.inl ⟨rfl, ?_⟩⟩
              · rw [← hvalP x 0 h2]
                exact hc
              · rw [← hvalV x u]
                exact hl
            · rw [if_neg hk0] at hl
              refine ⟨⟨2 * k - 1, by omega⟩, ?_, Or.inr (Or.inr ⟨⟨2 * k, by omega⟩, by simp only []; omega, ?_⟩)⟩
              · rw [← hvalP x (2 * k - 1) (by omega)]
                exact hl
              · rw [← hvalP x (2 * k) (by omega)]
                exact hc
          · refine ⟨⟨2 * k, by omega⟩, ?_, Or.inr (Or.inr ⟨⟨2 * k + 1, by omega⟩, rfl, ?_⟩)⟩
            · rw [← hvalP x (2 * k) (by omega)]
              exact hc
            · rw [← hvalP x (2 * k + 1) (by omega)]
              exact hr
      · rintro ⟨i, hi, hcase⟩
        rcases hcase with ⟨hi0, hxu⟩ | ⟨hilast, hxv⟩ | ⟨j, hj, hxj⟩
        · right
          refine ⟨_, List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
          simp only [Bool.and_eq_true, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
          refine ⟨?_, Or.inl ?_⟩
          · rw [hvalP x (2 * 0) (by omega)]
            have hi' : (⟨2 * 0, by omega⟩ : Fin (2 * h)) = i := Fin.ext (by simp only []; omega)
            rw [hi']
            exact hi
          · show (List.ofFn x).getD (u : ℕ) false = true
            rw [hvalV x u]
            exact hxu
        · left
          have key : ∀ (q : 2 * h - 1 < 2 * h), x (Fin.natAdd N ⟨2 * h - 1, q⟩) = true := by
            intro q
            have hi' : (⟨2 * h - 1, q⟩ : Fin (2 * h)) = i := Fin.ext (by simp only []; omega)
            rw [hi']
            exact hi
          exact ⟨hxv, key _⟩
        · right
          obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (i : ℕ)
          · refine ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr (by have := j.isLt; omega), rfl⟩, ?_⟩
            simp only [Bool.and_eq_true, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
            refine ⟨?_, Or.inr ?_⟩
            · rw [hvalP x (2 * k) (by have := i.isLt; omega)]
              have hi' : (⟨2 * k, by have := i.isLt; omega⟩ : Fin (2 * h)) = i := Fin.ext (by simp only []; omega)
              rw [hi']
              exact hi
            · rw [hvalP x (2 * k + 1) (by have := j.isLt; omega)]
              have hj' : (⟨2 * k + 1, by have := j.isLt; omega⟩ : Fin (2 * h)) = j := Fin.ext (by simp only []; omega)
              rw [hj']
              exact hxj
          · refine ⟨_, List.mem_map.mpr ⟨k + 1, List.mem_range.mpr (by have := j.isLt; omega), rfl⟩, ?_⟩
            simp only [Bool.and_eq_true, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
            refine ⟨?_, Or.inl ?_⟩
            · rw [hvalP x (2 * (k + 1)) (by have := j.isLt; omega)]
              have hj' : (⟨2 * (k + 1), by have := j.isLt; omega⟩ : Fin (2 * h)) = j := Fin.ext (by simp only []; omega)
              rw [hj']
              exact hxj
            · rw [if_neg (by omega)]
              have e3 : N + (2 * (k + 1) - 1) = N + (2 * k + 1) := by omega
              rw [e3, hvalP x (2 * k + 1) (by have := i.isLt; omega)]
              have hi' : (⟨2 * k + 1, by have := i.isLt; omega⟩ : Fin (2 * h)) = i := Fin.ext (by simp only []; omega)
              rw [hi']
              exact hi

end PEqualNP.Outside.L_meta_653

theorem PEqualNP.Outside.L_meta_653 : ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), 1 ≤ h → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x u.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x v.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) :=
  PEqualNP.Outside.L_meta_653.main_aux
