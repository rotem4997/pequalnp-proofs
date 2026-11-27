import PEqualNP.MetaComplexity.Helpers.Deg2Transp

/-!
# The contexts as appended gates: D2-15 (iii) (helper for L-meta-649)

Card `card15c_contexts` of the degree-two card plan, with its statement as in
the plan. Construction: the senders `T_or ∪ T_andf` are processed in descending order; each wire
carries absent, the constant `1`, or a wire computing its context so far; an OR of T sends its
context to each child of degree at least one, an AND of T with a label sends context AND label
to its degree-two child; two wires meeting at a receiver are merged by one OR gate. At most two
new gates per sender. Conjecture until checked.
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ}

/-! ### Appending gates keeps the old wires -/

theorem tr_getElem?_prefix {gs gs' : List G} (hp : gs <+: gs') {i : ℕ} (hi : i < gs.length) :
    gs'[i]? = gs[i]? := by
  obtain ⟨t, rfl⟩ := hp
  exact List.getElem?_append_left hi

theorem tr_val_prefix {gs gs' : List G} (hp : gs <+: gs') (o o' : ℕ)
    (x : Fin (N + N) → Bool) : ∀ n, n < N + N + gs.length →
      (⟨gs', o'⟩ : Dag N).val x n = (⟨gs, o⟩ : Dag N).val x n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  have key : ∀ a, (if _ : a < n then (⟨gs', o'⟩ : Dag N).val x a else false) =
      (if _ : a < n then (⟨gs, o⟩ : Dag N).val x a else false) := by
    intro a
    split_ifs with ha
    · exact ih a ha (by omega)
    · rfl
  conv_lhs => rw [Dag.val]
  conv_rhs => rw [Dag.val]
  by_cases hi : n < N + N
  · rw [dif_pos hi, dif_pos hi]
  · rw [dif_neg hi, dif_neg hi]
    have hg : gs'[n - (N + N)]? = gs[n - (N + N)]? := tr_getElem?_prefix hp (by omega)
    dsimp only
    rw [hg]
    cases gs[n - (N + N)]? with
    | none => rfl
    | some g => cases g <;> first | rfl | simp only [key]

theorem tr_deg_prefix {gs gs' : List G} (hp : gs <+: gs') (o o' : ℕ) :
    ∀ n, n < N + N + gs.length → (⟨gs', o'⟩ : Dag N).deg n = (⟨gs, o⟩ : Dag N).deg n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  have key : ∀ a, (if _ : a < n then (⟨gs', o'⟩ : Dag N).deg a else 0) =
      (if _ : a < n then (⟨gs, o⟩ : Dag N).deg a else 0) := by
    intro a
    split_ifs with ha
    · exact ih a ha (by omega)
    · rfl
  conv_lhs => rw [Dag.deg]
  conv_rhs => rw [Dag.deg]
  by_cases hi : n < N + N
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]
    have hg : gs'[n - (N + N)]? = gs[n - (N + N)]? := tr_getElem?_prefix hp (by omega)
    dsimp only
    rw [hg]
    cases gs[n - (N + N)]? with
    | none => rfl
    | some g => cases g <;> first | rfl | simp only [key]

theorem tr_gateAt_prefix {gs gs' : List G} (hp : gs <+: gs') (o o' : ℕ) {n : ℕ}
    (hn : n < N + N + gs.length) :
    (⟨gs', o'⟩ : Dag N).gateAt n = (⟨gs, o⟩ : Dag N).gateAt n := by
  unfold Dag.gateAt
  split_ifs with h
  · exact tr_getElem?_prefix hp (by omega)
  · rfl

theorem tr_gateAt_last (gs : List G) (g : G) (o : ℕ) :
    (⟨gs ++ [g], o⟩ : Dag N).gateAt (N + N + gs.length) = some g := by
  unfold Dag.gateAt
  rw [if_pos (by omega)]
  simp

/-! ### The state -/

/-- What a wire carries during the pass: nothing yet, the constant `1`, or a wire. -/
inductive tr_W where
  | absent
  | const
  | wire (n : ℕ)

/-- A wire the new gates may read: a point, a gate of X, or a new gate below `N + N + len`. -/
def tr_Good (D : Dag N) (len n : ℕ) : Prop :=
  n < N ∨ n ∈ D.X ∨ (N + N + D.size ≤ n ∧ n < N + N + len)

/-- The gate list extends `D` and every new gate is an AND or OR of good wires below it. -/
def tr_NewOK (D : Dag N) (gs : List G) : Prop :=
  D.gates <+: gs ∧ ∀ j g, D.size ≤ j → gs[j]? = some g →
    ∃ u v, (g = .and u v ∨ g = .or u v) ∧ tr_Good D j u ∧ tr_Good D j v

/-- `m` represents the function `P` (and `PT`, the same with every label true). -/
def tr_Ok (D : Dag N) (gs : List G) (m : tr_W) (P : (Fin (N + N) → Bool) → Prop)
    (PT : Prop) : Prop :=
  match m with
  | .absent => ¬ PT ∧ ∀ x, ¬ P x
  | .const => ∀ x, P x
  | .wire n => tr_Good D gs.length n ∧ ∀ x, ((⟨gs, D.out⟩ : Dag N).val x n = true ↔ P x)

theorem tr_X_lt {D : Dag N} {n : ℕ} (h : n ∈ D.X) : N + N ≤ n ∧ n < N + N + D.size := by
  have := Api.coneOf_sub D {D.out} (Finset.mem_filter.1 h).1
  exact Finset.mem_Ico.1 this

theorem tr_Good_mono {D : Dag N} {j len n : ℕ} (h : tr_Good D j n) (hj : j ≤ len) :
    tr_Good D len n := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h.1, by omega⟩)

theorem tr_Good_lt {D : Dag N} {len n : ℕ} (h : tr_Good D len n) (hl : D.size ≤ len) :
    n < N + N + len := by
  rcases h with h | h | h
  · omega
  · have := tr_X_lt h; omega
  · exact h.2

theorem tr_NewOK_size {D : Dag N} {gs : List G} (h : tr_NewOK D gs) : D.size ≤ gs.length :=
  h.1.length_le

theorem tr_Ok_lift {D : Dag N} {gs gs' : List G} {m : tr_W} {P PT}
    (h : tr_Ok D gs m P PT) (hp : gs <+: gs') (hD : D.size ≤ gs.length) :
    tr_Ok D gs' m P PT := by
  cases m with
  | absent => exact h
  | const => exact h
  | wire n =>
    obtain ⟨hg, hv⟩ := h
    refine ⟨tr_Good_mono hg hp.length_le, fun x => ?_⟩
    rw [tr_val_prefix hp D.out D.out x n (tr_Good_lt hg hD)]
    exact hv x

theorem tr_Ok_congr {D : Dag N} {gs : List G} {m : tr_W} {P P' : (Fin (N + N) → Bool) → Prop}
    {PT PT' : Prop} (h : tr_Ok D gs m P PT) (hP : ∀ x, P x ↔ P' x) (hT : PT ↔ PT') :
    tr_Ok D gs m P' PT' := by
  cases m with
  | absent => exact ⟨fun h' => h.1 (hT.2 h'), fun x h' => h.2 x ((hP x).2 h')⟩
  | const => exact fun x => (hP x).1 (h x)
  | wire n => exact ⟨h.1, fun x => (h.2 x).trans (hP x)⟩

theorem tr_NewOK_append {D : Dag N} {gs : List G} (h : tr_NewOK D gs) {g : G} {a b : ℕ}
    (hg : g = .and a b ∨ g = .or a b) (ha : tr_Good D gs.length a)
    (hb : tr_Good D gs.length b) : tr_NewOK D (gs ++ [g]) := by
  refine ⟨h.1.trans (List.prefix_append gs [g]), fun j g' hj hg' => ?_⟩
  by_cases hjl : j < gs.length
  · rw [List.getElem?_append_left hjl] at hg'
    exact h.2 j g' hj hg'
  · by_cases hje : j = gs.length
    · subst hje
      simp at hg'
      subst hg'
      exact ⟨a, b, hg, ha, hb⟩
    · have : (gs ++ [g])[j]? = none := by
        rw [List.getElem?_eq_none_iff]; simp; omega
      rw [this] at hg'; cases hg'

/-- Merge a message `m` into what a receiver carries. -/
def tr_merge (N : ℕ) (gs : List G) : tr_W → tr_W → List G × tr_W
  | .absent, m => (gs, m)
  | .const, _ => (gs, .const)
  | .wire a, .absent => (gs, .wire a)
  | .wire _, .const => (gs, .const)
  | .wire a, .wire b => (gs ++ [.or a b], .wire (N + N + gs.length))

theorem tr_merge_ok {D : Dag N} {gs : List G} (hN : tr_NewOK D gs) {u m : tr_W}
    {P Q PT QT} (hu : tr_Ok D gs u P PT) (hm : tr_Ok D gs m Q QT) :
    tr_NewOK D (tr_merge N gs u m).1 ∧ gs <+: (tr_merge N gs u m).1 ∧
      (tr_merge N gs u m).1.length ≤ gs.length + 1 ∧
      tr_Ok D (tr_merge N gs u m).1 (tr_merge N gs u m).2 (fun x => P x ∨ Q x) (PT ∨ QT) := by
  have hD := tr_NewOK_size hN
  cases u with
  | absent =>
    refine ⟨hN, List.prefix_refl gs, by simp [tr_merge], ?_⟩
    simp only [tr_merge]
    exact tr_Ok_congr hm (fun x => by simp [hu.2 x]) (by simp [hu.1])
  | const =>
    refine ⟨hN, List.prefix_refl gs, by simp [tr_merge], ?_⟩
    simp only [tr_merge]
    exact fun x => Or.inl (hu x)
  | wire a =>
    cases m with
    | absent =>
      refine ⟨hN, List.prefix_refl gs, by simp [tr_merge], ?_⟩
      simp only [tr_merge]
      exact tr_Ok_congr hu (fun x => by simp [hm.2 x]) (by simp [hm.1])
    | const =>
      refine ⟨hN, List.prefix_refl gs, by simp [tr_merge], ?_⟩
      simp only [tr_merge]
      exact fun x => Or.inr (hm x)
    | wire b =>
      simp only [tr_merge]
      have hp : gs <+: gs ++ [G.or a b] := List.prefix_append gs _
      refine ⟨tr_NewOK_append hN (Or.inr rfl) hu.1 hm.1, hp, by simp, ?_⟩
      have ha := tr_Good_lt hu.1 hD
      have hb := tr_Good_lt hm.1 hD
      refine ⟨Or.inr (Or.inr ⟨by omega, by simp⟩), fun x => ?_⟩
      rw [tr_val_or (tr_gateAt_last gs _ D.out) ha hb, tr_val_prefix hp D.out D.out x a ha,
        tr_val_prefix hp D.out D.out x b hb, Bool.or_eq_true, hu.2 x, hm.2 x]

/-- The message of an AND of T with label `f`: context AND `f`. -/
def tr_msgAnd (N : ℕ) (gs : List G) (u : tr_W) (f : ℕ) : List G × tr_W :=
  match u with
  | .absent => (gs, .absent)
  | .const => (gs, .wire f)
  | .wire n => (gs ++ [.and n f], .wire (N + N + gs.length))

theorem tr_msgAnd_ok {D : Dag N} {gs : List G} (hN : tr_NewOK D gs) {u : tr_W} {P PT}
    (hu : tr_Ok D gs u P PT) {f : ℕ} (hf : f < N ∨ f ∈ D.X) :
    tr_NewOK D (tr_msgAnd N gs u f).1 ∧ gs <+: (tr_msgAnd N gs u f).1 ∧
      (tr_msgAnd N gs u f).1.length ≤ gs.length + 1 ∧
      tr_Ok D (tr_msgAnd N gs u f).1 (tr_msgAnd N gs u f).2
        (fun x => P x ∧ D.val x f = true) PT := by
  have hD := tr_NewOK_size hN
  have hfg : tr_Good D gs.length f := by
    rcases hf with hf | hf
    · exact Or.inl hf
    · exact Or.inr (Or.inl hf)
  have hfl := tr_Good_lt hfg hD
  have hfv : ∀ (gs' : List G), D.gates <+: gs' → ∀ x,
      (⟨gs', D.out⟩ : Dag N).val x f = D.val x f := by
    intro gs' hp x
    rcases hf with hf | hf
    · exact tr_val_prefix hp D.out D.out x f (by omega)
    · exact tr_val_prefix hp D.out D.out x f (tr_X_lt hf).2
  cases u with
  | absent =>
    refine ⟨hN, List.prefix_refl gs, by simp [tr_msgAnd], ?_⟩
    simp only [tr_msgAnd]
    exact ⟨hu.1, fun x h => hu.2 x h.1⟩
  | const =>
    refine ⟨hN, List.prefix_refl gs, by simp [tr_msgAnd], ?_⟩
    simp only [tr_msgAnd]
    refine ⟨hfg, fun x => ?_⟩
    rw [hfv gs hN.1 x]
    exact ⟨fun h => ⟨hu x, h⟩, fun h => h.2⟩
  | wire n =>
    simp only [tr_msgAnd]
    have hp : gs <+: gs ++ [G.and n f] := List.prefix_append gs _
    refine ⟨tr_NewOK_append hN (Or.inl rfl) hu.1 hfg, hp, by simp, ?_⟩
    have hn := tr_Good_lt hu.1 hD
    refine ⟨Or.inr (Or.inr ⟨by omega, by simp⟩), fun x => ?_⟩
    rw [tr_val_and (tr_gateAt_last gs _ D.out) hn hfl, tr_val_prefix hp D.out D.out x n hn,
      hfv _ (hN.1.trans hp), Bool.and_eq_true, hu.2 x]

/-- Update the receiver `c` with the message `m`. -/
def tr_upd (N : ℕ) (st : List G × (ℕ → tr_W)) (c : ℕ) (m : tr_W) : List G × (ℕ → tr_W) :=
  ((tr_merge N st.1 (st.2 c) m).1, Function.update st.2 c (tr_merge N st.1 (st.2 c) m).2)

theorem tr_upd_ok {D : Dag N} {gs : List G} {w : ℕ → tr_W} (hN : tr_NewOK D gs)
    {R : ℕ → (Fin (N + N) → Bool) → Prop} {RT : ℕ → Prop}
    (hw : ∀ c, tr_Ok D gs (w c) (R c) (RT c)) {m : tr_W} {Q QT} (hm : tr_Ok D gs m Q QT)
    (r : ℕ) :
    tr_NewOK D (tr_upd N (gs, w) r m).1 ∧ gs <+: (tr_upd N (gs, w) r m).1 ∧
      (tr_upd N (gs, w) r m).1.length ≤ gs.length + 1 ∧
      ∀ c, tr_Ok D (tr_upd N (gs, w) r m).1 ((tr_upd N (gs, w) r m).2 c)
        (fun x => R c x ∨ (c = r ∧ Q x)) (RT c ∨ (c = r ∧ QT)) := by
  obtain ⟨h1, h2, h3, h4⟩ := tr_merge_ok hN (hw r) hm
  refine ⟨h1, h2, h3, fun c => ?_⟩
  simp only [tr_upd]
  by_cases hc : c = r
  · subst hc
    rw [Function.update_self]
    exact tr_Ok_congr h4 (fun x => by simp) (by simp)
  · rw [Function.update_of_ne hc]
    exact tr_Ok_congr (tr_Ok_lift (hw c) h2 (tr_NewOK_size hN)) (fun x => by simp [hc])
      (by simp [hc])

/-! ### The pass with senders restricted to a set -/

/-- `Top` with every sender in `S`. -/
inductive tr_TopS (D : Dag N) (S : Finset ℕ) (ok : ℕ → Prop) : ℕ → Prop
  | root : tr_TopS D S ok D.out
  | orStep {h c : ℕ} : tr_TopS D S ok h → h ∈ S → h ∈ D.Tor → D.Kid h c → 1 ≤ D.deg c →
      tr_TopS D S ok c
  | andStep {h f c : ℕ} : tr_TopS D S ok h → h ∈ S → h ∈ D.Tandf →
      (D.gateAt h = some (.and f c) ∨ D.gateAt h = some (.and c f)) →
      D.deg f = 0 → D.deg c = 2 → f < h → c < h → ok f → tr_TopS D S ok c

/-- One step of the pass from `h` to `c`. -/
def tr_Step (D : Dag N) (ok : ℕ → Prop) (h c : ℕ) : Prop :=
  (h ∈ D.Tor ∧ D.Kid h c ∧ 1 ≤ D.deg c) ∨
    (h ∈ D.Tandf ∧ ∃ f, (D.gateAt h = some (.and f c) ∨ D.gateAt h = some (.and c f)) ∧
      D.deg f = 0 ∧ D.deg c = 2 ∧ f < h ∧ c < h ∧ ok f)

theorem tr_Step_lt {D : Dag N} {ok : ℕ → Prop} {h c : ℕ} (hs : tr_Step D ok h c) : c < h := by
  rcases hs with ⟨-, ⟨_, _, _, hc⟩, -⟩ | ⟨-, f, -, -, -, -, hc, -⟩
  · exact hc
  · exact hc

theorem tr_TopS_mono {D : Dag N} {S S' : Finset ℕ} {ok : ℕ → Prop} (hS : S ⊆ S') {c : ℕ}
    (h : tr_TopS D S ok c) : tr_TopS D S' ok c := by
  induction h with
  | root => exact tr_TopS.root
  | orStep _ hm ht hk hd ih => exact tr_TopS.orStep ih (hS hm) ht hk hd
  | andStep _ hm ht hg hf hc2 hfh hch hok ih =>
    exact tr_TopS.andStep ih (hS hm) ht hg hf hc2 hfh hch hok

theorem tr_TopS_step {D : Dag N} {S : Finset ℕ} {ok : ℕ → Prop} {h c : ℕ}
    (hT : tr_TopS D S ok h) (hm : h ∈ S) (hs : tr_Step D ok h c) : tr_TopS D S ok c := by
  rcases hs with ⟨ht, hk, hd⟩ | ⟨ht, f, hg, hf, hc2, hfh, hch, hok⟩
  · exact tr_TopS.orStep hT hm ht hk hd
  · exact tr_TopS.andStep hT hm ht hg hf hc2 hfh hch hok

theorem tr_TopS_insert {D : Dag N} {S : Finset ℕ} {ok : ℕ → Prop} {h : ℕ}
    (hS : ∀ s ∈ S, h < s) (c : ℕ) :
    tr_TopS D (insert h S) ok c ↔ tr_TopS D S ok c ∨ (tr_TopS D S ok h ∧ tr_Step D ok h c) := by
  constructor
  · intro hT
    induction hT with
    | root => exact Or.inl tr_TopS.root
    | @orStep h' c' _ hm ht hk hd ih =>
      have hs : tr_Step D ok h' c' := Or.inl ⟨ht, hk, hd⟩
      rcases Finset.mem_insert.1 hm with rfl | hm
      · rcases ih with ih | ⟨ih, -⟩ <;> exact Or.inr ⟨ih, hs⟩
      · rcases ih with ih | ⟨-, hs'⟩
        · exact Or.inl (tr_TopS_step ih hm hs)
        · have := tr_Step_lt hs'; have := hS h' hm; omega
    | @andStep h' f c' _ hm ht hg hf hc2 hfh hch hok ih =>
      have hs : tr_Step D ok h' c' := Or.inr ⟨ht, f, hg, hf, hc2, hfh, hch, hok⟩
      rcases Finset.mem_insert.1 hm with rfl | hm
      · rcases ih with ih | ⟨ih, -⟩ <;> exact Or.inr ⟨ih, hs⟩
      · rcases ih with ih | ⟨-, hs'⟩
        · exact Or.inl (tr_TopS_step ih hm hs)
        · have := tr_Step_lt hs'; have := hS h' hm; omega
  · rintro (hT | ⟨hT, hs⟩)
    · exact tr_TopS_mono (Finset.subset_insert h S) hT
    · exact tr_TopS_step (tr_TopS_mono (Finset.subset_insert h S) hT) (Finset.mem_insert_self h S) hs

theorem tr_TopS_empty {D : Dag N} {ok : ℕ → Prop} {c : ℕ} :
    tr_TopS D ∅ ok c ↔ c = D.out := by
  constructor
  · intro h
    induction h with
    | root => rfl
    | orStep _ hm => simp at hm
    | andStep _ hm => simp at hm
  · rintro rfl; exact tr_TopS.root

theorem tr_TopS_all {D : Dag N} {ok : ℕ → Prop} {c : ℕ} :
    tr_TopS D (D.Tor ∪ D.Tandf) ok c ↔ D.Top ok c := by
  constructor
  · intro h
    induction h with
    | root => exact Dag.Top.root
    | orStep _ _ ht hk hd ih => exact Dag.Top.orStep ih ht hk hd
    | andStep _ _ ht hg hf hc2 hfh hch hok ih => exact Dag.Top.andStep ih ht hg hf hc2 hfh hch hok
  · intro h
    induction h with
    | root => exact tr_TopS.root
    | orStep _ ht hk hd ih => exact tr_TopS.orStep ih (Finset.mem_union_left _ ht) ht hk hd
    | andStep _ ht hg hf hc2 hfh hch hok ih =>
      exact tr_TopS.andStep ih (Finset.mem_union_right _ ht) ht hg hf hc2 hfh hch hok

/-! ### Processing one sender -/

/-- Process the sender `h`: an OR of T sends what it carries to each child of degree at least
one; an AND of T with label `f` sends what it carries AND `f` to its other child. -/
def tr_proc (D : Dag N) (st : List G × (ℕ → tr_W)) (h : ℕ) : List G × (ℕ → tr_W) :=
  match D.gateAt h with
  | some (.or a b) =>
      tr_upd N (tr_upd N st a (if 1 ≤ D.deg a then st.2 h else .absent)) b
        (if 1 ≤ D.deg b then st.2 h else .absent)
  | some (.and a b) =>
      if D.deg a = 0 then
        tr_upd N ((tr_msgAnd N st.1 (st.2 h) a).1, st.2) b (tr_msgAnd N st.1 (st.2 h) a).2
      else
        tr_upd N ((tr_msgAnd N st.1 (st.2 h) b).1, st.2) a (tr_msgAnd N st.1 (st.2 h) b).2
  | _ => st

/-- The invariant after the senders of `S`. -/
def tr_Inv (D : Dag N) (st : List G × (ℕ → tr_W)) (S : Finset ℕ) : Prop :=
  tr_NewOK D st.1 ∧ st.1.length ≤ D.size + 2 * S.card ∧
    ∀ c, tr_Ok D st.1 (st.2 c) (fun x => tr_TopS D S (fun f => D.val x f = true) c)
      (tr_TopS D S (fun _ => True) c)

theorem tr_label_good {D : Dag N} {h f : ℕ} (hh : h ∈ D.cone) (hk : D.Kid h f)
    (hf : D.deg f = 0) : f < N ∨ f ∈ D.X := by
  by_cases hfN : f < N + N
  · left
    by_contra hc
    rw [Dag.deg, if_pos hfN, if_pos (by omega)] at hf
    exact one_ne_zero hf
  · right
    exact Finset.mem_filter.2 ⟨Api.api_coneOf_down D {D.out} h hh f hk (by omega), hf⟩

theorem tr_step_or {D : Dag N} {ok : ℕ → Prop} {h a b c : ℕ}
    (hg : D.gateAt h = some (.or a b)) (ha : a < h) (hb : b < h) (ht : h ∈ D.Tor) :
    tr_Step D ok h c ↔ ((c = a ∨ c = b) ∧ 1 ≤ D.deg c) := by
  constructor
  · rintro (⟨-, ⟨g, hg', hc, -⟩, hd⟩ | ⟨-, f, hg', -⟩)
    · rw [hg] at hg'; cases hg'
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc
      exact ⟨hc, hd⟩
    · rcases hg' with hg' | hg' <;> rw [hg] at hg' <;> cases hg'
  · rintro ⟨hc, hd⟩
    left
    refine ⟨ht, ⟨_, hg, ?_, ?_⟩, hd⟩
    · simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false]; exact hc
    · rcases hc with rfl | rfl <;> assumption

theorem tr_step_and {D : Dag N} {ok : ℕ → Prop} {h f0 c0 c : ℕ}
    (hg : D.gateAt h = some (.and f0 c0) ∨ D.gateAt h = some (.and c0 f0))
    (hf : D.deg f0 = 0) (hc2 : D.deg c0 = 2) (hfh : f0 < h) (hch : c0 < h)
    (ht : h ∈ D.Tandf) : tr_Step D ok h c ↔ (c = c0 ∧ ok f0) := by
  classical
  constructor
  · rintro (⟨ht', -⟩ | ⟨-, f, hg', hf', hc', -, -, hok⟩)
    · obtain ⟨-, a, b, hg'⟩ := Finset.mem_filter.1 ht'
      rcases hg with hg | hg <;> rw [hg] at hg' <;> cases hg'
    · rcases hg with hg | hg <;> rcases hg' with hg' | hg' <;> rw [hg] at hg' <;> cases hg' <;>
        first | exact ⟨rfl, hok⟩ | omega
  · rintro ⟨rfl, hok⟩
    exact Or.inr ⟨ht, f0, hg, hf, hc2, hfh, hch, hok⟩

theorem tr_proc_ok {D : Dag N} (hwf : D.WF) {st : List G × (ℕ → tr_W)} {S : Finset ℕ}
    {h : ℕ} (hI : tr_Inv D st S) (hS : ∀ s ∈ S, h < s) (hh : h ∈ D.Tor ∪ D.Tandf) :
    tr_Inv D (tr_proc D st h) (insert h S) := by
  classical
  obtain ⟨gs, w⟩ := st
  obtain ⟨hN, hlen, hw⟩ := hI
  dsimp only at hN hlen hw
  have hhS : h ∉ S := fun hm => lt_irrefl h (hS h hm)
  have hcard : (insert h S).card = S.card + 1 := Finset.card_insert_of_notMem hhS
  have hD := tr_NewOK_size hN
  rcases Finset.mem_union.1 hh with ht | ht
  · obtain ⟨hT, a, b, hg⟩ := Finset.mem_filter.1 ht
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    have hm : ∀ a', tr_Ok D gs (if 1 ≤ D.deg a' then w h else .absent)
        (fun x => 1 ≤ D.deg a' ∧ tr_TopS D S (fun f => D.val x f = true) h)
        (1 ≤ D.deg a' ∧ tr_TopS D S (fun _ => True) h) := by
      intro a'
      by_cases hda : 1 ≤ D.deg a'
      · rw [if_pos hda]; exact tr_Ok_congr (hw h) (fun x => by simp [hda]) (by simp [hda])
      · rw [if_neg hda]; exact ⟨fun h' => hda h'.1, fun x h' => hda h'.1⟩
    unfold tr_proc
    rw [hg]
    dsimp only
    obtain ⟨hN1, hp1, hl1, hw1⟩ := tr_upd_ok hN hw (hm a) a
    have hmb := tr_Ok_lift (hm b) hp1 hD
    generalize tr_upd N (gs, w) a (if 1 ≤ D.deg a then w h else .absent) = st1
      at hN1 hp1 hl1 hw1 hmb ⊢
    obtain ⟨g1, w1⟩ := st1
    dsimp only at hN1 hp1 hl1 hw1 hmb ⊢
    obtain ⟨hN2, hp2, hl2, hw2⟩ := tr_upd_ok hN1 hw1 hmb b
    refine ⟨hN2, ?_, fun c => tr_Ok_congr (hw2 c) ?_ ?_⟩
    · rw [hcard]; omega
    · intro x
      beta_reduce
      rw [tr_TopS_insert hS, tr_step_or hg ha hb ht]
      constructor
      · rintro ((h1 | ⟨rfl, h2, h3⟩) | ⟨rfl, h2, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨h3, Or.inl rfl, h2⟩
        · exact Or.inr ⟨h3, Or.inr rfl, h2⟩
      · rintro (h1 | ⟨h3, (rfl | rfl), h2⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr ⟨rfl, h2, h3⟩)
        · exact Or.inr ⟨rfl, h2, h3⟩
    · rw [tr_TopS_insert hS, tr_step_or hg ha hb ht]
      constructor
      · rintro ((h1 | ⟨rfl, h2, h3⟩) | ⟨rfl, h2, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨h3, Or.inl rfl, h2⟩
        · exact Or.inr ⟨h3, Or.inr rfl, h2⟩
      · rintro (h1 | ⟨h3, (rfl | rfl), h2⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr ⟨rfl, h2, h3⟩)
        · exact Or.inr ⟨rfl, h2, h3⟩
  · obtain ⟨hT, a, b, hg, hf⟩ := Finset.mem_filter.1 ht
    have ha := hwf _ _ hg a (by simp [G.kids])
    have hb := hwf _ _ hg b (by simp [G.kids])
    have hT' := Finset.mem_filter.1 hT
    have hdeg := tr_deg_and hg ha hb
    unfold tr_proc
    rw [hg]
    dsimp only
    by_cases ha0 : D.deg a = 0
    · rw [if_pos ha0]
      have hlab := tr_label_good hT'.1 (tr_kid_of hg (by simp [G.kids]) ha) ha0
      obtain ⟨hN1, hp1, hl1, hm1⟩ := tr_msgAnd_ok hN (hw h) hlab
      obtain ⟨hN2, hp2, hl2, hw2⟩ :=
        tr_upd_ok hN1 (fun c => tr_Ok_lift (hw c) hp1 hD) hm1 b
      have hst := tr_step_and (ok := fun _ => True) (c := 0) (Or.inl hg) ha0 (by omega) ha hb ht
      refine ⟨hN2, ?_, fun c => tr_Ok_congr (hw2 c) ?_ ?_⟩
      · rw [hcard]; omega
      · intro x
        beta_reduce
        rw [tr_TopS_insert hS, tr_step_and (Or.inl hg) ha0 (by omega) ha hb ht]
        constructor
        · rintro (h1 | ⟨rfl, h2, h3⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨h2, rfl, h3⟩
        · rintro (h1 | ⟨h2, rfl, h3⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨rfl, h2, h3⟩
      · rw [tr_TopS_insert hS, tr_step_and (Or.inl hg) ha0 (by omega) ha hb ht]
        constructor
        · rintro (h1 | ⟨rfl, h2⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨h2, rfl, trivial⟩
        · rintro (h1 | ⟨h2, rfl, -⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨rfl, h2⟩
    · rw [if_neg ha0]
      have hb0 : D.deg b = 0 := by omega
      have hlab := tr_label_good hT'.1 (tr_kid_of hg (by simp [G.kids]) hb) hb0
      obtain ⟨hN1, hp1, hl1, hm1⟩ := tr_msgAnd_ok hN (hw h) hlab
      obtain ⟨hN2, hp2, hl2, hw2⟩ :=
        tr_upd_ok hN1 (fun c => tr_Ok_lift (hw c) hp1 hD) hm1 a
      refine ⟨hN2, ?_, fun c => tr_Ok_congr (hw2 c) ?_ ?_⟩
      · rw [hcard]; omega
      · intro x
        beta_reduce
        rw [tr_TopS_insert hS, tr_step_and (Or.inr hg) hb0 (by omega) hb ha ht]
        constructor
        · rintro (h1 | ⟨rfl, h2, h3⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨h2, rfl, h3⟩
        · rintro (h1 | ⟨h2, rfl, h3⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨rfl, h2, h3⟩
      · rw [tr_TopS_insert hS, tr_step_and (Or.inr hg) hb0 (by omega) hb ha ht]
        constructor
        · rintro (h1 | ⟨rfl, h2⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨h2, rfl, trivial⟩
        · rintro (h1 | ⟨h2, rfl, -⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨rfl, h2⟩

/-! ### The whole pass -/

theorem tr_fold_ok {D : Dag N} (hwf : D.WF) : ∀ (L : List ℕ) (st : List G × (ℕ → tr_W))
    (S : Finset ℕ), L.Pairwise (· > ·) → (∀ h ∈ L, h ∈ D.Tor ∪ D.Tandf) →
    (∀ h ∈ L, ∀ s ∈ S, h < s) → tr_Inv D st S →
    tr_Inv D (L.foldl (tr_proc D) st) (S ∪ L.toFinset) := by
  intro L
  induction L with
  | nil => intro st S _ _ _ hI; simpa using hI
  | cons h t ih =>
    intro st S hp hm hlt hI
    rw [List.pairwise_cons] at hp
    rw [List.foldl_cons, List.toFinset_cons, Finset.union_insert, ← Finset.insert_union]
    apply ih _ _ hp.2 (fun h' h'' => hm h' (List.mem_cons_of_mem _ h''))
    · intro h' hh' s hs
      rcases Finset.mem_insert.1 hs with rfl | hs
      · exact hp.1 h' hh'
      · exact hlt h' (List.mem_cons_of_mem _ hh') s hs
    · exact tr_proc_ok hwf hI (hlt h (by simp)) (hm h (by simp))

theorem tr_wf {D : Dag N} (hwf : D.WF) {gs : List G} (hN : tr_NewOK D gs) (o : ℕ) :
    (⟨gs, o⟩ : Dag N).WF := by
  intro i g hg c hc
  obtain ⟨hi, hg'⟩ := Api.gateAt_some hg
  dsimp only at hg'
  by_cases hj : i - (N + N) < D.size
  · have e : (⟨gs, o⟩ : Dag N).gateAt i = (⟨D.gates, D.out⟩ : Dag N).gateAt i :=
      tr_gateAt_prefix hN.1 o D.out (by unfold Dag.size at hj; omega)
    rw [e] at hg
    exact hwf i g hg c hc
  · obtain ⟨u, v, hgv, hu, hv⟩ := hN.2 _ g (by omega) hg'
    have hu' := tr_Good_lt hu (by omega)
    have hv' := tr_Good_lt hv (by omega)
    rcases hgv with rfl | rfl <;>
      simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hc <;>
      rcases hc with rfl | rfl <;> omega

theorem tr_good_final {D : Dag N} {gs : List G} (hN : tr_NewOK D gs) (o : ℕ) :
    ∀ n, tr_Good D gs.length n → (⟨gs, o⟩ : Dag N).deg n = 0 ∧
      ∀ m, (⟨gs, o⟩ : Dag N).Kid n m → tr_Good D gs.length m := by
  have hD := tr_NewOK_size hN
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases hn with hn | hn | ⟨hn1, hn2⟩
  · refine ⟨?_, ?_⟩
    · rw [Dag.deg, if_pos (by omega), if_neg (by omega)]
    · rintro m ⟨g, hg, -, -⟩
      have := (Api.gateAt_some hg).1
      omega
  · have hlt := tr_X_lt hn
    have hX := Finset.mem_filter.1 hn
    have hsz : n < N + N + D.gates.length := hlt.2
    refine ⟨?_, ?_⟩
    · rw [tr_deg_prefix hN.1 D.out o n hsz]
      exact hX.2
    · rintro m ⟨g, hg, hmg, hmn⟩
      rw [tr_gateAt_prefix hN.1 D.out o hsz] at hg
      have hk : D.Kid n m := ⟨g, hg, hmg, hmn⟩
      have hd0 : D.deg m = 0 := by have := Api.deg_kid hk; omega
      rcases tr_label_good hX.1 hk hd0 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · cases hgs : gs[n - (N + N)]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at hgs
      omega
    | some g =>
      obtain ⟨u, v, hgv, hu, hv⟩ := hN.2 _ g (by omega) hgs
      have hgate : (⟨gs, o⟩ : Dag N).gateAt n = some g := by
        unfold Dag.gateAt
        rw [if_pos (by omega)]
        exact hgs
      have hdj : D.size ≤ n - (N + N) := by omega
      have hun : u < n := by have := tr_Good_lt hu hdj; omega
      have hvn : v < n := by have := tr_Good_lt hv hdj; omega
      have hu2 := tr_Good_mono hu (by omega : n - (N + N) ≤ gs.length)
      have hv2 := tr_Good_mono hv (by omega : n - (N + N) ≤ gs.length)
      refine ⟨?_, ?_⟩
      · rcases hgv with rfl | rfl
        · rw [tr_deg_and hgate hun hvn, (ih u hun hu2).1, (ih v hvn hv2).1]
        · rw [tr_deg_or hgate hun hvn, (ih u hun hu2).1, (ih v hvn hv2).1]
          rfl
      · rintro m ⟨g', hg', hmg, -⟩
        rw [hgate] at hg'
        cases hg'
        rcases hgv with rfl | rfl <;>
          simp only [G.kids, List.mem_cons, List.not_mem_nil, or_false] at hmg <;>
          rcases hmg with rfl | rfl <;> assumption

theorem tr_cone_final {D : Dag N} {gs : List G} (hN : tr_NewOK D gs) (o : ℕ) {n : ℕ}
    (hn : tr_Good D gs.length n) :
    (⟨gs, o⟩ : Dag N).coneOf {n} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + gs.length) := by
  classical
  intro m hm
  unfold Dag.coneOf at hm
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at hm
  obtain ⟨-, hm1, r, rfl, hr⟩ := hm
  have hg : tr_Good D gs.length m := by
    clear hm1
    induction hr with
    | refl => exact hn
    | tail _ hk ih => exact (tr_good_final hN o _ ih).2 _ hk
  rcases hg with h | h | h
  · omega
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_Ico.2 h)

/-- D2-15 (iii). The contexts by at most `2 |T_or| + 2 |T_andf|` appended x-only gates reading
only X and the new gates (a constant context `1` needs no gate). -/
theorem card15c_contexts (D : Dag N) (hwf : D.WF) (hd : D.deg D.out ≤ 2) :
    ∃ D' : Dag N, D.gates <+: D'.gates ∧ D'.WF ∧
      D'.size ≤ D.size + 2 * D.Tor.card + 2 * D.Tandf.card ∧
      ∀ b, D.IsItem b → (∀ x, D.ctx b x = true) ∨
        ∃ i, D'.deg i = 0 ∧ (∀ x, D'.val x i = D.ctx b x) ∧
          D'.coneOf {i} ⊆ D.X ∪ Finset.Ico (N + N + D.size) (N + N + D'.size) := by
  classical
  have hinit : tr_Inv D (D.gates, fun c => if c = D.out then tr_W.const else tr_W.absent) ∅ := by
    refine ⟨⟨List.prefix_refl _, fun j g hj hg => ?_⟩, by simp [Dag.size], fun c => ?_⟩
    · have : D.gates[j]? = none :=
        List.getElem?_eq_none_iff.2 (by unfold Dag.size at hj; omega)
      rw [this] at hg
      cases hg
    · dsimp only
      by_cases hc : c = D.out
      · rw [if_pos hc]
        subst hc
        exact fun x => tr_TopS.root
      · rw [if_neg hc]
        exact ⟨fun h => hc (tr_TopS_empty.1 h), fun x h => hc (tr_TopS_empty.1 h)⟩
  have hpw : ((D.Tor ∪ D.Tandf).sort (· ≥ ·)).Pairwise (· > ·) := by
    have h1 := Finset.pairwise_sort (D.Tor ∪ D.Tandf) (· ≥ ·)
    have h2 := Finset.sort_nodup (D.Tor ∪ D.Tandf) (· ≥ ·)
    exact (h1.and h2).imp (fun h => lt_of_le_of_ne h.1 (Ne.symm h.2))
  have hfin := tr_fold_ok hwf ((D.Tor ∪ D.Tandf).sort (· ≥ ·)) _ ∅ hpw
    (fun h hh => (Finset.mem_sort _).1 hh) (by simp) hinit
  rw [Finset.empty_union, Finset.sort_toFinset] at hfin
  generalize List.foldl (tr_proc D) _ _ = st at hfin
  obtain ⟨hN, hlen, hw⟩ := hfin
  refine ⟨⟨st.1, D.out⟩, hN.1, tr_wf hwf hN D.out, ?_, fun b hb => ?_⟩
  · have := Finset.card_union_le D.Tor D.Tandf
    show st.1.length ≤ _
    omega
  · have hwb := tr_Ok_congr (hw b) (fun x => tr_TopS_all) tr_TopS_all
    generalize st.2 b = m at hwb
    cases m with
    | absent => exact absurd hb.1 hwb.1
    | const =>
      left
      intro x
      unfold Dag.ctx
      exact decide_eq_true (hwb x)
    | wire n =>
      right
      obtain ⟨hg, hv⟩ := hwb
      refine ⟨n, (tr_good_final hN D.out n hg).1, fun x => ?_, tr_cone_final hN D.out hg⟩
      unfold Dag.ctx
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact hv x

end PEqualNP.MetaComplexity.Deg2
