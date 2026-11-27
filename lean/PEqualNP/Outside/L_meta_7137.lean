import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7137

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

abbrev Vertex := Fin 26
abbrev Row := Vertex → Bool
abbrev Port := ℕ × Bool
abbrev Wires := ℕ → Row → Bool
abbrev Pins := ℕ → Bool → ℕ

def rel (u v : Vertex) : Prop :=
  u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + 13 - (v.val - 13)) % 13 ∈ ({0, 1, 3, 9} : Finset ℕ)

def relDec (u v : Vertex) : Decidable (rel u v) := by
  unfold rel
  infer_instance

def edge (u v : Vertex) : Bool :=
  @decide (rel u v ∨ rel v u) (@instDecidableOr _ _ (relDec u v) (relDec v u))

lemma edge_eq (u v : Vertex) : edge u v = true ↔ (SimpleGraph.fromRel rel).Adj u v := by
  rw [edge]
  simp only [decide_eq_true_eq]
  change (rel u v ∨ rel v u) ↔ u ≠ v ∧ (rel u v ∨ rel v u)
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  rintro rfl
  rcases h with h | h <;> exact Nat.not_le_of_lt h.1 h.2.1

lemma edge_diag : ∀ u : Vertex, edge u u = false := by decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma privateNeighbor : ∀ u v : Vertex, u ≠ v →
    ∃ w : Vertex, w ≠ u ∧ w ≠ v ∧ edge u w = true ∧ edge v w = false := by
  decide +kernel

def pair (u v : Vertex) : Row := fun i => decide (i = u ∨ i = v)

def bin (k a b : Bool) : Bool := if k then a && b else a || b

lemma bin_mono {k a b c d : Bool} (ha : a ≤ c) (hb : b ≤ d) :
    bin k a b ≤ bin k c d := by
  cases k <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all [bin]

def wireSet (G : Finset ℕ) : Finset ℕ := Finset.range 28 ∪ G

def Valid (G : Finset ℕ) (A : Pins) (K : ℕ → Bool) (V : Wires) : Prop :=
  (∀ i ∈ G, 28 ≤ i ∧ ∀ z, A i z ∈ wireSet G ∧ A i z < i) ∧
  (∀ x i, V i.val x = x i) ∧
  (∀ x, V 26 x = false) ∧ (∀ x, V 27 x = true) ∧
  (∀ x i, i ∈ G → V i x = bin (K i) (V (A i false) x) (V (A i true) x))

def Correct (V : Wires) (o : ℕ) : Prop :=
  ∀ u v, V o (pair u v) = edge u v

def Realizes (s : ℕ) : Prop :=
  ∃ (G : Finset ℕ) (A : Pins) (K : ℕ → Bool) (V : Wires) (o : ℕ),
    G.card ≤ s ∧ Valid G A K V ∧ o ∈ wireSet G ∧ Correct V o

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x

lemma run_append (as bs : List Gate) (x : List Bool) :
    run (as ++ bs) x = run bs (run as x) := List.foldl_append

lemma run_prefix (gs : List Gate) (x : List Bool) :
    ∃ ys, run gs x = x ++ ys ∧ ys.length = gs.length := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    let bit := g.op.eval (g.inputs.map fun j => x.getD j false)
    obtain ⟨ys, hy, hl⟩ := ih (x ++ [bit])
    refine ⟨bit :: ys, ?_, by simp [hl]⟩
    change run gs (x ++ [bit]) = _
    simpa only [List.append_assoc, List.singleton_append] using hy

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  obtain ⟨ys, h, hl⟩ := run_prefix gs x
  simp [h, hl]

lemma run_get (gs : List Gate) (x : List Bool) {j : ℕ} (h : j < x.length) :
    (run gs x).getD j false = x.getD j false := by
  obtain ⟨ys, hy, _⟩ := run_prefix gs x
  rw [hy, List.getD_append _ _ _ _ h]

lemma run_gate (gs : List Gate) (x : List Bool) (k : ℕ) (hk : k < gs.length) :
    (run gs x).getD (x.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < x.length + k
        then (run gs x).getD j false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k+1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  let y := run (gs.take k) x
  have hy : y.length = x.length + k := by simp [y, run_length, Nat.min_eq_left hk.le]
  have hr : run gs x = run (gs.drop (k+1))
      (y ++ [gs[k].op.eval (gs[k].inputs.map fun j => y.getD j false)]) := by
    conv_lhs => rw [hsplit]
    rw [run_append]
    rfl
  conv_lhs => rw [hr, run_get _ _ (by simp [hy]), ← hy]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
  change gs[k].op.eval _ = gs[k].op.eval _
  congr 1
  apply List.map_congr_left
  intro j _
  split_ifs with hj
  · symm
    rw [hr]
    have hz : j < (y ++ [gs[k].op.eval (gs[k].inputs.map fun j => y.getD j false)]).length := by
      simp only [List.length_append, List.length_singleton, hy]
      omega
    rw [run_get _ _ hz, List.getD_append _ _ _ _ (by omega)]
  · exact List.getD_eq_default _ _ (by omega)

def translate (limit j : ℕ) : ℕ :=
  if j < 26 then j else if j < limit then j + 2 else 26

-- Reserve two wire identifiers for constants, and include the final OR in the gate budget.
lemma realize (C : Circuit) (hm : Monotone2 C) (a b : ℕ)
    (h : ∀ u v : Vertex,
      ((C.wires (List.ofFn (pair u v))).getD a false ||
        (C.wires (List.ofFn (pair u v))).getD b false) = edge u v) :
    Realizes (C.size + 1) := by
  classical
  let gs := C.gates ++ [⟨GateOp.or, [a,b]⟩]
  have mono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · simpa using hm g hg
    · simp at hg
      subst g
      simp
  let G := (Finset.range (28 + gs.length)).filter (28 ≤ ·)
  let V : Wires := fun j x => if j < 26 then (List.ofFn x).getD j false
    else if j < 28 then j == 27 else (run gs (List.ofFn x)).getD (j-2) false
  let gate (i : ℕ) := gs[i-28]?.getD ⟨GateOp.or, []⟩
  let K := fun i => decide ((gate i).op = GateOp.and)
  let A : Pins := fun i z =>
    if (gate i).inputs.isEmpty then (if K i then 27 else 26)
    else translate (i-2) ((gate i).inputs.getD (if z ∧ (gate i).inputs.length = 2 then 1 else 0) 0)
  have memG (i : ℕ) : i ∈ G ↔ 28 ≤ i ∧ i < 28 + gs.length := by
    simp [G, and_comm]
  have memW (i : ℕ) (hi : i < 28 + gs.length) : i ∈ wireSet G := by
    simp only [wireSet, Finset.mem_union, Finset.mem_range, memG]
    omega
  have read (x : Row) (i j : ℕ) (hi : 28 ≤ i) :
      V (translate (i-2) j) x =
        if j < i-2 then (run gs (List.ofFn x)).getD j false else false := by
    by_cases hj : j < 26
    · simp only [translate, ite_eq_left hj, V, ite_eq_left (show j < i-2 by omega)]
      symm
      exact run_get _ _ (by simpa)
    · by_cases hl : j < i-2
      · simp [translate, V, hj, hl, show ¬ j+2 < 26 by omega, show ¬ j+2 < 28 by omega]
      · simp [translate, V, hj, hl]
  have cardG : G.card = gs.length := by
    have he : Finset.range (28+gs.length) = Finset.range 28 ∪ G := by
      ext i
      simp only [Finset.mem_range, Finset.mem_union, memG]
      omega
    have hd : Disjoint (Finset.range 28) G := Finset.disjoint_left.mpr (by
      intro i h1 h2
      exact (Nat.not_lt_of_ge ((memG i).mp h2).1) (Finset.mem_range.mp h1))
    have := congrArg Finset.card he
    rw [Finset.card_union_of_disjoint hd, Finset.card_range, Finset.card_range] at this
    omega
  have glen : gs.length = C.gates.length + 1 := by simp [gs]
  let o := 28 + C.gates.length
  refine ⟨G,A,K,V,o,by simp [cardG, glen, Circuit.size], ?_, memW _ (by dsimp [o]; omega), ?_⟩
  refine ⟨?_, ?_, by intro x; rfl, by intro x; rfl, ?_⟩
  · intro i hi
    obtain ⟨hi, hil⟩ := (memG i).mp hi
    refine ⟨hi, fun z => ?_⟩
    have raw (j : ℕ) : translate (i-2) j < i := by
      unfold translate
      split_ifs <;> omega
    have hb : A i z < i := by
      dsimp [A]
      split_ifs <;> first | omega | exact raw _
    exact ⟨memW _ (by omega), hb⟩
  · intro x i
    have hi := i.isLt
    rw [show V i.val x = (List.ofFn x).getD i.val false from ite_eq_left hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp), List.getElem_ofFn]
    rfl
  · intro x i hi
    obtain ⟨hi, hil⟩ := (memG i).mp hi
    have hj : i-28 < gs.length := by omega
    have he : gate i = gs[i-28] := by simp [gate, List.getElem?_eq_getElem hj]
    have H := run_gate gs (List.ofFn x) (i-28) hj
    simp only [List.length_ofFn, show 26 + (i-28) = i-2 by omega] at H
    have hop := mono _ (List.getElem_mem hj)
    rw [← he] at H hop
    have hV : V i x = (run gs (List.ofFn x)).getD (i-2) false := by
      simp only [V, ite_eq_right (show ¬ i < 26 by omega), ite_eq_right (show ¬ i < 28 by omega)]
    rw [hV]
    rw [H]
    simp only [← read x i _ hi]
    rcases hop with ⟨hop, hl⟩
    rcases hls : (gate i).inputs with _ | ⟨j, _ | ⟨k, _ | ⟨l, ls⟩⟩⟩
    · rcases hop with hop | hop <;> simp [A, K, hls, hop, GateOp.eval, bin, V]
    · rcases hop with hop | hop <;> simp [A, K, hls, hop, GateOp.eval, bin]
    · rcases hop with hop | hop <;>
        simp [A, K, hls, hop, GateOp.eval, bin]
    · simp [hls] at hl
  · intro u v
    have he : run C.gates (List.ofFn (pair u v)) = C.wires (List.ofFn (pair u v)) := rfl
    simp only [V, o, ite_eq_right (show ¬ 28 + C.gates.length < 26 by omega),
      ite_eq_right (show ¬ 28 + C.gates.length < 28 by omega),
      show 28 + C.gates.length - 2 = 26 + C.gates.length by omega, gs, run_append]
    change (run C.gates (List.ofFn (pair u v)) ++
      [GateOp.or.eval [ (run C.gates (List.ofFn (pair u v))).getD a false,
        (run C.gates (List.ofFn (pair u v))).getD b false]]).getD
          (26+C.gates.length) false = edge u v
    have hlen : (run C.gates (List.ofFn (pair u v))).length = 26+C.gates.length := by
      simp [run_length]
    rw [← hlen, List.getD_append_right _ _ _ _ (by omega), Nat.sub_self, he]
    simpa [GateOp.eval] using h u v

def reroute (d j w : ℕ) : ℕ := if w = d then j else w

lemma erase_gate {G A K V o} (h : Valid G A K V) (ho : o ∈ wireSet G)
    {d j : ℕ} (hj : j ∈ wireSet G) (hjd : j < d)
    (hval : (o = d ∨ ∃ t ∈ G, ∃ z, A t z = d) → ∀ x, V j x = V d x) :
    ∃ (A' : Pins) (o' : ℕ), Valid (G.erase d) A' K V ∧ o' ∈ wireSet (G.erase d) ∧
      ∀ x, V o' x = V o x := by
  have remain {w : ℕ} (hw : w ∈ wireSet G) (hne : w ≠ d) : w ∈ wireSet (G.erase d) := by
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union_left _ hw
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hw⟩)
  refine ⟨fun t z => reroute d j (A t z), reroute d j o, ?_, ?_, ?_⟩
  · refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    · intro t ht
      have ht' := (Finset.mem_erase.mp ht).2
      refine ⟨(h.1 t ht').1, fun z => ?_⟩
      obtain ⟨hw, hl⟩ := (h.1 t ht').2 z
      change reroute d j (A t z) ∈ wireSet (G.erase d) ∧ reroute d j (A t z) < t
      unfold reroute
      split_ifs with he
      · exact ⟨remain hj hjd.ne, by omega⟩
      · exact ⟨remain hw he, hl⟩
    · intro x t ht
      have ht' := (Finset.mem_erase.mp ht).2
      have read (z : Bool) : V (reroute d j (A t z)) x = V (A t z) x := by
        unfold reroute
        split_ifs with he
        · rw [he]
          exact hval (Or.inr ⟨t, ht', z, he⟩) x
        · rfl
      rw [read, read]
      exact h.2.2.2.2 x t ht'
  · unfold reroute
    split_ifs with he
    · exact remain hj hjd.ne
    · exact remain ho he
  · intro x
    unfold reroute
    split_ifs with he
    · rw [he]
      exact hval (Or.inl he) x
    · rfl

def ports (G : Finset ℕ) : Finset Port := G ×ˢ Finset.univ

def uses (G : Finset ℕ) (A : Pins) (w : ℕ) : Finset Port :=
  (ports G).filter fun p => A p.1 p.2 = w

@[simp] lemma mem_uses {G A w} {p : Port} :
    p ∈ uses G A w ↔ p.1 ∈ G ∧ A p.1 p.2 = w := by
  simp [uses, ports]

def actual (G : Finset ℕ) : Finset ℕ := Finset.range 26 ∪ G

lemma used_or_output {G A K V o} (h : Valid G A K V)
    (ho : o ∈ wireSet G) (hc : Correct V o)
    (least : ∀ s < G.card, ¬ Realizes s) :
    (∀ w ∈ actual G, w ≠ o → (uses G A w).Nonempty) ∧
      (∀ t ∈ G, ∀ z, A t z ∈ actual G) ∧ o ∈ G := by
  classical
  have mem26 : 26 ∈ wireSet G := Finset.mem_union_left _ (by decide)
  have mem27 : 27 ∈ wireSet G := Finset.mem_union_left _ (by decide)
  have erase {d j : ℕ} (hd : d ∈ G) (hj : j ∈ wireSet G) (hjd : j < d)
      (he : (o = d ∨ ∃ t ∈ G, ∃ z, A t z = d) → ∀ x, V j x = V d x) : False := by
    obtain ⟨B, p, hB, hp, hv⟩ := erase_gate h ho hj hjd he
    apply least _ (Finset.card_erase_lt_of_mem hd)
    exact ⟨_, B, K, V, p, le_rfl, hB, hp, fun u v => (hv _).trans (hc u v)⟩
  have noConst (t : ℕ) (ht : t ∈ G) (z : Bool) : A t z ≠ 26 ∧ A t z ≠ 27 := by
    have bound := (h.1 t ht).1
    have contra (c : Bool) (he : A t z = if c then 27 else 26) : False := by
      let j := if K t = c then A t (!z) else A t z
      have hj : j ∈ wireSet G ∧ j < t := by
        unfold j
        split_ifs <;> exact (h.1 t ht).2 _
      apply erase ht hj.1 hj.2
      intro _ x
      have hv : V (A t z) x = c := by
        cases c
        · exact he.symm ▸ h.2.2.1 x
        · exact he.symm ▸ h.2.2.2.1 x
      rw [h.2.2.2.2 x t ht]
      cases z <;> cases c <;> cases hk : K t <;> simp_all [j, bin]
    exact ⟨contra false, contra true⟩
  have nz : (edge 0 13) = true := by decide
  have output : o ∈ G := by
    rcases Finset.mem_union.mp ho with ho' | hG
    · have hol := Finset.mem_range.mp ho'
      by_cases hl : o < 26
      · let i : Vertex := ⟨o, hl⟩
        have he := hc i i
        have hv := h.2.1 (pair i i) i
        change V o (pair i i) = _ at hv
        rw [hv, edge_diag] at he
        simp [pair] at he
      · rcases (show o = 26 ∨ o = 27 by omega) with rfl | rfl
        · have he := hc 0 13
          rw [h.2.2.1, nz] at he
          contradiction
        · have he := hc 0 0
          rw [h.2.2.2.1, edge_diag] at he
          contradiction
    · exact hG
  refine ⟨?_, ?_, output⟩
  · intro w hw hwo
    by_contra hn
    have nr (t : ℕ) (ht : t ∈ G) (z : Bool) : A t z ≠ w := by
      intro he
      exact hn ⟨(t,z), mem_uses.mpr ⟨ht,he⟩⟩
    rcases Finset.mem_union.mp hw with hraw | hwG
    · let u : Vertex := ⟨w, Finset.mem_range.mp hraw⟩
      obtain ⟨v,hvu,_,hev,_⟩ := privateNeighbor u (if u = 0 then 1 else 0) (by split_ifs <;> simp_all)
      have equal : ∀ w' ∈ wireSet G, w' ≠ w →
          V w' (pair u v) = V w' (pair v v) := by
        intro w'
        induction w' using Nat.strong_induction_on with
        | ind w' ih =>
          intro hm hne
          rcases Finset.mem_union.mp hm with hb | hg
          · have hb := Finset.mem_range.mp hb
            by_cases hlt : w' < 26
            · let i : Vertex := ⟨w',hlt⟩
              have hiu : i ≠ u := fun he => hne (congrArg Fin.val he)
              change V i.val _ = V i.val _
              rw [h.2.1, h.2.1]
              simp [pair,hiu]
            · rcases (show w' = 26 ∨ w' = 27 by omega) with rfl | rfl
              · rw [h.2.2.1, h.2.2.1]
              · rw [h.2.2.2.1, h.2.2.2.1]
          · rw [h.2.2.2.2 _ _ hg, h.2.2.2.2 _ _ hg]
            have step (z : Bool) := ih (A w' z) ((h.1 w' hg).2 z).2
              ((h.1 w' hg).2 z).1 (nr w' hg z)
            rw [step false, step true]
      have he := equal o ho hwo.symm
      rw [hc, hc, hev, edge_diag] at he
      contradiction
    · exact erase hwG mem26 (by have := (h.1 w hwG).1; omega) (by
        rintro (he | ⟨t, ht, z, he⟩)
        · exact (hwo he.symm).elim
        · exact (nr t ht z he).elim)
  · intro t ht z
    rcases Finset.mem_union.mp ((h.1 t ht).2 z).1 with hm | hm
    · have := Finset.mem_range.mp hm
      have := noConst t ht z
      exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    · exact Finset.mem_union_right _ hm

def Link (G : Finset ℕ) (A : Pins) (w t : ℕ) : Prop :=
  ∃ z, uses G A w = {(t,z)}

abbrev Path (G : Finset ℕ) (A : Pins) := ReflTransGen (Link G A)

lemma link_of {G A w} {p : Port} (hm : p ∈ uses G A w)
    (hc : (uses G A w).card = 1) : Link G A w p.1 := by
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hc
  have : p = q := by simpa [hq] using hm
  exact ⟨p.2, by rw [hq, ← this]⟩

lemma link_port {G A w t} (hl : Link G A w t) {p : Port} (hp : p ∈ uses G A w) :
    p.1 = t := by
  obtain ⟨z,hz⟩ := hl
  have he : p = (t,z) := by simpa [hz] using hp
  exact congrArg Prod.fst he

lemma link_lt {G A K V w t} (h : Valid G A K V) (hl : Link G A w t) : w < t := by
  obtain ⟨z,hz⟩ := hl
  have hm : (t,z) ∈ uses G A w := by simp [hz]
  obtain ⟨ht, hw⟩ := mem_uses.mp hm
  exact hw ▸ ((h.1 t ht).2 z).2

lemma path_le {G A K V w t} (h : Valid G A K V) (hp : Path G A w t) : w ≤ t := by
  induction hp with
  | refl => exact le_rfl
  | tail _ hl ih => exact ih.trans (link_lt h hl).le

lemma path_compare {G A w a b} (ha : Path G A w a) (hb : Path G A w b) :
    Path G A a b ∨ Path G A b a := by
  induction ha using ReflTransGen.head_induction_on with
  | refl => exact Or.inl hb
  | @head x y hl hp ih =>
    rcases hb.cases_head with rfl | ⟨z, hz, htail⟩
    · exact Or.inr (hp.head hl)
    · obtain ⟨q, hq⟩ := hz
      have hm : (z,q) ∈ uses G A x := by simp [hq]
      have he : z = y := link_port hl hm
      subst z
      exact ih htail

lemma through_reader {G A w t c} {z : Bool}
    (hp : (t,z) ∈ uses G A w) (hne : w ≠ c) (hw : Path G A w c) :
    Path G A t c := by
  rcases hw.cases_head with he | ⟨p, hp', ht⟩
  · exact (hne he).elim
  · have he : t = p := link_port hp' hp
    rwa [he]

lemma cut_mono {G A K V} (h : Valid G A K V) (x y : Row) (c : ℕ)
    (hin : ∀ i : Vertex, ¬ Path G A i.val c → x i ≤ y i)
    (hc : V c x ≤ V c y) :
    ∀ t ∈ wireSet G, (t = c ∨ ¬ Path G A t c) → V t x ≤ V t y := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht hs
    rcases hs with rfl | hn
    · exact hc
    · rcases Finset.mem_union.mp ht with hr | hg
      · have hr := Finset.mem_range.mp hr
        by_cases hb : t < 26
        · let i : Vertex := ⟨t,hb⟩
          change V i.val x ≤ V i.val y
          rw [h.2.1, h.2.1]
          exact hin i hn
        · rcases (show t = 26 ∨ t = 27 by omega) with rfl | rfl
          · rw [h.2.2.1, h.2.2.1]
          · rw [h.2.2.2.1, h.2.2.2.1]
      · rw [h.2.2.2.2 _ _ hg, h.2.2.2.2 _ _ hg]
        have next (z : Bool) : V (A t z) x ≤ V (A t z) y := by
          apply ih _ ((h.1 t hg).2 z).2 ((h.1 t hg).2 z).1
          by_cases he : A t z = c
          · exact Or.inl he
          · exact Or.inr fun hp => hn (through_reader (mem_uses.mpr ⟨hg,rfl⟩) he hp)
        exact bin_mono (next false) (next true)

lemma output_max {G A K V o} (h : Valid G A K V) (ho : o ∈ G) (hc : Correct V o)
    (least : ∀ s < G.card, ¬ Realizes s) :
    ∀ t ∈ G, t ≤ o := by
  classical
  intro t ht
  by_contra hn
  let H := G.filter (· ≤ o)
  have hH : H ⊂ G := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.filter_subset _ _, by
      intro he
      have htH : t ∈ H := he.symm ▸ ht
      exact hn ((Finset.mem_filter.mp htH).2)⟩
  apply least _ (Finset.card_lt_card hH)
  refine ⟨H,A,K,V,o,le_rfl,?_,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ho, le_rfl⟩),hc⟩
  refine ⟨?_,h.2.1,h.2.2.1,h.2.2.2.1,fun x j hj => h.2.2.2.2 x j (Finset.mem_filter.mp hj).1⟩
  intro j hj
  obtain ⟨hjG,hjo⟩ := Finset.mem_filter.mp hj
  refine ⟨(h.1 j hjG).1, fun z => ?_⟩
  obtain ⟨hw,hwj⟩ := (h.1 j hjG).2 z
  refine ⟨?_,hwj⟩
  rcases Finset.mem_union.mp hw with hw | hw
  · exact Finset.mem_union_left _ hw
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw,hwj.le.trans hjo⟩)

lemma pair_le_except {u v w i : Vertex} (hne : i ≠ u) :
    pair u w i ≤ pair v w i := by
  apply Bool.le_iff_imp.mpr
  intro h
  have hw := (of_decide_eq_true h).resolve_left hne
  exact decide_eq_true (Or.inr hw)

lemma cut_contra {G A K V o t} {u v w : Vertex}
    (h : Valid G A K V) (ho : o ∈ G) (hc : Correct V o) (ht : t ≤ o)
    (hp : Path G A u.val t) (hu : edge u w = true) (hv : edge v w = false)
    (hm : V t (pair u w) ≤ V t (pair v w)) : False := by
  have out := cut_mono h (pair u w) (pair v w) t
    (fun i hi => pair_le_except (fun he => hi (he ▸ hp))) hm o
    (Finset.mem_union_right _ ho) (by
      by_cases he : o = t
      · exact Or.inl he
      · exact Or.inr fun hp' => he (le_antisymm (path_le h hp') ht))
  rw [hc, hc, hu, hv] at out
  exact (by decide : ¬ true ≤ false) out

lemma gate_swapped {G A K V t} (h : Valid G A K V) (ht : t ∈ G) (z : Bool) (x : Row) :
    V t x = bin (K t) (V (A t z) x) (V (A t (!z)) x) := by
  rw [h.2.2.2.2 x t ht]
  cases z <;> simp [bin, Bool.and_comm, Bool.or_comm]

-- An input read once cannot share its reader with another raw input.
lemma sibling_gate {G A K V o t} {z : Bool} {u : Vertex}
    (h : Valid G A K V) (ho : o ∈ G) (hc : Correct V o)
    (hmax : ∀ j ∈ G, j ≤ o) (hactual : ∀ j ∈ G, ∀ d, A j d ∈ actual G)
    (hp : (t,z) ∈ uses G A u.val) (hone : (uses G A u.val).card = 1) :
    A t (!z) ∈ G := by
  have ⟨ht,hu⟩ := mem_uses.mp hp
  have hpath : Path G A u.val t := ReflTransGen.single (link_of hp hone)
  rcases Finset.mem_union.mp (hactual t ht (!z)) with hb | hb
  · exfalso
    let v : Vertex := ⟨A t (!z), Finset.mem_range.mp hb⟩
    have hne : u ≠ v := by
      intro he
      have hp' : (t,!z) ∈ uses G A u.val := mem_uses.mpr ⟨ht, congrArg Fin.val he.symm⟩
      have hsub : ({(t,z),(t,!z)} : Finset Port) ⊆ uses G A u.val := by
        intro p hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl
        · exact hp
        · exact hp'
      have hh := Finset.card_le_card hsub
      cases z <;> simp [hone] at hh
    obtain ⟨w,hwu,hwv,hew,hnw⟩ := privateNeighbor u v hne
    cases hk : K t
    · apply cut_contra h ho hc (hmax t ht) hpath hew hnw
      rw [gate_swapped h ht z _, gate_swapped h ht z _, hu, hk]
      change bin false (V u.val (pair u w)) (V v.val (pair u w)) ≤
        bin false (V u.val (pair v w)) (V v.val (pair v w))
      simp [bin, h.2.1, pair]
    · apply cut_contra h ho hc (hmax t ht) hpath hew (edge_diag w)
      rw [gate_swapped h ht z _, gate_swapped h ht z _, hu, hk]
      change bin true (V u.val (pair u w)) (V v.val (pair u w)) ≤
        bin true (V u.val (pair w w)) (V v.val (pair w w))
      simp [bin, h.2.1, pair, hne.symm, hwv.symm]
  · exact hb

-- The reader of a singly read vertex cannot lie on a unique path from another vertex.
lemma only_vertex_at_reader {G A K V o t} {z : Bool} {u v : Vertex}
    (h : Valid G A K V) (ho : o ∈ G) (hc : Correct V o)
    (hmax : ∀ j ∈ G, j ≤ o) (hm : (t,z) ∈ uses G A u.val)
    (hp : Path G A v.val t) : v = u := by
  by_contra hne
  have ⟨ht,hu⟩ := mem_uses.mp hm
  obtain ⟨w,hwv,hwu,hew,hnw⟩ := privateNeighbor v u hne
  cases hk : K t
  · apply cut_contra h ho hc (hmax t ht) hp hew hnw
    rw [gate_swapped h ht z _, gate_swapped h ht z _, hu, hk]
    simp [bin, h.2.1, pair]
  · apply cut_contra h ho hc (hmax t ht) hp hew (edge_diag w)
    rw [gate_swapped h ht z _, gate_swapped h ht z _, hu, hk]
    simp [bin, h.2.1, pair, Ne.symm hne, hwu.symm]

def PortStep (G : Finset ℕ) (A : Pins) (p q : Port) : Prop :=
  uses G A p.1 = {q}

abbrev Trail (G : Finset ℕ) (A : Pins) := ReflTransGen (PortStep G A)

lemma trail_path {G A p q} (hp : Trail G A p q) : Path G A p.1 q.1 := by
  induction hp with
  | refl => exact .refl
  | tail _ hl ih =>
    exact ih.tail ⟨_, hl⟩

lemma trail_same_gate {G A K V p q} (h : Valid G A K V)
    (hp : Trail G A p q) (he : p.1 = q.1) : p = q := by
  rcases hp.cases_head with he' | ⟨r, hr, hq⟩
  · exact he'
  · have hlt : p.1 < r.1 := link_lt h ⟨r.2,hr⟩
    have hle := path_le h (trail_path hq)
    omega

lemma trail_compare {G A p q r} (hq : Trail G A p q) (hr : Trail G A p r) :
    Trail G A q r ∨ Trail G A r q := by
  induction hq using ReflTransGen.head_induction_on with
  | refl => exact Or.inl hr
  | @head x y hxy hq ih =>
    rcases hr.cases_head with rfl | ⟨z,hxz,hr⟩
    · exact Or.inr (hq.head hxy)
    · have he : y = z := Finset.singleton_inj.mp (hxy.symm.trans hxz)
      subst z
      exact ih hr

lemma upstream_repeat {G A K V} (h : Valid G A K V)
    (hactual : ∀ j ∈ G, ∀ d, A j d ∈ actual G) :
    ∀ (p : Port), p.1 ∈ G → (∀ i : Vertex, ¬ Path G A i.val p.1) →
      ∃ q : Port, q.1 ∈ G ∧ 2 ≤ (uses G A (A q.1 q.2)).card ∧ Trail G A q p := by
  suffices ∀ t (z : Bool), t ∈ G → (∀ i : Vertex, ¬ Path G A i.val t) →
      ∃ q : Port, q.1 ∈ G ∧ 2 ≤ (uses G A (A q.1 q.2)).card ∧ Trail G A q (t,z) by
    rintro ⟨t,z⟩
    exact this t z
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro z ht hn
    let w := A t z
    have hm : (t,z) ∈ uses G A w := mem_uses.mpr ⟨ht,rfl⟩
    by_cases hr : 2 ≤ (uses G A w).card
    · exact ⟨(t,z),ht,hr,.refl⟩
    have hp := Finset.card_pos.mpr ⟨_,hm⟩
    have hone : (uses G A w).card = 1 := by omega
    obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hone
    have he : (t,z) = p := by simpa [hp] using hm
    have hh : uses G A w = {(t,z)} := by rw [hp,he]
    have hl : Link G A w t := ⟨z,hh⟩
    have hwG : w ∈ G := by
      rcases Finset.mem_union.mp (hactual t ht z) with hb | hb
      · exact (hn ⟨w,Finset.mem_range.mp hb⟩ (ReflTransGen.single hl)).elim
      · exact hb
    obtain ⟨q,hq,hqr,htrail⟩ := ih w (link_lt h hl) false hwG
      (fun i hip => hn i (hip.tail hl))
    exact ⟨q,hq,hqr,htrail.tail (show PortStep G A (w,false) (t,z) from hh)⟩

def uniqueVertices (G : Finset ℕ) (A : Pins) : Finset Vertex :=
  Finset.univ.filter fun u => (uses G A u.val).card = 1

def credits (G : Finset ℕ) (A : Pins) : Finset (Port × Bool) :=
  ((ports G) ×ˢ (Finset.univ : Finset Bool)).filter fun p =>
    2 ≤ (uses G A (A p.1.1 p.1.2)).card ∧ (p.2 = false ∨ 26 ≤ A p.1.1 p.1.2)

@[simp] lemma mem_credits {G A} {p : Port} {b : Bool} :
    (p,b) ∈ credits G A ↔
      p.1 ∈ G ∧ 2 ≤ (uses G A (A p.1 p.2)).card ∧ (b = false ∨ 26 ≤ A p.1 p.2) := by
  simp [credits, ports]

-- Count the repeated uses feeding each singly read vertex's reader through unique paths.
lemma two_credits {G A K V o} (h : Valid G A K V) (ho : o ∈ G) (hc : Correct V o)
    (hmax : ∀ j ∈ G, j ≤ o) (hactual : ∀ j ∈ G, ∀ d, A j d ∈ actual G) :
    2 * (uniqueVertices G A).card ≤ (credits G A).card := by
  classical
  let U := uniqueVertices G A
  have one (u : Vertex) (hu : u ∈ U) : (uses G A u.val).card = 1 :=
    (Finset.mem_filter.mp hu).2
  have existsReader (u : Vertex) (hu : u ∈ U) :
      ∃ p : Port, p ∈ uses G A u.val := Finset.card_pos.mp (by rw [one u hu]; decide)
  choose R hR using existsReader
  let C (u : U) := (credits G A).filter fun p => Path G A p.1.1 (R u.val u.property).1
  have enough (u : U) : 2 ≤ (C u).card := by
    let p := R u.val u.property
    have hm : p ∈ uses G A u.val.val := hR _ _
    have hone := one u.val u.property
    obtain ⟨ht, _⟩ := mem_uses.mp hm
    let b := A p.1 (!p.2)
    have hb : b ∈ G := sibling_gate h ho hc hmax hactual hm hone
    have hbt : b < p.1 := ((h.1 p.1 ht).2 (!p.2)).2
    have hx : (p.1,!p.2) ∈ uses G A b := mem_uses.mpr ⟨ht,rfl⟩
    have two (a d : Port × Bool) (ha : a ∈ C u) (hd : d ∈ C u) (hne : a ≠ d) :
        2 ≤ (C u).card := by
      have hs : ({a,d} : Finset (Port × Bool)) ⊆ C u := by
        intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl <;> assumption
      simpa [hne] using Finset.card_le_card hs
    by_cases hr : 2 ≤ (uses G A b).card
    · have c (k : Bool) : ((p.1,!p.2),k) ∈ C u := by
        apply Finset.mem_filter.mpr
        exact ⟨mem_credits.mpr ⟨ht,hr,Or.inr (show 26 ≤ b from (h.1 b hb).1.trans' (by decide))⟩,.refl⟩
      exact two _ _ (c false) (c true) (by simp)
    · have hpos := Finset.card_pos.mpr ⟨_,hx⟩
      have hl : Link G A b p.1 := link_of (p := (p.1,!p.2)) hx (by omega)
      have noneRaw (i : Vertex) (hi : Path G A i.val b) : False := by
        have he : i = u.val := only_vertex_at_reader h ho hc hmax hm (hi.tail hl)
        subst i
        have next := through_reader hm (by have := (h.1 b hb).1; have := u.val.isLt; omega) hi
        exact hbt.not_ge (path_le h next)
      obtain ⟨q,hq,hqr,hqt⟩ := upstream_repeat h hactual (b,false) hb noneRaw
      obtain ⟨r,hrG,hrr,hrt⟩ := upstream_repeat h hactual (b,true) hb noneRaw
      have hd : q ≠ r := by
        intro he
        subst r
        rcases trail_compare hqt hrt with he' | he'
        · have := trail_same_gate h he' rfl
          simp at this
        · have := trail_same_gate h he' rfl
          simp at this
      exact two (q,false) (r,false)
        (Finset.mem_filter.mpr ⟨mem_credits.mpr ⟨hq,hqr,Or.inl rfl⟩,(trail_path hqt).tail hl⟩)
        (Finset.mem_filter.mpr ⟨mem_credits.mpr ⟨hrG,hrr,Or.inl rfl⟩,(trail_path hrt).tail hl⟩)
        (fun he => hd (congrArg Prod.fst he))
  have disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset U)) C := by
    intro u _ v _ hne
    refine Finset.disjoint_left.mpr fun p hp hq => ?_
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    rcases path_compare hp' hq' with hx | hx
    · have hu := link_of (hR u.val u.property) (one u.val u.property)
      exact hne (Subtype.ext (only_vertex_at_reader h ho hc hmax (hR v.val v.property) (hx.head hu)))
    · have hv := link_of (hR v.val v.property) (one v.val v.property)
      exact hne (Subtype.ext (only_vertex_at_reader h ho hc hmax (hR u.val u.property) (hx.head hv)).symm)
  have hsum : (∑ u : U, 2) ≤ ∑ u : U, (C u).card := Finset.sum_le_sum fun u _ => enough u
  rw [← Finset.card_biUnion disj] at hsum
  have hsub : Finset.univ.biUnion C ⊆ credits G A :=
    fun p hp => (Finset.mem_filter.mp (Finset.mem_biUnion.mp hp).choose_spec.2).1
  have hh := hsum.trans (Finset.card_le_card hsub)
  simpa [Nat.mul_comm, U] using hh

open scoped BigOperators

lemma credit_budget {G A K V o} (h : Valid G A K V) (ho : o ∈ G)
    (live : ∀ w ∈ actual G, w ≠ o → (uses G A w).Nonempty)
    (hactual : ∀ j ∈ G, ∀ d, A j d ∈ actual G) :
    (credits G A).card + 2 * (26 - (uniqueVertices G A).card) ≤ 4 * (G.card - 25) := by
  classical
  let W := actual G
  let d (w : ℕ) := (uses G A w).card
  let E := ∑ w ∈ W, (d w - 1)
  have inputlive (u : Vertex) : 0 < d u.val := by
    apply Finset.card_pos.mpr
    exact live u.val (Finset.mem_union_left _ (Finset.mem_range.mpr u.isLt))
      (by have := (h.1 o ho).1; have := u.isLt; omega)
  have hdis : Disjoint (Finset.range 26) G := Finset.disjoint_left.mpr (by
    intro i hi hg
    have := Finset.mem_range.mp hi
    have := (h.1 i hg).1
    omega)
  have hcW : W.card = 26 + G.card := by
    simp [W, actual, Finset.card_union_of_disjoint hdis]
  have portcount : ∑ w ∈ W, d w = 2 * G.card := by
    calc
      ∑ w ∈ W, d w = (ports G).card :=
        (Finset.card_eq_sum_card_fiberwise (f := fun p : Port => A p.1 p.2) (by
          intro p hp
          exact hactual p.1 ((Finset.mem_product.mp hp).1) p.2)).symm
      _ = 2 * G.card := by simp [ports, Nat.mul_comm]
  have budget : E ≤ G.card - 25 := by
    have pp : ∑ w ∈ W, ((d w - 1) + if w = o then 0 else 1) ≤ ∑ w ∈ W, d w := by
      apply Finset.sum_le_sum
      intro w hw
      split_ifs with he
      · omega
      · have := Finset.card_pos.mpr (live w hw he)
        change 0 < d w at this
        omega
    have hh : ∑ w ∈ W, (if w = o then 0 else (1 : ℕ)) = W.card - 1 := by
      have eq' : (∑ w ∈ W, (if w = o then 0 else (1 : ℕ))) =
          ∑ w ∈ W.filter (· ≠ o), (1 : ℕ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro w _
        by_cases he : w = o <;> simp [he]
      rw [eq']
      have eq : W.filter (· ≠ o) = W.erase o := by ext w; simp [and_comm]
      rw [eq]
      simp [Finset.card_erase_of_mem (show o ∈ W from Finset.mem_union_right _ ho)]
    rw [Finset.sum_add_distrib, hh, hcW, portcount] at pp
    change E + (26+G.card-1) ≤ 2*G.card at pp
    omega
  let R := W.filter fun w => w < 26 ∧ 2 ≤ d w
  let T := (Finset.univ : Finset Vertex).filter fun u => 2 ≤ d u.val
  have hTR : T.card = R.card := by
    have him : T.image Fin.val = R := by
      ext w
      simp only [Finset.mem_image, T, R, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨Finset.mem_union_left _ (Finset.mem_range.mpr u.isLt),u.isLt,hu⟩
      · rintro ⟨_,hw,hrep⟩
        exact ⟨⟨w,hw⟩,hrep,rfl⟩
    rw [← him, Finset.card_image_of_injective _ Fin.val_injective]
  have hR : R.card = 26 - (uniqueVertices G A).card := by
    have hU : uniqueVertices G A ∪ T = Finset.univ := by
      ext u
      simp only [T, uniqueVertices, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      have := inputlive u
      change d u.val = 1 ∨ 2 ≤ d u.val
      omega
    have hd : Disjoint (uniqueVertices G A) T := Finset.disjoint_left.mpr (by
      intro u h1 h2
      exact (Finset.mem_filter.mp h2).2.not_gt (by
        change d u.val < 2
        rw [show d u.val = 1 from (Finset.mem_filter.mp h1).2]
        decide))
    have hh := congrArg Finset.card hU
    rw [Finset.card_union_of_disjoint hd, hTR] at hh
    simp at hh
    omega
  let F (w : ℕ) := (credits G A).filter fun p => A p.1.1 p.1.2 = w
  have cF : (credits G A).card = ∑ w ∈ W, (F w).card :=
    Finset.card_eq_sum_card_fiberwise (by
      rintro ⟨⟨t,z⟩,b⟩ hp
      exact hactual t (mem_credits.mp hp).1 z)
  have cR : R.card = ∑ w ∈ W, if w < 26 ∧ 2 ≤ d w then (1 : ℕ) else 0 := by
    rw [← Finset.sum_filter]
    simp [R]
  have pointwise (w : ℕ) :
      (F w).card + 2 * (if w < 26 ∧ 2 ≤ d w then 1 else 0) ≤ 4 * (d w - 1) := by
    by_cases hr : 2 ≤ d w
    · let B : Finset Bool := if w < 26 then {false} else Finset.univ
      have he : F w = (uses G A w) ×ˢ B := by
        ext p
        obtain ⟨⟨t,z⟩,b⟩ := p
        simp only [F, Finset.mem_filter, mem_credits, Finset.mem_product, mem_uses]
        by_cases hp : A t z = w
        · by_cases hl : w < 26
          · have hn : ¬ 26 ≤ w := by omega
            simp [hp, show 2 ≤ (uses G A w).card from hr, B, hl, hn]
          · have hn : 26 ≤ w := by omega
            simp [hp, show 2 ≤ (uses G A w).card from hr, B, hl, hn]
        · simp [hp]
      rw [he, Finset.card_product]
      change d w * B.card + 2 * (if w < 26 ∧ 2 ≤ d w then 1 else 0) ≤ _
      by_cases hl : w < 26
      · simp only [B, hl, ite_true, Finset.card_singleton, mul_one, hr, and_self]
        omega
      · simp [B, hl]
        omega
    · have he : F w = ∅ := by
        ext p
        obtain ⟨⟨t,z⟩,b⟩ := p
        simp only [F, Finset.mem_filter, mem_credits, Finset.notMem_empty, iff_false]
        rintro ⟨⟨_,hq,_⟩,rfl⟩
        exact hr hq
      simp [he, hr]
  have hh := Finset.sum_le_sum (s := W) (fun w _ => pointwise w)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← cF, ← cR, hR] at hh
  exact hh.trans (Nat.mul_le_mul_left _ budget)

lemma lower (s : ℕ) (hr : Realizes s) : 38 ≤ s := by
  classical
  let m := Nat.find ⟨s,hr⟩
  have hm : m ≤ s := Nat.find_min' ⟨s,hr⟩ hr
  obtain ⟨G,A,K,V,o,hcard,hv,ho,hc⟩ := Nat.find_spec (H := ⟨s,hr⟩)
  have least : ∀ q < G.card, ¬ Realizes q :=
    fun q hq => Nat.find_min ⟨s,hr⟩ (hq.trans_le hcard)
  obtain ⟨live, hactual, hoG⟩ := used_or_output hv ho hc least
  have ha := two_credits hv hoG hc (output_max hv hoG hc least) hactual
  have hb := credit_budget hv hoG live hactual
  have hu : (uniqueVertices G A).card ≤ 26 := by
    have := Finset.card_le_univ (uniqueVertices G A)
    simpa using this
  omega

end PEqualNP.Outside.L_meta_7137

theorem PEqualNP.Outside.L_meta_7137 :
    have x1 : Finset ℕ := {(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)}; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     ∀ (x4 x5 : ℕ),       (∀ (x6 x7 : Fin (26 : ℕ)),           (have x8 : List Bool := x2.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = x6 ∨ x8 = x7));             PEqualNP.CircuitLowerBounds.GateOp.or.eval [x8.getD x4 Bool.false, x8.getD x5 Bool.false] = Bool.true) ↔             (SimpleGraph.fromRel fun (x8 x9 : Fin (26 : ℕ)) => ↑x8 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x9 ∧ (↑x8 + (13 : ℕ) - (↑x9 - (13 : ℕ))) % (13 : ℕ) ∈ x1).Adj x6 x7) →         (37 : ℕ) ≤ x2.size := by
  intro _ C hm a b hc
  have h : ∀ u v : Fin 26,
      ((C.wires (List.ofFn (PEqualNP.Outside.L_meta_7137.pair u v))).getD a false ||
        (C.wires (List.ofFn (PEqualNP.Outside.L_meta_7137.pair u v))).getD b false) =
        PEqualNP.Outside.L_meta_7137.edge u v := by
    intro u v
    apply Bool.eq_iff_iff.mpr
    rw [PEqualNP.Outside.L_meta_7137.edge_eq]
    have hs := hc u v
    change PEqualNP.CircuitLowerBounds.GateOp.or.eval
      [(C.wires (List.ofFn (PEqualNP.Outside.L_meta_7137.pair u v))).getD a false,
        (C.wires (List.ofFn (PEqualNP.Outside.L_meta_7137.pair u v))).getD b false] = true ↔
      (SimpleGraph.fromRel PEqualNP.Outside.L_meta_7137.rel).Adj u v at hs
    simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hs
  have hl := PEqualNP.Outside.L_meta_7137.lower _ (PEqualNP.Outside.L_meta_7137.realize C hm a b h)
  omega
