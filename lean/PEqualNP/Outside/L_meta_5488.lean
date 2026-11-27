import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5488

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BV := BitVec 16

def v0 : BV := 0xAAAA#16
def v1 : BV := 0xCCCC#16
def v2 : BV := 0xF0F0#16
def v3 : BV := 0xFF00#16
def bvAll : BV := 0xFFFF#16
def initBV : List BV := [v0, v1, v2, v3]

def addIfNew (ws acc : List BV) (c : BV) : List BV :=
  if c != 0#16 && c != bvAll && !ws.contains c && !acc.contains c then c :: acc else acc

def stepPair (ws acc : List BV) (a b : BV) : List BV :=
  if a.toNat < b.toNat then
    addIfNew ws (addIfNew ws acc (a &&& b)) (a ||| b)
  else acc

def stepList (ws : List BV) : List BV :=
  ws.foldl (fun acc a => ws.foldl (fun acc2 b => stepPair ws acc2 a b) acc) []

def pairHits (ws : List BV) (t : BV) : Bool :=
  ws.any fun a => ws.any fun b => (a &&& b) == t || (a ||| b) == t

def canReachMono : Nat → List BV → BV → Bool
  | 0, ws, t => ws.contains t
  | 1, ws, t => ws.contains t || pairHits ws t
  | k + 2, ws, t => ws.contains t || (stepList ws).any (fun c => canReachMono (k + 1) (c :: ws) t)

lemma mem_addIfNew_of_mem {ws acc : List BV} {c x : BV} (hx : x ∈ acc) :
    x ∈ addIfNew ws acc c := by
  unfold addIfNew; split_ifs
  · exact List.mem_cons_of_mem _ hx
  · exact hx

lemma mem_addIfNew_self {ws acc : List BV} {c : BV}
    (h0 : c ≠ 0#16) (h1 : c ≠ bvAll) (hw : c ∉ ws) :
    c ∈ addIfNew ws acc c := by
  unfold addIfNew
  by_cases ha : c ∈ acc
  · split_ifs
    · exact List.mem_cons_self
    · exact ha
  · have hcond : (c != 0#16 && c != bvAll && !ws.contains c && !acc.contains c) = true := by
      simp [h0, h1, hw, ha]
    rw [ite_eq_left_iff.mpr (fun h => absurd hcond h)]
    exact List.mem_cons_self

lemma mem_stepPair_of_mem {ws acc : List BV} {a b x : BV} (hx : x ∈ acc) :
    x ∈ stepPair ws acc a b := by
  unfold stepPair; split_ifs
  · exact mem_addIfNew_of_mem (mem_addIfNew_of_mem hx)
  · exact hx

lemma foldl_stepPair_mono {ws : List BV} (l : List BV) (a x : BV) (acc : List BV) (hx : x ∈ acc) :
    x ∈ l.foldl (fun acc2 b => stepPair ws acc2 a b) acc := by
  induction l generalizing acc with
  | nil => exact hx
  | cons b bs ih => exact ih _ (mem_stepPair_of_mem hx)

lemma foldl_stepList_mono {ws : List BV} (l : List BV) (x : BV) (acc : List BV) (hx : x ∈ acc) :
    x ∈ l.foldl (fun acc a => ws.foldl (fun acc2 b => stepPair ws acc2 a b) acc) acc := by
  induction l generalizing acc with
  | nil => exact hx
  | cons a as ih => exact ih _ (foldl_stepPair_mono ws a x acc hx)

lemma foldl_stepPair_mem {ws : List BV} (l : List BV) {a b c : BV} (hb : b ∈ l)
    (hlt : a.toNat < b.toNat) (hc : c = a &&& b ∨ c = a ||| b)
    (h0 : c ≠ 0#16) (h1 : c ≠ bvAll) (hw : c ∉ ws) (acc : List BV) :
    c ∈ l.foldl (fun acc2 b => stepPair ws acc2 a b) acc := by
  induction l generalizing acc with
  | nil => simp at hb
  | cons y ys ih =>
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · rw [List.foldl_cons]
      apply foldl_stepPair_mono
      unfold stepPair
      rw [ite_eq_left_iff.mpr (fun h => absurd hlt h)]
      rcases hc with rfl | rfl
      · exact mem_addIfNew_of_mem (mem_addIfNew_self h0 h1 hw)
      · exact mem_addIfNew_self h0 h1 hw
    · rw [List.foldl_cons]; exact ih hb _

lemma mem_stepList_of_op {ws : List BV} {a b c : BV} (ha : a ∈ ws) (hb : b ∈ ws)
    (hc : c = a &&& b ∨ c = a ||| b) (h0 : c ≠ 0#16) (h1 : c ≠ bvAll) (hw : c ∉ ws) :
    c ∈ stepList ws := by
  have hab : a ≠ b := by
    intro h; subst h; rcases hc with rfl | rfl <;> exact hw (by simpa using ha)
  have hlt_or : a.toNat < b.toNat ∨ b.toNat < a.toNat := by
    rcases Nat.lt_trichotomy a.toNat b.toNat with h | h | h
    · exact Or.inl h
    · exact absurd (BitVec.eq_of_toNat_eq h) hab
    · exact Or.inr h
  suffices ∀ {u v : BV}, u ∈ ws → v ∈ ws → u.toNat < v.toNat →
      (c = u &&& v ∨ c = u ||| v) → c ∈ stepList ws by
    rcases hlt_or with h | h
    · exact this ha hb h hc
    · exact this hb ha h (by rcases hc with rfl | rfl; exact Or.inl (BitVec.and_comm ..); exact Or.inr (BitVec.or_comm ..))
  intro u v hu hv hlt huv
  unfold stepList
  have aux : ∀ (l : List BV) (acc : List BV), u ∈ l →
      c ∈ l.foldl (fun acc a => ws.foldl (fun acc2 b => stepPair ws acc2 a b) acc) acc := by
    intro l
    induction l with
    | nil => intro _ h; simp at h
    | cons x xs ih =>
      intro acc hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [List.foldl_cons]
        exact foldl_stepList_mono xs c _ (foldl_stepPair_mem ws hv hlt huv h0 h1 hw acc)
      · rw [List.foldl_cons]; exact ih _ hx
  exact aux ws [] hu

lemma canReachMono_of_mem {k : Nat} {ws : List BV} {t : BV} (ht : t ∈ ws) :
    canReachMono k ws t = true := by
  cases k with
  | zero => simpa [canReachMono] using ht
  | succ k' =>
    cases k' with
    | zero => simp [canReachMono, ht]
    | succ k'' => simp [canReachMono, ht]

def ValidStep (ws : List BV) (g : BV) : Prop :=
  g = 0#16 ∨ g = bvAll ∨ g ∈ ws ∨ ∃ a ∈ ws, ∃ b ∈ ws, g = a &&& b ∨ g = a ||| b

def ValidSeq : Nat → List BV → List BV → Prop
  | _, _, [] => True
  | k, ws, g :: gs =>
    ValidStep ws g ∧
    (g = 0#16 ∨ g = bvAll ∨ g ∈ ws → ValidSeq k ws gs) ∧
    (¬(g = 0#16 ∨ g = bvAll ∨ g ∈ ws) → ∃ k', k = k' + 1 ∧ ValidSeq k' (g :: ws) gs)

lemma canReachMono_of_validSeq : ∀ {k : Nat} {ws gs : List BV} {t : BV},
    ValidSeq k ws gs → t ≠ 0#16 → t ≠ bvAll →
    (t ∈ ws ∨ t ∈ gs) → canReachMono k ws t = true := by
  intro k ws gs t hvs ht0 ht1 hmem
  induction gs generalizing k ws with
  | nil =>
    rcases hmem with hw | hg
    · exact canReachMono_of_mem hw
    · simp at hg
  | cons g gs ih =>
    rcases hvs with ⟨hstep, htriv_imp, hnew_imp⟩
    by_cases htriv : g = 0#16 ∨ g = bvAll ∨ g ∈ ws
    · apply ih (htriv_imp htriv)
      rcases hmem with hw | hg
      · exact Or.inl hw
      · rcases List.mem_cons.mp hg with rfl | hgs
        · rcases htriv with rfl | rfl | hw
          · exact absurd rfl ht0
          · exact absurd rfl ht1
          · exact Or.inl hw
        · exact Or.inr hgs
    · obtain ⟨k', rfl, hvs'⟩ := hnew_imp htriv
      have hg0 : g ≠ 0#16 := fun h => htriv (Or.inl h)
      have hg1 : g ≠ bvAll := fun h => htriv (Or.inr (Or.inl h))
      have hgw : g ∉ ws := fun h => htriv (Or.inr (Or.inr h))
      have hop : ∃ a ∈ ws, ∃ b ∈ ws, g = a &&& b ∨ g = a ||| b := by
        rcases hstep with rfl | rfl | hw | h
        · exact absurd rfl hg0
        · exact absurd rfl hg1
        · exact absurd hw hgw
        · exact h
      obtain ⟨a, ha, b, hb, hab⟩ := hop
      have hrec : canReachMono k' (g :: ws) t = true := by
        apply ih hvs'
        rcases hmem with hw | hg
        · exact Or.inl (List.mem_cons_of_mem _ hw)
        · rcases List.mem_cons.mp hg with rfl | hgs
          · exact Or.inl List.mem_cons_self
          · exact Or.inr hgs
      cases k' with
      | zero =>
        simp only [canReachMono, List.contains_eq_mem, decide_eq_true_eq, List.mem_cons] at hrec
        simp only [canReachMono, Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq]
        rcases hrec with rfl | hw
        · right
          simp only [pairHits, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
          exact ⟨a, ha, b, hb, hab.imp Eq.symm Eq.symm⟩
        · exact Or.inl hw
      | succ k'' =>
        simp only [canReachMono, Bool.or_eq_true, List.any_eq_true]
        right
        exact ⟨g, mem_stepList_of_op ha hb hab hg0 hg1 hgw, hrec⟩

-- Circuit reachability and degree counting on n = 6 inputs
def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

def isNotGate (C : Circuit) (w : Nat) : Bool :=
  match C.gates[w - 6]? with
  | some g => isNotOp g.op
  | none => false

def effIn (C : Circuit) (j : Nat) : List Nat :=
  match C.gates[j]? with
  | none => []
  | some g =>
    if isNotOp g.op then (g.inputs.take 1).filter (· < 6 + j)
    else g.inputs.filter (· < 6 + j)

lemma effIn_lt (C : Circuit) (j u : Nat) (hu : u ∈ effIn C j) : u < 6 + j := by
  unfold effIn at hu
  cases h : C.gates[j]? with
  | none => simp [h] at hu
  | some g =>
    simp only [h] at hu
    split_ifs at hu
    · exact (List.mem_filter.mp hu).2 |> of_decide_eq_true
    · exact (List.mem_filter.mp hu).2 |> of_decide_eq_true

lemma effIn_len_not (C : Circuit) (j : Nat) (g : Gate) (hg : C.gates[j]? = some g)
    (hop : isNotOp g.op = true) : (effIn C j).length ≤ 1 := by
  unfold effIn; simp only [hg, hop, ite_true]
  exact le_trans (List.length_filter_le ..) (List.length_take_le ..)

lemma effIn_len_bin (C : Circuit) (j : Nat) (g : Gate) (hg : C.gates[j]? = some g)
    (h2 : g.inputs.length ≤ 2) : (effIn C j).length ≤ 2 := by
  unfold effIn; simp only [hg]
  split_ifs
  · exact le_trans (List.length_filter_le ..) (le_trans (List.length_take_le ..) (by omega))
  · exact le_trans (List.length_filter_le ..) h2

def reach (C : Circuit) (w : Nat) : Finset Nat :=
  if h6 : w < 6 then {w}
  else if w - 6 < C.gates.length then
    insert w ((effIn C (w - 6)).attach.foldl (fun (acc : Finset Nat) (u : {x // x ∈ effIn C (w - 6)}) =>
      have : u.val < w := by
        have hlt := effIn_lt C (w - 6) u.val u.property
        omega
      acc ∪ reach C u.val) ∅)
  else ∅
termination_by w

lemma mem_foldl_union_iff {α β : Type} [DecidableEq β] (l : List α) (f : α → Finset β)
    (acc : Finset β) (x : β) :
    x ∈ l.foldl (fun s a => s ∪ f a) acc ↔ x ∈ acc ∨ ∃ a ∈ l, x ∈ f a := by
  induction l generalizing acc with
  | nil => simp
  | cons a as ih =>
    rw [List.foldl_cons, ih, Finset.mem_union]
    constructor
    · rintro ((hx | hfa) | ⟨b, hb, hfb⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨a, List.mem_cons_self, hfa⟩
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hfb⟩
    · rintro (hx | ⟨b, hb, hfb⟩)
      · exact Or.inl (Or.inl hx)
      · rcases List.mem_cons.mp hb with rfl | hbs
        · exact Or.inl (Or.inr hfb)
        · exact Or.inr ⟨b, hbs, hfb⟩

lemma reach_lt_len (C : Circuit) (w u : Nat) (hu : u ∈ reach C w) :
    u < 6 + C.gates.length := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    unfold reach at hu
    split_ifs at hu with h1 h2
    · simp only [Finset.mem_singleton] at hu; omega
    · simp only [Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · omega
      · rw [mem_foldl_union_iff] at hu
        rcases hu with hnil | ⟨⟨a, ha⟩, _, hua⟩
        · simp at hnil
        · have hlt : a < w := by have := effIn_lt C (w - 6) a ha; omega
          exact ih a hlt hua
    · simp at hu

lemma reach_mem_self (C : Circuit) (w : Nat) (hne : (reach C w).Nonempty) : w ∈ reach C w := by
  unfold reach at hne ⊢
  split_ifs at hne ⊢ with h1 h2
  · exact Finset.mem_singleton_self w
  · exact Finset.mem_insert_self w _
  · simp at hne

lemma reach_parent (C : Circuit) (w u : Nat) (hu : u ∈ reach C w) (hne : u ≠ w) :
    ∃ g ∈ reach C w, 6 ≤ g ∧ g - 6 < C.gates.length ∧ u ∈ effIn C (g - 6) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    unfold reach at hu
    split_ifs at hu with h1 h2
    · simp only [Finset.mem_singleton] at hu; exact absurd hu hne
    · simp only [Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · exact absurd rfl hne
      · rw [mem_foldl_union_iff] at hu
        rcases hu with hnil | ⟨⟨a, ha⟩, _, hua⟩
        · simp at hnil
        · have hlt : a < w := by have := effIn_lt C (w - 6) a ha; omega
          by_cases hau : u = a
          · subst hau
            refine ⟨w, ?_, by omega, h2, ha⟩
            unfold reach; split_ifs <;> try omega
            exact Finset.mem_insert_self w _
          · obtain ⟨g, hga, hg6, hgl, hug⟩ := ih a hlt hua hau
            refine ⟨g, ?_, hg6, hgl, hug⟩
            unfold reach; split_ifs <;> try omega
            apply Finset.mem_insert_of_mem
            rw [mem_foldl_union_iff]
            exact Or.inr ⟨⟨a, ha⟩, List.mem_attach _ _, hga⟩
    · simp at hu

lemma reach_subset_of_effIn (C : Circuit) (w a : Nat) (hw : 6 ≤ w) (hwl : w - 6 < C.gates.length)
    (ha : a ∈ effIn C (w - 6)) : reach C a ⊆ reach C w := by
  intro u hu
  unfold reach
  split_ifs <;> try omega
  apply Finset.mem_insert_of_mem
  rw [mem_foldl_union_iff]
  exact Or.inr ⟨⟨a, ha⟩, List.mem_attach _ _, hu⟩

def stepGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepGate x := rfl

lemma foldl_stepGate_len (gs : List Gate) (init : List Bool) :
    (gs.foldl stepGate init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepGate]; omega

lemma foldl_stepGate_getD_lt (gs : List Gate) (init : List Bool) (i : Nat) (hi : i < init.length) :
    (gs.foldl stepGate init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepGate]; omega)]
    unfold stepGate; rw [List.getD_append _ _ _ _ hi]

lemma wires_take (C : Circuit) (x : List Bool) (j : Nat) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun k => ((C.gates.take j).foldl stepGate x).getD k false) := by
  rw [wires_eq_foldl]
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hj]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  set pref := (C.gates.take j).foldl stepGate x
  have hlen : pref.length = x.length + j := by
    rw [foldl_stepGate_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [foldl_stepGate_getD_lt _ _ (x.length + j) (by simp [stepGate, hlen])]
  unfold stepGate
  rw [List.getD_append_right _ _ _ _ (by omega)]
  have hsub : x.length + j - pref.length = 0 := by omega
  rw [hsub]; rfl

lemma wires_pref_eq (C : Circuit) (x : List Bool) (j k : Nat) (hj : j < C.gates.length)
    (hk : k < x.length + j) :
    ((C.gates.take j).foldl stepGate x).getD k false = (C.wires x).getD k false := by
  rw [wires_eq_foldl]
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  have hlen : ((C.gates.take j).foldl stepGate x).length = x.length + j := by
    rw [foldl_stepGate_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  conv_rhs => rw [hsplit, List.foldl_append]
  exact (foldl_stepGate_getD_lt (C.gates.drop j) ((C.gates.take j).foldl stepGate x) k (by omega)).symm

lemma wires_getD_ge (C : Circuit) (x : List Bool) (w : Nat) (hw : x.length + C.gates.length ≤ w) :
    (C.wires x).getD w false = false := by
  rw [wires_eq_foldl, List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [foldl_stepGate_len]; exact hw

lemma wires_getD_lt6 (C : Circuit) (x : Fin 6 → Bool) (i : Nat) (hi : i < 6) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [wires_eq_foldl, foldl_stepGate_getD_lt _ _ i (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

lemma eval_eq_of_eq_on_reach (C : Circuit) (x y : Fin 6 → Bool) (w : Nat)
    (heq : ∀ i : Fin 6, i.val ∈ reach C w → x i = y i) :
    (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h6 : w < 6
    · rw [wires_getD_lt6 C x w h6, wires_getD_lt6 C y w h6]
      apply heq ⟨w, h6⟩
      unfold reach; split_ifs <;> try omega
      exact Finset.mem_singleton_self w
    · by_cases hl : w - 6 < C.gates.length
      · have hw_eq : w = (List.ofFn x).length + (w - 6) := by simp; omega
        have hw_eq' : w = (List.ofFn y).length + (w - 6) := by simp; omega
        conv_lhs => rw [hw_eq, wires_take C (List.ofFn x) (w - 6) hl]
        conv_rhs => rw [hw_eq', wires_take C (List.ofFn y) (w - 6) hl]
        set g := C.gates[w - 6]
        set px := (C.gates.take (w - 6)).foldl stepGate (List.ofFn x)
        set py := (C.gates.take (w - 6)).foldl stepGate (List.ofFn y)
        have hpx_len : px.length = w := by
          rw [foldl_stepGate_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hl)]; omega
        have hpy_len : py.length = w := by
          rw [foldl_stepGate_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hl)]; omega
        have hwire : ∀ k, k ∈ effIn C (w - 6) → px.getD k false = py.getD k false := by
          intro k hk
          have hkw : k < w := by have := effIn_lt C (w - 6) k hk; omega
          rw [wires_pref_eq C (List.ofFn x) (w - 6) k hl (by simp; omega),
              wires_pref_eq C (List.ofFn y) (w - 6) k hl (by simp; omega)]
          apply ih k hkw
          intro i hi
          exact heq i (reach_subset_of_effIn C w k (by omega) hl hk hi)
        cases hop : g.op with
        | not =>
          simp only [GateOp.eval]
          cases hin : g.inputs with
          | nil => rfl
          | cons k ks =>
            simp only [List.map_cons, List.headD_cons]
            by_cases hkw : k < w
            · have hk_eff : k ∈ effIn C (w - 6) := by
                unfold effIn
                rw [List.getElem?_eq_getElem hl]
                have hno : isNotOp g.op = true := by simp [hop, isNotOp]
                simp only [g, hno, ite_true, hin, List.take_succ_cons, List.take_zero,
                  List.mem_filter, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq]
                exact ⟨trivial, by omega⟩
              rw [hwire k hk_eff]
            · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
                  List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        | _ =>
          have hmap_eq : g.inputs.map (fun k => px.getD k false) = g.inputs.map (fun k => py.getD k false) := by
            apply List.map_congr_left
            intro k hk
            by_cases hkw : k < w
            · have hk_eff : k ∈ effIn C (w - 6) := by
                unfold effIn
                rw [List.getElem?_eq_getElem hl]
                have hno : isNotOp g.op = false := by simp [hop, isNotOp]
                simp only [g, hno, Bool.false_eq_true, ite_false, List.mem_filter, decide_eq_true_eq]
                exact ⟨hk, by omega⟩
              exact hwire k hk_eff
            · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
                  List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          rw [hmap_eq]
      · rw [wires_getD_ge C (List.ofFn x) w (by simp; omega),
            wires_getD_ge C (List.ofFn y) w (by simp; omega)]

lemma degree_bound (C : Circuit) (hF : FanInTwo C)
    (hV : ∀ i : Fin 6, i.val ∈ reach C C.output) :
    let U := (reach C C.output).filter (6 ≤ ·)
    let Unot := U.filter (fun w => isNotGate C w = true)
    5 + Unot.card ≤ U.card := by
  intro U Unot
  have hR_ne : (reach C C.output).Nonempty := ⟨0, hV 0⟩
  have hout_mem : C.output ∈ reach C C.output := reach_mem_self C C.output hR_ne
  have hsub : (reach C C.output).erase C.output ⊆ U.biUnion (fun w => (effIn C (w - 6)).toFinset) := by
    intro u hu
    rw [Finset.mem_erase] at hu
    obtain ⟨g, hgr, hg6, hgl, hug⟩ := reach_parent C C.output u hu.2 hu.1
    rw [Finset.mem_biUnion]
    exact ⟨g, Finset.mem_filter.mpr ⟨hgr, hg6⟩, List.mem_toFinset.mpr hug⟩
  have hcard1 : ((reach C C.output).erase C.output).card ≤ ∑ w ∈ U, ((effIn C (w - 6)).toFinset).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hcard2 : ∑ w ∈ U, ((effIn C (w - 6)).toFinset).card ≤ ∑ w ∈ U, (effIn C (w - 6)).length :=
    Finset.sum_le_sum fun w _ => List.toFinset_card_le _
  have hcard3 : ∑ w ∈ U, (effIn C (w - 6)).length ≤ 2 * U.card - Unot.card := by
    have hsplit : ∑ w ∈ U, (effIn C (w - 6)).length =
        ∑ w ∈ Unot, (effIn C (w - 6)).length + ∑ w ∈ U \ Unot, (effIn C (w - 6)).length := by
      rw [← Finset.sum_union disjoint_sdiff_self_right, Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
    have hnot : ∑ w ∈ Unot, (effIn C (w - 6)).length ≤ Unot.card := by
      calc ∑ w ∈ Unot, (effIn C (w - 6)).length
          ≤ ∑ _w ∈ Unot, 1 := by
            apply Finset.sum_le_sum; intro w hw
            simp only [Unot, U, Finset.mem_filter] at hw
            have hlt : w - 6 < C.gates.length := by have := reach_lt_len C C.output w hw.1.1; omega
            have hg : C.gates[w - 6]? = some C.gates[w - 6] := List.getElem?_eq_getElem hlt
            have hng : isNotOp C.gates[w - 6].op = true := by
              unfold isNotGate at hw; rw [hg] at hw; exact hw.2
            exact effIn_len_not C (w - 6) C.gates[w - 6] hg hng
        _ = Unot.card := by simp
    have hbin : ∑ w ∈ U \ Unot, (effIn C (w - 6)).length ≤ 2 * (U \ Unot).card := by
      calc ∑ w ∈ U \ Unot, (effIn C (w - 6)).length
          ≤ ∑ _w ∈ U \ Unot, 2 := by
            apply Finset.sum_le_sum; intro w hw
            rw [Finset.mem_sdiff] at hw
            have hw6 : 6 ≤ w := (Finset.mem_filter.mp hw.1).2
            have hlt : w - 6 < C.gates.length := by
              have := reach_lt_len C C.output w (Finset.mem_filter.mp hw.1).1; omega
            have hg : C.gates[w - 6]? = some C.gates[w - 6] := List.getElem?_eq_getElem hlt
            have h2 := (hF C.gates[w - 6] (List.getElem_mem hlt)).2
            exact effIn_len_bin C (w - 6) C.gates[w - 6] hg h2
        _ = 2 * (U \ Unot).card := by simp [Nat.mul_comm]
    have hsubU : Unot ⊆ U := Finset.filter_subset _ _
    have hsdiff : (U \ Unot).card + Unot.card = U.card := by
      rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_left, Finset.sdiff_union_of_subset hsubU]
    have hleU : Unot.card ≤ U.card := Finset.card_le_card hsubU
    omega
  have hV_sub : Finset.range 6 ⊆ (reach C C.output).filter (· < 6) := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact Finset.mem_filter.mpr ⟨hV ⟨i, hi⟩, hi⟩
  have hV_card : 6 ≤ ((reach C C.output).filter (· < 6)).card := by
    have := Finset.card_le_card hV_sub
    simpa using this
  have hpart : (reach C C.output).card = ((reach C C.output).filter (· < 6)).card + U.card := by
    have := Finset.card_filter_add_card_filter_not (s := reach C C.output) (p := (· < 6))
    have heq : (reach C C.output).filter (fun x => ¬x < 6) = U := by
      ext x; simp [U]
    rw [heq] at this; omega
  have herase : ((reach C C.output).erase C.output).card + 1 = (reach C C.output).card :=
    Finset.card_erase_add_one hout_mem
  have hleU : Unot.card ≤ U.card := Finset.card_le_card (Finset.filter_subset _ _)
  omega

-- Restrict 1 = false and 5 = false
def emb4 (y : Fin 4 → Bool) : Fin 6 → Bool
  | ⟨0, _⟩ => y 0
  | ⟨1, _⟩ => false
  | ⟨2, _⟩ => y 1
  | ⟨3, _⟩ => y 2
  | ⟨4, _⟩ => y 3
  | ⟨5, _⟩ => false

def fin4OfNat (m : Nat) : Fin 4 → Bool := fun i => m.testBit i.val

def bvOfFnAux (g : (Fin 4 → Bool) → Bool) : Nat → BV
  | 0 => 0#16
  | k + 1 => if g (fin4OfNat k) then bvOfFnAux g k ||| (1#16 <<< k) else bvOfFnAux g k

def bvOfFn (g : (Fin 4 → Bool) → Bool) : BV := bvOfFnAux g 16

lemma bvOfFnAux_getLsbD (g : (Fin 4 → Bool) → Bool) (n m : Nat) (hm : m < 16) :
    (bvOfFnAux g n).getLsbD m = if m < n then g (fin4OfNat m) else false := by
  induction n with
  | zero => simp [bvOfFnAux]
  | succ k ih =>
    unfold bvOfFnAux
    by_cases hg : g (fin4OfNat k) = true
    · rw [ite_eq_left_iff.mpr (fun h => absurd hg h), BitVec.getLsbD_or, ih]
      by_cases hmk : m < k
      · have hmk1 : m < k + 1 := by omega
        simp [hmk, hmk1, hm]
      · by_cases heq : m = k
        · subst heq; simp [hm, hg]
        · have hmk1 : ¬(m < k + 1) := by omega
          simp [hmk, hmk1, hm]; omega
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hg), ih]
      by_cases hmk : m < k
      · have hmk1 : m < k + 1 := by omega
        simp [hmk, hmk1]
      · by_cases heq : m = k
        · subst heq; simp [hg]
        · have hmk1 : ¬(m < k + 1) := by omega
          simp [hmk, hmk1]

lemma bvOfFn_getLsbD (g : (Fin 4 → Bool) → Bool) (m : Nat) (hm : m < 16) :
    (bvOfFn g).getLsbD m = g (fin4OfNat m) := by
  unfold bvOfFn
  rw [bvOfFnAux_getLsbD g 16 m hm, ite_eq_left_iff.mpr (fun h => absurd hm h)]

lemma bvOfFn_ext {g1 g2 : (Fin 4 → Bool) → Bool} (h : ∀ y, g1 y = g2 y) :
    bvOfFn g1 = bvOfFn g2 := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [bvOfFn_getLsbD _ m hm, bvOfFn_getLsbD _ m hm, h]

lemma bvOfFn_false : bvOfFn (fun _ => false) = 0#16 := by decide
lemma bvOfFn_true : bvOfFn (fun _ => true) = bvAll := by decide
lemma bvOfFn_v0 : bvOfFn (fun y => y 0) = v0 := by decide
lemma bvOfFn_v1 : bvOfFn (fun y => y 1) = v1 := by decide
lemma bvOfFn_v2 : bvOfFn (fun y => y 2) = v2 := by decide
lemma bvOfFn_v3 : bvOfFn (fun y => y 3) = v3 := by decide

lemma bvOfFn_and (g1 g2 : (Fin 4 → Bool) → Bool) :
    bvOfFn (fun y => g1 y && g2 y) = bvOfFn g1 &&& bvOfFn g2 := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  simp [bvOfFn_getLsbD _ m hm, BitVec.getLsbD_and]

lemma bvOfFn_or (g1 g2 : (Fin 4 → Bool) → Bool) :
    bvOfFn (fun y => g1 y || g2 y) = bvOfFn g1 ||| bvOfFn g2 := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  simp [bvOfFn_getLsbD _ m hm, BitVec.getLsbD_or]

lemma bv_all_and (a : BV) : bvAll &&& a = a := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  have h1 : bvAll.getLsbD m = true := by
    have : (bvOfFn fun _ => true).getLsbD m = true := bvOfFn_getLsbD _ m hm
    rwa [bvOfFn_true] at this
  simp [BitVec.getLsbD_and, h1]

lemma bv_and_all (a : BV) : a &&& bvAll = a := by rw [BitVec.and_comm, bv_all_and]

lemma bv_all_or (a : BV) : bvAll ||| a = bvAll := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  have h1 : bvAll.getLsbD m = true := by
    have : (bvOfFn fun _ => true).getLsbD m = true := bvOfFn_getLsbD _ m hm
    rwa [bvOfFn_true] at this
  simp [BitVec.getLsbD_or, h1]

lemma bv_or_all (a : BV) : a ||| bvAll = bvAll := by rw [BitVec.or_comm, bv_all_or]

def wireBV (C : Circuit) (w : Nat) : BV :=
  bvOfFn fun y => (C.wires (List.ofFn (emb4 y))).getD w false

lemma wireBV_lt6 (C : Circuit) (i : Nat) (hi : i < 6) :
    wireBV C i = 0#16 ∨ wireBV C i ∈ initBV := by
  have h : wireBV C i = bvOfFn (fun y => emb4 y ⟨i, hi⟩) := by
    unfold wireBV; apply bvOfFn_ext; intro y; exact wires_getD_lt6 C (emb4 y) i hi
  rw [h]
  interval_cases i
  · right; simp [emb4, bvOfFn_v0, initBV]
  · left; simp [emb4, bvOfFn_false]
  · right; simp [emb4, bvOfFn_v1, initBV]
  · right; simp [emb4, bvOfFn_v2, initBV]
  · right; simp [emb4, bvOfFn_v3, initBV]
  · left; simp [emb4, bvOfFn_false]

lemma wireBV_ka (C : Circuit) : wireBV C 1 = 0#16 := by
  unfold wireBV
  have h : bvOfFn (fun y => (C.wires (List.ofFn (emb4 y))).getD 1 false) = bvOfFn (fun _ => false) := by
    apply bvOfFn_ext; intro y; rw [wires_getD_lt6 C (emb4 y) 1 (by omega)]; rfl
  rw [h, bvOfFn_false]

lemma wireBV_kb (C : Circuit) : wireBV C 5 = 0#16 := by
  unfold wireBV
  have h : bvOfFn (fun y => (C.wires (List.ofFn (emb4 y))).getD 5 false) = bvOfFn (fun _ => false) := by
    apply bvOfFn_ext; intro y; rw [wires_getD_lt6 C (emb4 y) 5 (by omega)]; rfl
  rw [h, bvOfFn_false]

lemma wireBV_gate_valid (C : Circuit) (hF : FanInTwo C) (w : Nat) (hw6 : 6 ≤ w)
    (hwl : w - 6 < C.gates.length) (hnot : isNotOp C.gates[w - 6].op = false)
    (ws : List BV) (hprev : ∀ u < w, wireBV C u = 0#16 ∨ wireBV C u = bvAll ∨ wireBV C u ∈ ws) :
    ValidStep ws (wireBV C w) ∧
    ((∃ z ∈ effIn C (w - 6), wireBV C z = 0#16) →
      wireBV C w = 0#16 ∨ wireBV C w = bvAll ∨ wireBV C w ∈ ws) ∧
    ((∀ z ∈ effIn C (w - 6), wireBV C z = 0#16) → (effIn C (w - 6)).length = 2 →
      wireBV C w = 0#16) := by
  set g := C.gates[w - 6]
  have hmem := hF g (List.getElem_mem hwl)
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
    rcases hmem.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hnot; simp [isNotOp] at hnot
  have hval : ∀ y, (C.wires (List.ofFn (emb4 y))).getD w false =
      g.op.eval (g.inputs.map fun k => if k < w then (C.wires (List.ofFn (emb4 y))).getD k false else false) := by
    intro y
    have hw_eq : w = (List.ofFn (emb4 y)).length + (w - 6) := by simp; omega
    conv_lhs => rw [hw_eq, wires_take C (List.ofFn (emb4 y)) (w - 6) hwl]
    have hmap : g.inputs.map (fun k => ((C.gates.take (w - 6)).foldl stepGate (List.ofFn (emb4 y))).getD k false) =
        g.inputs.map (fun k => if k < w then (C.wires (List.ofFn (emb4 y))).getD k false else false) := by
      apply List.map_congr_left; intro k _
      split_ifs with hkw
      · exact wires_pref_eq C (List.ofFn (emb4 y)) (w - 6) k hwl (by simp; omega)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
        · rfl
        · rw [foldl_stepGate_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hwl)]; omega
    exact congrArg g.op.eval hmap
  have hget : ∀ k, (bvOfFn fun y => if k < w then (C.wires (List.ofFn (emb4 y))).getD k false else false) =
      if k < w then wireBV C k else 0#16 := by
    intro k; split_ifs with hkw; rfl; exact bvOfFn_false
  have hlen : g.inputs.length ≤ 2 := hmem.2
  have h0_mem : ∀ k, (if k < w then wireBV C k else 0#16) = 0#16 ∨
      (if k < w then wireBV C k else 0#16) = bvAll ∨
      (if k < w then wireBV C k else 0#16) ∈ ws := by
    intro k; split_ifs with hkw; exact hprev k hkw; exact Or.inl rfl
  have hand_step : ∀ a b : BV, (a = 0#16 ∨ a = bvAll ∨ a ∈ ws) → (b = 0#16 ∨ b = bvAll ∨ b ∈ ws) →
      ValidStep ws (a &&& b) := by
    intro a b ha hb
    rcases ha with rfl | rfl | ha
    · left; simp
    · rcases hb with rfl | rfl | hb
      · left; simp
      · right; left; exact bv_all_and bvAll
      · right; right; left; rw [bv_all_and]; exact hb
    · rcases hb with rfl | rfl | hb
      · left; simp
      · right; right; left; rw [bv_and_all]; exact ha
      · exact Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, Or.inl rfl⟩))
  have hor_step : ∀ a b : BV, (a = 0#16 ∨ a = bvAll ∨ a ∈ ws) → (b = 0#16 ∨ b = bvAll ∨ b ∈ ws) →
      ValidStep ws (a ||| b) := by
    intro a b ha hb
    rcases ha with rfl | rfl | ha
    · rcases hb with rfl | rfl | hb
      · left; simp
      · right; left; simp
      · right; right; left; simpa using hb
    · right; left; exact bv_all_or b
    · rcases hb with rfl | rfl | hb
      · right; right; left; simpa using ha
      · right; left; exact bv_or_all a
      · exact Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, Or.inr rfl⟩))
  match hin : g.inputs with
  | [] =>
    have heff : effIn C (w - 6) = [] := by
      unfold effIn; rw [List.getElem?_eq_getElem hwl]; simp [g, hnot, hin]
    rcases hop with hop | hop
    · have : wireBV C w = bvAll := by
        change bvOfFn _ = _; rw [bvOfFn_ext (g2 := fun _ => true) fun y => by rw [hval y, hop, hin]; rfl]; exact bvOfFn_true
      rw [this]; refine ⟨Or.inr (Or.inl rfl), fun _ => Or.inr (Or.inl rfl), fun _ h2 => by simp [heff] at h2⟩
    · have : wireBV C w = 0#16 := by
        change bvOfFn _ = _; rw [bvOfFn_ext (g2 := fun _ => false) fun y => by rw [hval y, hop, hin]; rfl]; exact bvOfFn_false
      rw [this]; exact ⟨Or.inl rfl, fun _ => Or.inl rfl, fun _ _ => rfl⟩
  | [k] =>
    have heff_len : (effIn C (w - 6)).length ≤ 1 := by
      unfold effIn; rw [List.getElem?_eq_getElem hwl]; simp [g, hnot, hin]
      exact List.length_filter_le ..
    have : wireBV C w = if k < w then wireBV C k else 0#16 := by
      change bvOfFn _ = _
      have he : bvOfFn (fun y => (C.wires (List.ofFn (emb4 y))).getD w false) =
          bvOfFn (fun y => if k < w then (C.wires (List.ofFn (emb4 y))).getD k false else false) :=
        bvOfFn_ext fun y => by rw [hval y, hin]; rcases hop with hop | hop <;> simp [hop, GateOp.eval]
      rw [he, hget k]
    rw [this]
    have htriv := h0_mem k
    exact ⟨by rcases htriv with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h)),
      fun _ => htriv, fun _ h2 => by omega⟩
  | [k1, k2] =>
    have hmem_eff : ∀ z, z ∈ effIn C (w - 6) ↔ (z = k1 ∨ z = k2) ∧ z < w := by
      intro z
      unfold effIn; rw [List.getElem?_eq_getElem hwl]
      simp only [g, hnot, Bool.false_eq_true, ite_false, hin, List.mem_filter, List.mem_cons,
        List.not_mem_nil, or_false, decide_eq_true_eq]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
    have hlen2_lt : (effIn C (w - 6)).length = 2 → k1 < w ∧ k2 < w := by
      intro h2
      unfold effIn at h2; rw [List.getElem?_eq_getElem hwl] at h2
      simp only [g, hnot, Bool.false_eq_true, ite_false, hin] at h2
      by_cases h1 : k1 < 6 + (w - 6) <;> by_cases h2' : k2 < 6 + (w - 6)
      · omega
      · simp [h1, h2'] at h2
      · simp [h1, h2'] at h2
      · simp [h1, h2'] at h2
    rcases hop with hop | hop
    · have hwv : wireBV C w = (if k1 < w then wireBV C k1 else 0#16) &&& (if k2 < w then wireBV C k2 else 0#16) := by
        change bvOfFn _ = _
        have he : bvOfFn (fun y => (C.wires (List.ofFn (emb4 y))).getD w false) =
            bvOfFn (fun y => (if k1 < w then (C.wires (List.ofFn (emb4 y))).getD k1 false else false) &&
                             (if k2 < w then (C.wires (List.ofFn (emb4 y))).getD k2 false else false)) :=
          bvOfFn_ext fun y => by rw [hval y, hop, hin]; simp [GateOp.eval]
        rw [he, bvOfFn_and, hget k1, hget k2]
      rw [hwv]
      refine ⟨hand_step _ _ (h0_mem k1) (h0_mem k2), ?_, ?_⟩
      · rintro ⟨z, hz, hz0⟩
        obtain ⟨rfl | rfl, hzw⟩ := (hmem_eff z).mp hz
        · left; rw [ite_eq_left_iff.mpr (fun h => absurd hzw h), hz0]; simp
        · left; rw [ite_eq_left_iff.mpr (fun h => absurd hzw h), hz0]; simp
      · intro hall h2
        obtain ⟨hk1, hk2⟩ := hlen2_lt h2
        have hz1 := hall k1 ((hmem_eff k1).mpr ⟨Or.inl rfl, hk1⟩)
        rw [ite_eq_left_iff.mpr (fun h => absurd hk1 h), hz1]; simp
    · have hwv : wireBV C w = (if k1 < w then wireBV C k1 else 0#16) ||| (if k2 < w then wireBV C k2 else 0#16) := by
        change bvOfFn _ = _
        have he : bvOfFn (fun y => (C.wires (List.ofFn (emb4 y))).getD w false) =
            bvOfFn (fun y => (if k1 < w then (C.wires (List.ofFn (emb4 y))).getD k1 false else false) ||
                             (if k2 < w then (C.wires (List.ofFn (emb4 y))).getD k2 false else false)) :=
          bvOfFn_ext fun y => by rw [hval y, hop, hin]; simp [GateOp.eval]
        rw [he, bvOfFn_or, hget k1, hget k2]
      rw [hwv]
      refine ⟨hor_step _ _ (h0_mem k1) (h0_mem k2), ?_, ?_⟩
      · rintro ⟨z, hz, hz0⟩
        obtain ⟨rfl | rfl, hzw⟩ := (hmem_eff z).mp hz
        · rw [ite_eq_left_iff.mpr (fun h => absurd hzw h), hz0]; simpa using h0_mem k2
        · rw [ite_eq_left_iff.mpr (fun h => absurd hzw h), hz0]; simpa using h0_mem k1
      · intro hall h2
        obtain ⟨hk1, hk2⟩ := hlen2_lt h2
        have hz1 := hall k1 ((hmem_eff k1).mpr ⟨Or.inl rfl, hk1⟩)
        have hz2 := hall k2 ((hmem_eff k2).mpr ⟨Or.inr rfl, hk2⟩)
        rw [ite_eq_left_iff.mpr (fun h => absurd hk1 h), ite_eq_left_iff.mpr (fun h => absurd hk2 h), hz1, hz2]; simp
  | _ :: _ :: _ :: _ => rw [hin] at hlen; simp at hlen

def fTarget (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 2) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3)

def targetBV : BV := (v0 &&& v1) ||| (v0 &&& v3) ||| (v1 &&& v2)

lemma bvOfFn_fTarget : bvOfFn (fun y => fTarget (emb4 y)) = targetBV := by decide

lemma check_no3 : canReachMono 3 initBV targetBV = false := by decide

lemma fTarget_essential : ∀ i : Fin 6, ∃ x : Fin 6 → Bool,
    fTarget x ≠ fTarget (Function.update x i (!x i)) := by
  decide

-- Track count of remaining skip gates (among j1, j2 with j1 < j2 < C.gates.length)
def skipCount (j1 j2 m : Nat) : Nat :=
  (if m ≤ j1 then 1 else 0) + (if m ≤ j2 then 1 else 0)

lemma validSeq_of_two_skips (C : Circuit) (hF : FanInTwo C)
    (hnoNot : ∀ j (hj : j < C.gates.length), isNotOp C.gates[j].op = false)
    (j1 j2 : Nat) (hj12 : j1 < j2) (hj2 : j2 < C.gates.length)
    (hskip1 : ∃ z ∈ effIn C j1, wireBV C z = 0#16)
    (hskip2 : ∃ z ∈ effIn C j2, wireBV C z = 0#16) :
    ∀ (r m : Nat), m ≤ C.gates.length → C.gates.length - m = r →
      ∀ (ws : List BV),
        (∀ u < 6 + m, wireBV C u = 0#16 ∨ wireBV C u = bvAll ∨ wireBV C u ∈ ws) →
        ∀ (k : Nat), r - skipCount j1 j2 m ≤ k →
        ValidSeq k ws ((List.range r).map fun d => wireBV C (6 + m + d)) := by
  intro r
  induction r with
  | zero => intro _ _ _ _ _ _ _; simp [ValidSeq]
  | succ r ih =>
    intro m hm hrem ws hprev k hk
    have hmlt : m < C.gates.length := by omega
    have hmap : (List.range (r + 1)).map (fun d => wireBV C (6 + m + d)) =
        wireBV C (6 + m) :: (List.range r).map (fun d => wireBV C (6 + (m + 1) + d)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1; apply List.map_congr_left; intro d _
      show wireBV C (6 + m + (d + 1)) = wireBV C (6 + (m + 1) + d); congr 1; omega
    rw [hmap]
    have hgv := wireBV_gate_valid C hF (6 + m) (by omega) (by simpa using hmlt)
      (by simpa using hnoNot m hmlt) ws hprev
    refine ⟨hgv.1, ?_, ?_⟩
    · intro htriv
      apply ih (m + 1) (by omega) (by omega) ws _ k (by unfold skipCount at hk ⊢; split_ifs at hk ⊢ <;> omega)
      intro u hu
      by_cases hu' : u < 6 + m
      · exact hprev u hu'
      · have heq : u = 6 + m := by omega
        rw [heq]; exact htriv
    · intro htriv
      have hm_ne1 : m ≠ j1 := by
        intro h; subst h; exact htriv (hgv.2.1 (by simpa using hskip1))
      have hm_ne2 : m ≠ j2 := by
        intro h; subst h; exact htriv (hgv.2.1 (by simpa using hskip2))
      have hsc_eq : skipCount j1 j2 (m + 1) = skipCount j1 j2 m := by
        unfold skipCount; split_ifs <;> omega
      have hsc_le : skipCount j1 j2 m ≤ r := by
        unfold skipCount; split_ifs <;> omega
      refine ⟨k - 1, by omega, ih (m + 1) (by omega) (by omega) (wireBV C (6 + m) :: ws) ?_ (k - 1) (by omega)⟩
      intro u hu
      by_cases hu' : u < 6 + m
      · rcases hprev u hu' with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))
      · have heq : u = 6 + m := by omega
        rw [heq]; exact Or.inr (Or.inr List.mem_cons_self)

lemma main (t : Nat) (h : HasCircuitSize 6 fTarget t) : 6 ≤ t := by
  by_contra hlt
  obtain ⟨C, hF, hsz, heval⟩ := h
  have hCsz : C.gates.length ≤ 5 := by unfold Circuit.size at hsz; omega
  have hV : ∀ i : Fin 6, i.val ∈ reach C C.output := by
    intro i
    by_contra hni
    obtain ⟨x, hx⟩ := fTarget_essential i
    have heq := eval_eq_of_eq_on_reach C x (Function.update x i (!x i)) C.output (by
      intro j hj
      have hji : j ≠ i := fun h => hni (h ▸ hj)
      simp [Function.update, hji])
    have h1 := heval x
    have h2 := heval (Function.update x i (!x i))
    unfold Circuit.eval at h1 h2
    rw [heq] at h1
    exact hx (h1.symm.trans h2)
  have hdeg := degree_bound C hF hV
  dsimp only at hdeg
  set U := (reach C C.output).filter (6 ≤ ·)
  set Unot := U.filter (fun w => isNotGate C w = true)
  have hU_sub : U ⊆ Finset.image (· + 6) (Finset.range C.gates.length) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    have hlt' := reach_lt_len C C.output w hw.1
    rw [Finset.mem_image]
    exact ⟨w - 6, Finset.mem_range.mpr (by omega), by omega⟩
  have hU_le : U.card ≤ C.gates.length := by
    calc U.card ≤ (Finset.image (· + 6) (Finset.range C.gates.length)).card := Finset.card_le_card hU_sub
      _ ≤ (Finset.range C.gates.length).card := Finset.card_image_le
      _ = C.gates.length := Finset.card_range _
  have hU_eq : U.card = 5 ∧ C.gates.length = 5 ∧ Unot.card = 0 := by omega
  have hU_all : ∀ j < C.gates.length, 6 + j ∈ U := by
    have hcard_eq : U.card = (Finset.image (· + 6) (Finset.range C.gates.length)).card := by
      rw [Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]
      omega
    have hEq := Finset.eq_of_subset_of_card_le hU_sub (le_of_eq hcard_eq.symm)
    intro j hj
    rw [hEq, Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hj, by omega⟩
  have hnoNot : ∀ j (hj : j < C.gates.length), isNotOp C.gates[j].op = false := by
    intro j hj
    cases hop : isNotOp C.gates[j].op
    · rfl
    · exfalso
      have hmem : 6 + j ∈ Unot := by
        simp only [Unot, Finset.mem_filter]
        refine ⟨hU_all j hj, ?_⟩
        unfold isNotGate
        have : 6 + j - 6 = j := by omega
        rw [this, List.getElem?_eq_getElem hj]
        exact hop
      have hpos : 0 < Unot.card := Finset.card_pos.mpr ⟨6 + j, hmem⟩
      omega
  have hout_ge6 : 6 ≤ C.output := by
    by_contra hout6
    have hsubR : reach C C.output = {C.output} := by unfold reach; split_ifs <;> first | rfl | omega
    have h0 := hV 0; have h1 := hV 1
    rw [hsubR, Finset.mem_singleton] at h0 h1
    omega
  have hout_bv : wireBV C C.output = targetBV := by
    rw [← bvOfFn_fTarget]
    unfold wireBV
    apply bvOfFn_ext; intro y; exact heval (emb4 y)
  obtain ⟨ga, hgaR, hga6, hgal, hga_in⟩ := reach_parent C C.output 1 (hV ⟨1, by omega⟩) (by omega)
  obtain ⟨gb, hgbR, hgb6, hgbl, hgb_in⟩ := reach_parent C C.output 5 (hV ⟨5, by omega⟩) (by omega)
  have htwo : ∃ j1 j2, j1 < j2 ∧ j2 < C.gates.length ∧
      (∃ z ∈ effIn C j1, wireBV C z = 0#16) ∧
      (∃ z ∈ effIn C j2, wireBV C z = 0#16) := by
    by_cases hne : ga ≠ gb
    · by_cases hlt' : ga < gb
      · exact ⟨ga - 6, gb - 6, by omega, hgbl, ⟨1, hga_in, wireBV_ka C⟩, ⟨5, hgb_in, wireBV_kb C⟩⟩
      · exact ⟨gb - 6, ga - 6, by omega, hgal, ⟨5, hgb_in, wireBV_kb C⟩, ⟨1, hga_in, wireBV_ka C⟩⟩
    · push_neg at hne
      subst hne
      -- Both 1 and 5 are in effIn C (ga - 6), which has length <= 2!
      have hlen_le : (effIn C (ga - 6)).length ≤ 2 :=
        effIn_len_bin C (ga - 6) C.gates[ga - 6] (List.getElem?_eq_getElem hgal) (hF _ (List.getElem_mem hgal)).2
      have hall0 : ∀ z ∈ effIn C (ga - 6), wireBV C z = 0#16 := by
        intro z hz
        match hl : effIn C (ga - 6) with
        | [] => rw [hl] at hga_in; simp at hga_in
        | [x] =>
          rw [hl] at hga_in hgb_in
          simp only [List.mem_singleton] at hga_in hgb_in
          omega
        | [x, y] =>
          rw [hl] at hga_in hgb_in hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hga_in hgb_in hz
          rcases hga_in with rfl | rfl
          · rcases hgb_in with h | rfl
            · omega
            · rcases hz with rfl | rfl
              · exact wireBV_ka C
              · exact wireBV_kb C
          · rcases hgb_in with rfl | h
            · rcases hz with rfl | rfl
              · exact wireBV_kb C
              · exact wireBV_ka C
            · omega
        | _ :: _ :: _ :: _ => rw [hl] at hlen_le; simp at hlen_le
      have hlen2 : (effIn C (ga - 6)).length = 2 := by
        match hl : effIn C (ga - 6) with
        | [] => rw [hl] at hga_in; simp at hga_in
        | [x] =>
          rw [hl] at hga_in hgb_in
          simp only [List.mem_singleton] at hga_in hgb_in; omega
        | [_, _] => rfl
        | _ :: _ :: _ :: _ => rw [hl] at hlen_le; simp at hlen_le
      have hga0 : wireBV C ga = 0#16 := by
        have hgv := wireBV_gate_valid C hF ga hga6 hgal (hnoNot (ga - 6) hgal)
          ((List.range ga).map (wireBV C)) (fun u hu => Or.inr (Or.inr (List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩)))
        exact hgv.2.2 hall0 hlen2
      have hga_ne_out : ga ≠ C.output := by
        intro heq; rw [heq, hout_bv] at hga0; exact absurd hga0 (by decide)
      obtain ⟨gc, _, hgc6, hgcl, hgc_in⟩ := reach_parent C C.output ga hgaR hga_ne_out
      have hlt_ac : ga < gc := by have := effIn_lt C (gc - 6) ga hgc_in; omega
      exact ⟨ga - 6, gc - 6, by omega, hgcl, ⟨1, hga_in, wireBV_ka C⟩, ⟨ga, hgc_in, hga0⟩⟩
  obtain ⟨j1, j2, hj12, hj2, hskip1, hskip2⟩ := htwo
  have hvs := validSeq_of_two_skips C hF hnoNot j1 j2 hj12 hj2 hskip1 hskip2 C.gates.length 0
    (Nat.zero_le _) (by omega) initBV (by
      intro u hu
      rcases wireBV_lt6 C u (by omega) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)) 3 (by unfold skipCount; split_ifs <;> omega)
  have hout_lt : C.output < 6 + C.gates.length := reach_lt_len C C.output C.output (reach_mem_self C C.output ⟨0, hV 0⟩)
  have ht_mem : targetBV ∈ (List.range C.gates.length).map (fun d => wireBV C (6 + 0 + d)) := by
    rw [← hout_bv, List.mem_map]
    exact ⟨C.output - 6, List.mem_range.mpr (by omega), by congr 1; omega⟩
  have hreach := canReachMono_of_validSeq hvs (by decide) (by decide) (Or.inr ht_mem)
  rw [check_no3] at hreach
  exact Bool.false_ne_true hreach

end PEqualNP.Outside.L_meta_5488

theorem PEqualNP.Outside.L_meta_5488 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 2) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3)) t → 6 ≤ t :=
  PEqualNP.Outside.L_meta_5488.main
