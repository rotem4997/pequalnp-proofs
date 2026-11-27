import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_4213
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem coneSuffix (n : Nat) (gs : List Gate) (cs : List (List Nat)) :
    ∃ t, gs.foldl (coneStep n) cs=cs++t ∧ t.length=gs.length := by
  induction gs generalizing cs with
  | nil => exact ⟨[],by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t,ht,hl⟩ := ih (coneStep n cs g)
    rw [List.foldl_cons,ht]
    unfold coneStep
    exact ⟨_,List.append_assoc _ _ _,by simp [hl]⟩

theorem inheritCone (C : Circuit) (n j a k : Nat) (hj : j<C.gates.length) (ha : a<j)
    (reads : n+a ∈ (gateAt C j).inputs) (whereK : k=a ∨ InCone n C k a) : InCone n C k j := by
  let cs := (C.gates.take j).foldl (coneStep n) []
  obtain ⟨t,ht,hl⟩ := coneSuffix n (C.gates.take j) []
  have len : cs.length=j := by simp [cs,ht,hl,List.length_take,Nat.min_eq_left hj.le]
  let g := gateAt C j
  let anc := (g.inputs.filter (fun w => decide (n≤w ∧ w<n+cs.length))).flatMap (fun w => (w-n)::cs.getD (w-n) [])
  have list : C.gates=(C.gates.take j++[g])++C.gates.drop (j+1) := by
    calc C.gates = C.gates.take (j+1)++C.gates.drop (j+1) := (List.take_append_drop _ _).symm
         _ = _ := by rw [List.take_succ_eq_append_getElem hj,show g=C.gates[j] from List.getD_eq_getElem _ _ hj]
  obtain ⟨rest,hr,_⟩ := coneSuffix n (C.gates.drop (j+1)) (coneStep n cs g)
  have shape : cones n C=(cs++[anc])++rest := by
    unfold cones
    conv_lhs => rw [list,List.foldl_append,List.foldl_append]
    exact hr
  have hk : k=a ∨ k∈cs.getD a [] := by
    rcases whereK with h|h
    · exact Or.inl h
    · right;unfold InCone at h
      rw [shape,List.getD_append _ _ _ _ (by simp [len];omega),List.getD_append _ _ _ _ (by omega)] at h
      exact h
  have member : k∈anc := by
    apply List.mem_flatMap.mpr
    refine ⟨n+a,List.mem_filter.mpr ⟨reads,by simp [len,ha]⟩,?_⟩
    simpa using hk
  unfold InCone
  rw [shape,List.getD_append _ _ _ _ (by simp [len])]
  simpa [←len] using member

def bit (C : Circuit) (w : Nat) (u v : Fin 14) := val C (pairInput u v) w
def mixed (C : Circuit) (w : Nat) := bit C w 0 7=true ∧ bit C w 0 0=false ∧ bit C w 7 7=false
def cross (C : Circuit) (j : Nat) := (gateAt C j).op=.and ∧ bit C (14+j) 0 0=false ∧ bit C (14+j) 7 7=false ∧
  ∃ b : Fin 2, bit C (opnd C j b) 0 0=true ∧ bit C (opnd C j (1-b)) 7 7=true

theorem arity (C : Circuit) (ao : IsAO2 14 C) (j : Nat) (hj : j<C.gates.length) :
    ∃ a b, (gateAt C j).inputs=[a,b] := by
  have mem : gateAt C j∈C.gates := by rw [gateAt,List.getD_eq_getElem _ _ hj];exact List.getElem_mem _
  have ar := ao.2.2 _ mem
  rcases e : (gateAt C j).inputs with _|⟨a,_|⟨b,t⟩⟩ <;> simp_all

theorem stepValue (C : Circuit) (ao : IsAO2 14 C) (j a b : Nat) (hj : j<C.gates.length)
    (ins : (gateAt C j).inputs=[a,b]) (u v : Fin 14) :
    bit C (14+j) u v=(gateAt C j).op.eval [bit C a u v,bit C b u v] := by
  have slot : C.gates[j]?=some (gateAt C j) := by rw [gateAt,List.getD_eq_getElem _ _ hj,List.getElem?_eq_getElem hj]
  have la := ao.2.1 j hj a (by simp [ins])
  have lb := ao.2.1 j hj b (by simp [ins])
  unfold bit;rw [val_gate C _ slot,ins];simp [operand,la,lb]

theorem flags : ∀ a b c d : Bool, (a && b)=false → (c && d)=false →
    ¬(a=false ∧ c=false) → ¬(b=false ∧ d=false) → (a=true ∧ d=true) ∨ (b=true ∧ c=true) := by decide

theorem findCross (C : Circuit) (ao : IsAO2 14 C) (w : Nat) (m : mixed C w) :
    ∃ j, w=14+j ∧ ∃ k, (k=j ∨ InCone 14 C k j) ∧ cross C k := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    obtain ⟨on,leftOff,rightOff⟩ := m
    by_cases raw : w<14
    · let i : Fin 14 := ⟨w,raw⟩
      have get (u v : Fin 14) : bit C w u v=pairInput u v i := val_input C _ i
      rw [get] at on leftOff rightOff
      simp_all [pairInput]
    have valid : w-14<C.gates.length := by
      by_contra! big
      exact Bool.noConfusion ((val_beyond C (pairInput (0:Fin 14) 7) (by omega : 14+C.gates.length≤w)).symm.trans on)
    let j := w-14
    have hj : j<C.gates.length := valid
    have index : w=14+j := by dsimp [j];omega
    obtain ⟨a,b,ins⟩ := arity C ao j hj
    let g := gateAt C j
    have mem : g∈C.gates := by change C.gates.getD j _ ∈ _;rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    have step (u v : Fin 14) : bit C w u v=g.op.eval [bit C a u v,bit C b u v] := index ▸ stepValue C ao j a b hj ins u v
    have lower (r : Nat) (hr : r∈g.inputs) : r<w := index ▸ ao.2.1 j hj r hr
    have pass (r : Nat) (hr : r∈g.inputs) (good : mixed C r) : ∃ k, (k=j ∨ InCone 14 C k j) ∧ cross C k := by
      have earlier := lower r hr
      obtain ⟨i,ei,k,hk,hcross⟩ := ih r earlier good
      exact ⟨k,Or.inr (inheritCone C 14 j i k hj (by omega) (ei ▸ hr) hk),hcross⟩
    refine ⟨j,index,?_⟩
    have ha : a∈g.inputs := by change a∈(gateAt C j).inputs;simp [ins]
    have hb : b∈g.inputs := by change b∈(gateAt C j).inputs;simp [ins]
    rcases ao.1 g mem with kind|kind
    · have AND (u v : Fin 14) : bit C w u v=(bit C a u v && bit C b u v) := by rw [step,kind];simp [GateOp.eval]
      rw [AND,Bool.and_eq_true] at on
      by_cases leftM : mixed C a
      · exact pass a ha leftM
      by_cases rightM : mixed C b
      · exact pass b hb rightM
      have signs := flags _ _ _ _ ((AND 0 0).symm.trans leftOff) ((AND 7 7).symm.trans rightOff)
        (fun h => leftM ⟨on.1,h⟩) (fun h => rightM ⟨on.2,h⟩)
      refine ⟨j,Or.inl rfl,kind,index ▸ leftOff,index ▸ rightOff,?_⟩
      rcases signs with s|s
      · exact ⟨0,by simpa [opnd,ins] using s⟩
      · exact ⟨1,by simpa [opnd,ins] using s⟩
    · have OR (u v : Fin 14) : bit C w u v=(bit C a u v || bit C b u v) := by rw [step,kind];simp [GateOp.eval]
      rw [OR,Bool.or_eq_true] at on
      rw [OR,Bool.or_eq_false_iff] at leftOff rightOff
      rcases on with h|h
      · exact pass a ha ⟨h,leftOff.1,rightOff.1⟩
      · exact pass b hb ⟨h,leftOff.2,rightOff.2⟩

end PEqualNP.Outside.L_meta_4213
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_4213

theorem PEqualNP.Outside.L_meta_4213 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → ∀ (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((14 : ℕ) + x5) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x8 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x5 x8) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x5 x8) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → ∀ (x9 : Fin (2 : ℕ)), ∃ (x10 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x5 x9) x10 := by
  intro C
  dsimp only
  intro ao j kind pair singles side
  have hj : j<C.gates.length := by
    by_contra! h
    change (C.gates.getD j _).op=.and at kind
    rw [List.getD_eq_default _ _ h] at kind
    contradiction
  obtain ⟨a,b,ins⟩ := arity C ao j hj
  have on : bit C a 0 7=true ∧ bit C b 0 7=true := by
    change bit C (14+j) 0 7=true at pair
    rw [stepValue C ao j a b hj ins,kind] at pair
    simpa [GateOp.eval] using pair
  have active : bit C (opnd C j side) 0 7=true := by
    fin_cases side
    · simpa [opnd,ins] using on.1
    · simpa [opnd,ins] using on.2
  obtain ⟨i,idx,k,hk,c⟩ := findCross C ao _ ⟨active,singles side⟩
  refine ⟨k,?_,c⟩
  rcases hk with rfl|cone
  · exact Or.inl idx.symm
  · right;rw [idx];simpa using cone
