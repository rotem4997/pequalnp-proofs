import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Bowtie597

open PEqualNP.CircuitLowerBounds

private abbrev F := (Fin 5 → Bool) → Bool

private def inputs : List F := (fun _ => false) :: List.ofFn (fun i x => x i)

private def cl (G : List F) (w : F) : Prop :=
  ∃ S : List F, (∀ f ∈ S, f ∈ G ++ inputs) ∧ ∀ x, w x = S.all (fun f => f x)

private def good : List F → Prop
  | [] => True
  | g :: G => (∃ u v, cl G u ∧ cl G v ∧ ∀ x, g x = (u x || v x)) ∧ good G

private theorem member {G : List F} {f : F} (h : f ∈ G ++ inputs) : cl G f :=
  ⟨[f], by simpa using h, by simp⟩

private theorem cl_congr {G : List F} {u v : F} (hu : cl G u) (h : ∀ x, v x = u x) :
    cl G v := by
  obtain ⟨S, hs, he⟩ := hu
  exact ⟨S, hs, fun x => (h x).trans (he x)⟩

private theorem cl_new (G : List F) (f : F) : cl (f :: G) f := member (by simp)

private theorem cl_mono {G : List F} {f : F} (g : F) (h : cl G f) : cl (g :: G) f := by
  obtain ⟨S, hs, he⟩ := h
  exact ⟨S, fun v hv => List.mem_cons_of_mem _ (hs v hv), he⟩

private theorem cl_true (G : List F) : cl G (fun _ => true) := ⟨[], by simp, by simp⟩

private theorem cl_false (G : List F) : cl G (fun _ => false) := member (by simp [inputs])

private theorem cl_and {G : List F} {a b : F} (ha : cl G a) (hb : cl G b) :
    cl G (fun x => a x && b x) := by
  obtain ⟨A,hA,eA⟩ := ha
  obtain ⟨B,hB,eB⟩ := hb
  exact ⟨A ++ B, fun g hg => (List.mem_append.mp hg).elim (hA g) (hB g),
    fun x => by simp [eA x, eB x]⟩

private theorem gate_and (G : List ((Fin 5 → Bool) → Bool)) (f : ℕ → (Fin 5 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    cl G (fun x => GateOp.eval GateOp.and (ins.map fun i => f i x)) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact cl_congr (cl_true G) (fun x => by simp [GateOp.eval])
  · exact cl_congr (hw i) (fun x => by simp [GateOp.eval])
  · exact cl_congr (cl_and (hw i) (hw j)) (fun x => by simp [GateOp.eval])
  · exact absurd hl (by simp only [List.length_cons]; omega)

private theorem gate_or (G : List ((Fin 5 → Bool) → Bool)) (f : ℕ → (Fin 5 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ u v, cl G u ∧ cl G v ∧
      ∀ x, GateOp.eval GateOp.or (ins.map fun i => f i x) = (u x || v x) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact ⟨fun _ => false, fun _ => false, cl_false G, cl_false G,
      fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f i, hw i, hw i, fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f j, hw i, hw j, fun x => by simp [GateOp.eval]⟩
  · exact absurd hl (by simp only [List.length_cons]; omega)

private def W (gs : List Gate) (x : Fin 5 → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

private def wf (gs : List Gate) (k : ℕ) : (Fin 5 → Bool) → Bool :=
  fun x => (W gs x).getD k false

private theorem fold_len (gs : List Gate) : ∀ w0 : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs with
  | nil => intro w0; simp
  | cons g gs ih => intro w0; rw [List.foldl_cons, ih]; simp; omega

private theorem W_len (gs : List Gate) (x : Fin 5 → Bool) :
    (W gs x).length = 5 + gs.length := by
  unfold W
  rw [fold_len]
  simp

private theorem W_snoc (gs : List Gate) (g : Gate) (x : Fin 5 → Bool) :
    W (gs ++ [g]) x
      = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

private theorem wf_snoc (gs : List Gate) (g : Gate) (k : ℕ) :
    wf (gs ++ [g]) k = if k = 5 + gs.length then
      (fun x => g.op.eval (g.inputs.map fun i => wf gs i x)) else wf gs k := by
  funext x
  have hl := W_len gs x
  by_cases hk : k = 5 + gs.length
  · rw [if_pos hk]
    show (W (gs ++ [g]) x).getD k false = g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
    rw [W_snoc]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hl, hk]
  · rw [if_neg hk]
    show (W (gs ++ [g]) x).getD k false = (W gs x).getD k false
    rw [W_snoc]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
    split
    · rfl
    · rename_i h2
      have h3 : ¬ (k - (5 + gs.length) = 0) := by omega
      have h4 : ¬ k < (W gs x).length := by rw [hl]; exact h2
      simp [h3, hl, h2]

private theorem base (k : ℕ) : cl [] (wf [] k) := by
  by_cases hk : k < 5
  · apply cl_congr (member (G := []) (f := fun x => x ⟨k,hk⟩) (by interval_cases k <;> simp [inputs]))
    intro x
    interval_cases k <;> rfl
  · apply cl_congr (cl_false [])
    intro x
    simp [wf, W, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk]

private theorem inv (A : Finset ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.or ∨ g.op = GateOp.and) ∧ g.inputs.length ≤ 2)
    (hA : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.or → j ∈ A) :
    ∃ G, good G ∧ G.length ≤ (A.filter (fun j => j < gs.length)).card ∧
      ∀ k, cl G (wf gs k) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], trivial, by simp, fun k => base k⟩
  | append_singleton gs g ih =>
    obtain ⟨G, hG, hlen, hw⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
      (fun j g' hj ho => hA j g' (by
        have hjl : j < gs.length := (List.getElem?_eq_some_iff.mp hj).1
        rw [List.getElem?_append_left hjl]; exact hj) ho)
    obtain ⟨hop, hl⟩ := hm g (by simp)
    rcases hop with hop | hop
    · obtain ⟨u, v, hu, hv, he⟩ := gate_or G (wf gs) hw g.inputs hl
      have hmem : gs.length ∈ A := hA gs.length g (by simp) hop
      refine ⟨(fun x => GateOp.eval GateOp.or (g.inputs.map fun i => wf gs i x)) :: G,
        ⟨⟨u, v, hu, hv, he⟩, hG⟩, ?_, ?_⟩
      · have hsub : insert gs.length (A.filter (fun j => j < gs.length))
            ⊆ A.filter (fun j => j < (gs ++ [g]).length) := by
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_filter, List.length_append, List.length_cons,
            List.length_nil] at hj ⊢
          rcases hj with rfl | ⟨h1, h2⟩
          · exact ⟨hmem, by omega⟩
          · exact ⟨h1, by omega⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp)] at hc
        simp only [List.length_cons]
        omega
      · intro k
        rw [wf_snoc, hop]
        by_cases hk : k = 5 + gs.length
        · rw [if_pos hk]; exact cl_new _ _
        · rw [if_neg hk]; exact cl_mono _ (hw k)
    · refine ⟨G, hG, ?_, ?_⟩
      · refine le_trans hlen (Finset.card_le_card ?_)
        intro j hj
        simp only [Finset.mem_filter, List.length_append, List.length_cons, List.length_nil] at hj ⊢
        exact ⟨hj.1, by omega⟩
      · intro k
        rw [wf_snoc, hop]
        by_cases hk : k = 5 + gs.length
        · rw [if_pos hk]; exact gate_and G (wf gs) hw g.inputs hl
        · rw [if_neg hk]; exact hw k

private abbrev M := BitVec 10

private def inputMasks : Fin 5 → M := ![992, 540, 274, 139, 69]

private def sample (j : Fin 10) (i : Fin 5) : Bool := (inputMasks i)[j.val]

private def rep (f : F) (v : M) : Prop := ∀ j : Fin 10, f (sample j) = v[j.val]

private def closed (B : List M) : Prop :=
  (1023 : M) ∈ B ∧ ∀ a ∈ B, ∀ b ∈ B, a &&& b ∈ B

private def covers (B : List M) (S : List F) : Prop :=
  ∀ f ∈ S, ∃ a ∈ B, rep f a

private def grow (B : List M) (v : M) := B ++ B.map (· &&& v)

private theorem grow_closed {B : List M} (h : closed B) (v : M) : closed (grow B v) := by
  refine ⟨List.mem_append_left _ h.1, ?_⟩
  intro a ha b hb
  simp only [grow, List.mem_append, List.mem_map] at ha hb ⊢
  rcases ha with ha | ⟨u,hu,rfl⟩ <;> rcases hb with hb | ⟨w,hw,rfl⟩
  · exact Or.inl (h.2 _ ha _ hb)
  · exact Or.inr ⟨a &&& w, h.2 _ ha _ hw, by ac_rfl⟩
  · exact Or.inr ⟨u &&& b, h.2 _ hu _ hb, by ac_rfl⟩
  · exact Or.inr ⟨u &&& w, h.2 _ hu _ hw, by
      rw [show (u &&& v) &&& (w &&& v) = (u &&& w) &&& (v &&& v) by ac_rfl]
      simp⟩

private theorem cl_rep {B : List M} {G : List F} {w : F} (hc : closed B)
    (hG : covers B (G ++ inputs)) (hw : cl G w) : ∃ a ∈ B, rep w a := by
  obtain ⟨S,hS,he⟩ := hw
  have aux (T : List F) (hT : ∀ f ∈ T, f ∈ G ++ inputs) :
      ∃ a ∈ B, ∀ j : Fin 10, T.all (fun f => f (sample j)) = a[j.val] := by
    induction T with
    | nil =>
      refine ⟨1023, hc.1, ?_⟩
      intro j; fin_cases j <;> rfl
    | cons f T ih =>
      obtain ⟨a,ha,ea⟩ := hG f (hT f (by simp))
      obtain ⟨b,hb,eb⟩ := ih (fun t ht => hT t (List.mem_cons_of_mem _ ht))
      exact ⟨a &&& b, hc.2 _ ha _ hb, fun j => by simp [ea j, eb j, List.all_cons]⟩
  obtain ⟨a,ha,ea⟩ := aux S hS
  exact ⟨a,ha,fun j => (he _).trans (ea j)⟩


private theorem target_rep (w : F) (hw : ∀ x, w x = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) : rep w 977 := by
  have tab : ∀ j : Fin 10, (977 : M)[j.val] = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (ℕ × ℕ)) ∧ sample j u = true ∧ sample j v = true := by decide
  intro j
  have h := (hw (sample j)).trans (tab j).symm
  exact Bool.eq_iff_iff.mpr h

private def initial : List M :=
  [0,1,2,4,8,16,64,69,128,139,256,274,512,540,992,1023]

private theorem initial_closed : closed initial := by
  constructor
  · decide
  · have h : initial.all (fun a => initial.all (fun b => initial.contains (a &&& b))) = true := by decide
    simpa only [List.all_eq_true, List.contains_iff_mem] using h

private theorem initial_covers : covers initial inputs := by
  intro f hf
  simp only [inputs, List.mem_cons, List.mem_ofFn] at hf
  rcases hf with rfl | ⟨i,rfl⟩
  · exact ⟨0, by decide, fun _ => by simp⟩
  · exact ⟨inputMasks i, by fin_cases i <;> decide, fun _ => rfl⟩

private def next (B : List M) (v : M) : List M :=
  if v ∈ B then B else (grow B v).eraseDups

private theorem next_mem {B : List M} {v t : M} (h : closed B) :
    t ∈ next B v ↔ t ∈ grow B v := by
  unfold next
  split
  · rename_i hv
    constructor
    · exact List.mem_append_left _
    · intro ht
      rcases List.mem_append.mp ht with ht | ht
      · exact ht
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
        exact h.2 b hb v hv
  · simp

private theorem next_closed {B : List M} (hc : closed B) (v : M) : closed (next B v) := by
  have hg := grow_closed hc v
  exact ⟨(next_mem hc).mpr hg.1, fun a ha b hb =>
    (next_mem hc).mpr (hg.2 a ((next_mem hc).mp ha) b ((next_mem hc).mp hb))⟩

private def Safe : ℕ → List M → Prop
  | 0, B => 977 ∉ B
  | k+1, B => 977 ∉ B ∧ ∀ a ∈ B, ∀ b ∈ B, Safe k (next B (a ||| b))

private theorem exclusion {B : List M} {k : ℕ} (h : Safe k B) : 977 ∉ B := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

private theorem realize {G : List F} (hg : good G) (safe : Safe 4 initial) (small : G.length ≤ 4) :
    ∃ B, closed B ∧ covers B (G ++ inputs) ∧ Safe (4-G.length) B := by
  induction G with
  | nil => exact ⟨initial, initial_closed, initial_covers, safe⟩
  | cons g G ih =>
    obtain ⟨⟨u,v,hu,hv,he⟩,htail⟩ := hg
    obtain ⟨B,hB,hcov,hs⟩ := ih htail (by simp at small; omega)
    obtain ⟨a,ha,ea⟩ := cl_rep hB hcov hu
    obtain ⟨b,hb,eb⟩ := cl_rep hB hcov hv
    have heq : 4-G.length = (4-(g::G).length)+1 := by simp at small ⊢; omega
    rw [heq] at hs
    refine ⟨next B (a ||| b), next_closed hB _, ?_, hs.2 a ha b hb⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · refine ⟨a ||| b, (next_mem hB).mpr (List.mem_append_right _ (List.mem_map.mpr
        ⟨1023,hB.1,?_⟩)), fun j => by simp [he _,ea j,eb j]⟩
      exact BitVec.allOnes_and
    · obtain ⟨t,ht,et⟩ := hcov f hf
      exact ⟨t,(next_mem hB).mpr (List.mem_append_left _ ht),et⟩

private def lastOK (B : List M) : Bool :=
  decide ((977 : M) ∉ B) && B.all fun c =>
    if (c &&& 977) != 977 then true else
    let candidates := ((B.map (c &&& ·)).filter (fun u => (u &&& 977) == u)).eraseDups
    candidates.all fun u => candidates.all fun v => (u ||| v) != 977

private theorem mask_absorb (x y : M) : x &&& (x ||| y) = x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases x[i] <;> simp

private theorem last_sound {B : List M} (hc : closed B) (h : lastOK B = true) : Safe 1 B := by
  simp only [lastOK, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  refine ⟨h.1, ?_⟩
  intro a ha b hb
  change 977 ∉ next B (a ||| b)
  intro hz
  rcases List.mem_append.mp ((next_mem hc).mp hz) with hz | hz
  · exact h.1 hz
  · obtain ⟨c,hc',eq⟩ := List.mem_map.mp hz
    have id₁ : c &&& (977 : M) = 977 := by rw [← eq, ← BitVec.and_assoc]; simp
    have hyp := h.2 c hc'
    simp only [id₁, bne_self_eq_false, Bool.false_eq_true, if_false,
      List.all_eq_true, List.mem_eraseDups, List.mem_filter, List.mem_map, beq_iff_eq,
      bne_iff_ne] at hyp
    have dist : (c &&& a) ||| (c &&& b) = 977 := by rw [← eq]; exact (BitVec.and_or_distrib_left ..).symm
    have hu : (c &&& a) &&& (977 : M) = c &&& a := by rw [← dist]; exact mask_absorb ..
    have hv : (c &&& b) &&& (977 : M) = c &&& b := by rw [← dist, BitVec.or_comm]; exact mask_absorb ..
    exact hyp _ ⟨⟨a,ha,rfl⟩,hu⟩ _ ⟨⟨b,hb,rfl⟩,hv⟩ dist

private def options (B : List M) : List M :=
  ((B.flatMap fun a => B.map (a ||| ·)).eraseDups).filter (fun z => z ∉ B)

private def check : ℕ → List M → Bool
  | 0, B => decide ((977 : M) ∉ B)
  | 1, B => lastOK B
  | k+2, B => check (k+1) B && (options B).all (fun z => check (k+1) (next B z))

private theorem check_sound (k : ℕ) (B : List M) (hc : closed B) (h : check k B = true) : Safe k B := by
  match k with
  | 0 => simpa only [check, Safe, decide_eq_true_eq] using h
  | 1 => exact last_sound hc h
  | k+2 =>
    simp only [check, Bool.and_eq_true, List.all_eq_true] at h
    have hskip := check_sound (k+1) B hc h.1
    refine ⟨exclusion hskip, ?_⟩
    intro a ha b hb
    by_cases hz : a ||| b ∈ B
    · simpa [next, hz] using hskip
    · apply check_sound (k+1) _ (next_closed hc _)
      apply h.2
      simp only [options, List.mem_filter, List.mem_eraseDups, List.mem_flatMap, List.mem_map,
        decide_eq_true_eq]
      exact ⟨⟨a,ha,b,hb,rfl⟩,hz⟩
termination_by k

private def project (indices : List ℕ) (x : M) : M :=
  (BitVec.ofBoolListLE (indices.map x.getLsbD)).setWidth 10

private theorem project_and (indices : List ℕ) (x y : M) :
    project indices (x &&& y) = project indices x &&& project indices y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases hx : indices[i]? <;>
    simp [project, BitVec.getLsbD_setWidth, hi, List.getD, List.getElem?_map, hx]

private theorem project_or (indices : List ℕ) (x y : M) :
    project indices (x ||| y) = project indices x ||| project indices y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases hx : indices[i]? <;>
    simp [project, BitVec.getLsbD_setWidth, hi, List.getD, List.getElem?_map, hx]

private theorem safe_project (indices : List ℕ) (ht : project indices 977 = 977) (k : ℕ)
    (B T : List M) (hc : closed T) (hs : Safe k T)
    (sub : ∀ x ∈ B, project indices x ∈ T) : Safe k B := by
  induction k generalizing T B with
  | zero => exact fun h => exclusion hs (ht ▸ sub _ h)
  | succ k ih =>
    refine ⟨fun h => exclusion hs (ht ▸ sub _ h), ?_⟩
    intro a ha b hb
    let z := a ||| b
    let p := project indices
    let v := p a ||| p b
    have ht' : Safe k (next T v) := hs.2 _ (sub _ ha) _ (sub _ hb)
    apply ih _ _ (next_closed hc v) ht'
    intro x hx
    apply (next_mem hc).mpr
    by_cases hz : z ∈ B
    · have hx' : x ∈ B := by simpa [next, z, hz, show a ||| b ∈ B from hz] using hx
      exact List.mem_append_left _ (sub x hx')
    · have hx' : x ∈ grow B z := by simpa [next, show a ||| b ∉ B from hz, z] using hx
      rcases List.mem_append.mp hx' with hx' | hx'
      · exact List.mem_append_left _ (sub x hx')
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx'
        exact List.mem_append_right _ (List.mem_map.mpr
          ⟨p q,sub _ hq,by simp [p,v,z,project_and,project_or]⟩)

private abbrev Group := List ℕ × List M × List M

private def groupTest (B : List M) (g : Group) : Bool :=
  let p := project g.1
  let T := g.2.1
  (p 977 == 977) && B.all (fun x => T.contains (p x)) && g.2.2.all (fun z => T.contains (p z))

private def valid (k : ℕ) (T : List M) : Prop := closed T ∧ Safe k T

private def groupsValid (k : ℕ) (B : List M) : List Group → Prop
  | [] => True
  | g :: gs => (valid k g.2.1 ∧ groupTest B g = true) ∧ groupsValid k B gs

private theorem group_of_mem {k : ℕ} {B : List M} {gs : List Group}
    (hv : groupsValid k B gs) {g : Group} (hg : g ∈ gs) : valid k g.2.1 ∧ groupTest B g = true := by
  induction gs with
  | nil => simp at hg
  | cons h gs ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hv.1
    · exact ih hv.2 hg

private def coveredKeys (B : List M) (gs : List Group) : Bool :=
  (0 :: options B).all fun z => gs.any fun g => g.2.2.contains z

private theorem viaGroups {k : ℕ} {B : List M} (gs : List Group)
    (base : (977 : M) ∉ B) (cover : coveredKeys B gs = true) (ok : groupsValid k B gs) :
    Safe (k+1) B := by
  refine ⟨base, ?_⟩
  intro a ha b hb
  let z := a ||| b
  let key : M := if z ∈ B then 0 else z
  have hkey : key ∈ 0 :: options B := by
    by_cases hz : z ∈ B
    · simp [key,hz]
    · apply List.mem_cons_of_mem
      simp only [key,hz,ite_false,options,List.mem_filter,List.mem_eraseDups,List.mem_flatMap,
        List.mem_map,decide_eq_true_eq]
      exact ⟨⟨a,ha,b,hb,rfl⟩,by simp⟩
  obtain ⟨g,hg,hit⟩ := List.any_eq_true.mp (List.all_eq_true.mp cover key hkey)
  have ⟨⟨hc,hs⟩,h⟩ := group_of_mem ok hg
  simp only [groupTest, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at h
  apply safe_project g.1 h.1.1 k _ _ hc hs
  intro v hv
  by_cases hz : z ∈ B
  · exact h.1.2 _ (by simpa [next,show a ||| b ∈ B from hz] using hv)
  · have hzT := h.2 key (List.contains_iff_mem.mp hit)
    simp only [key,hz,ite_false] at hzT
    have hv' : v ∈ grow B z := by simpa [next,z,show a ||| b ∉ B from hz] using hv
    rcases List.mem_append.mp hv' with h0 | h1
    · exact h.1.2 _ h0
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h1
      rw [project_and]
      exact hc.2 _ (h.1.2 _ hw) _ hzT

private theorem closed_of_test {B : List M} (top : (1023 : M) ∈ B)
    (test : B.all (fun a => B.all (fun b => B.contains (a &&& b))) = true) : closed B :=
  ⟨top, by simpa only [List.all_eq_true, List.contains_iff_mem] using test⟩

private theorem from_safe (safe : Safe 4 initial) : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → ∀ A : Finset ℕ, (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → 5 ≤ A.card := by
  intro C hm he A hA
  by_contra! h
  obtain ⟨G,hg,hlen,hw⟩ := inv A C.gates (fun g hmem => by
    obtain ⟨hop,hl⟩ := hm g hmem
    exact ⟨by simpa [Set.mem_insert_iff, or_comm] using hop, hl⟩) hA
  have hcard := Finset.card_filter_le A (fun j => j < C.gates.length)
  obtain ⟨B,hB,hcov,hs⟩ := realize hg safe (by omega)
  obtain ⟨v,hv,ev⟩ := cl_rep hB hcov (hw C.output)
  have et := target_rep (wf C.gates C.output) he
  have eq : v = 977 := BitVec.eq_of_getElem_eq (fun i hi =>
    (ev ⟨i,hi⟩).symm.trans (et ⟨i,hi⟩))
  exact exclusion hs (eq ▸ hv)

private def B597_2_0 : List M := [0,4,34,64,128,200,257,261,291,528,532,562,626,660,823,887,951,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_0 : valid 2 B597_2_0 := by
  have h := @closed_of_test B597_2_0 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_1 : List M := [0,4,34,38,64,98,102,128,132,257,261,355,359,389,528,728,766,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_1 : valid 2 B597_2_1 := by
  have h := @closed_of_test B597_2_1 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_2 : List M := [0,4,34,64,128,132,200,257,261,291,389,528,562,626,660,951,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_2 : valid 2 B597_2_2 := by
  have h := @closed_of_test B597_2_2 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_3 : List M := [0,4,34,64,98,128,162,257,291,355,389,423,528,532,728,762,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_3 : valid 2 B597_2_3 := by
  have h := @closed_of_test B597_2_3 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_4 : List M := [0,4,34,64,128,257,261,291,295,355,389,423,528,532,728,823,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_4 : valid 2 B597_2_4 := by
  have h := @closed_of_test B597_2_4 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_5 : List M := [0,4,34,64,128,257,261,291,295,355,359,389,423,528,532,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_5 : valid 2 B597_2_5 := by
  have h := @closed_of_test B597_2_5 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_6 : List M := [0,4,34,38,64,128,257,261,291,295,355,359,389,423,528,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_6 : valid 2 B597_2_6 := by
  have h := @closed_of_test B597_2_6 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_7 : List M := [0,4,34,38,64,98,128,132,162,166,257,355,389,528,728,762,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_7 : valid 2 B597_2_7 := by
  have h := @closed_of_test B597_2_7 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_8 : List M := [0,4,34,38,64,98,128,162,257,291,355,389,423,528,728,762,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_8 : valid 2 B597_2_8 := by
  have h := @closed_of_test B597_2_8 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_9 : List M := [0,4,34,38,64,98,102,128,257,261,291,295,355,389,528,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_9 : valid 2 B597_2_9 := by
  have h := @closed_of_test B597_2_9 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_10 : List M := [0,4,34,64,98,128,132,200,257,261,291,355,389,528,626,660,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_10 : valid 2 B597_2_10 := by
  have h := @closed_of_test B597_2_10 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_11 : List M := [0,4,34,64,128,132,200,257,261,291,355,389,528,562,660,951,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_11 : valid 2 B597_2_11 := by
  have h := @closed_of_test B597_2_11 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_12 : List M := [0,4,34,64,128,257,261,291,355,389,423,528,532,728,789,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_12 : valid 2 B597_2_12 := by
  have h := @closed_of_test B597_2_12 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_13 : List M := [0,4,34,64,128,200,257,261,291,325,528,562,626,660,951,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_13 : valid 2 B597_2_13 := by
  have h := @closed_of_test B597_2_13 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_14 : List M := [0,4,34,64,128,200,257,261,291,325,528,532,562,690,823,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_14 : valid 2 B597_2_14 := by
  have h := @closed_of_test B597_2_14 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_15 : List M := [0,4,34,38,64,128,257,291,355,389,423,528,532,566,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_15 : valid 2 B597_2_15 := by
  have h := @closed_of_test B597_2_15 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_16 : List M := [0,4,34,64,128,132,257,291,355,389,423,528,532,728,732,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_16 : valid 2 B597_2_16 := by
  have h := @closed_of_test B597_2_16 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_17 : List M := [0,4,34,64,128,200,257,261,291,528,562,626,660,917,951,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_17 : valid 2 B597_2_17 := by
  have h := @closed_of_test B597_2_17 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_18 : List M := [0,4,34,38,64,98,102,128,257,291,355,389,423,528,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_18 : valid 2 B597_2_18 := by
  have h := @closed_of_test B597_2_18 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_19 : List M := [0,4,34,38,64,98,128,257,261,355,359,389,528,728,762,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_19 : valid 2 B597_2_19 := by
  have h := @closed_of_test B597_2_19 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_20 : List M := [0,4,34,64,128,132,200,257,261,291,389,528,626,660,883,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_20 : valid 2 B597_2_20 := by
  have h := @closed_of_test B597_2_20 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_21 : List M := [0,4,34,64,128,132,200,257,261,291,389,423,528,626,660,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_21 : valid 2 B597_2_21 := by
  have h := @closed_of_test B597_2_21 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_22 : List M := [0,4,34,64,128,132,200,257,261,355,389,528,562,660,694,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_22 : valid 2 B597_2_22 := by
  have h := @closed_of_test B597_2_22 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_23 : List M := [0,4,34,64,98,128,132,257,261,389,528,562,728,762,819,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_23 : valid 2 B597_2_23 := by
  have h := @closed_of_test B597_2_23 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_24 : List M := [0,4,34,64,68,128,257,261,291,325,423,528,562,728,819,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_24 : valid 2 B597_2_24 := by
  have h := @closed_of_test B597_2_24 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_25 : List M := [0,4,34,64,128,162,200,257,291,325,419,528,562,694,819,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_25 : valid 2 B597_2_25 := by
  have h := @closed_of_test B597_2_25 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_26 : List M := [0,4,34,64,128,200,257,291,325,528,562,690,694,819,947,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_26 : valid 2 B597_2_26 := by
  have h := @closed_of_test B597_2_26 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_27 : List M := [0,4,34,64,128,132,200,257,261,355,389,528,562,694,883,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_27 : valid 2 B597_2_27 := by
  have h := @closed_of_test B597_2_27 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_28 : List M := [0,4,34,38,64,128,200,257,291,325,359,528,562,694,819,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_28 : valid 2 B597_2_28 := by
  have h := @closed_of_test B597_2_28 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_29 : List M := [0,4,34,64,128,200,257,261,291,325,528,562,694,819,951,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_29 : valid 2 B597_2_29 := by
  have h := @closed_of_test B597_2_29 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_30 : List M := [0,4,34,64,128,200,257,291,325,528,562,566,694,819,887,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_30 : valid 2 B597_2_30 := by
  have h := @closed_of_test B597_2_30 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_31 : List M := [0,4,34,64,128,162,200,257,291,325,419,528,562,660,694,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_31 : valid 2 B597_2_31 := by
  have h := @closed_of_test B597_2_31 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_32 : List M := [0,4,34,64,98,128,132,162,257,291,419,528,728,762,789,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_32 : valid 2 B597_2_32 := by
  have h := @closed_of_test B597_2_32 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_33 : List M := [0,4,34,64,128,132,200,257,261,291,419,423,528,626,660,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_33 : valid 2 B597_2_33 := by
  have h := @closed_of_test B597_2_33 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_34 : List M := [0,4,34,64,98,128,132,257,291,419,528,532,728,732,789,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_34 : valid 2 B597_2_34 := by
  have h := @closed_of_test B597_2_34 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_35 : List M := [0,4,34,64,128,257,291,355,389,423,528,532,562,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_35 : valid 2 B597_2_35 := by
  have h := @closed_of_test B597_2_35 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_36 : List M := [0,4,34,64,128,257,291,355,389,423,528,532,728,819,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_36 : valid 2 B597_2_36 := by
  have h := @closed_of_test B597_2_36 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_37 : List M := [0,4,34,64,68,128,257,291,355,389,423,528,532,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_37 : valid 2 B597_2_37 := by
  have h := @closed_of_test B597_2_37 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_38 : List M := [0,4,34,64,98,128,257,355,389,528,562,566,728,762,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_38 : valid 2 B597_2_38 := by
  have h := @closed_of_test B597_2_38 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_39 : List M := [0,4,34,38,64,98,102,128,257,355,389,528,728,762,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_39 : valid 2 B597_2_39 := by
  have h := @closed_of_test B597_2_39 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_40 : List M := [0,4,34,64,98,128,257,261,355,389,528,532,728,789,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_40 : valid 2 B597_2_40 := by
  have h := @closed_of_test B597_2_40 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_41 : List M := [0,4,34,64,128,162,257,261,355,389,528,532,728,789,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_41 : valid 2 B597_2_41 := by
  have h := @closed_of_test B597_2_41 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_42 : List M := [0,4,34,64,128,257,261,291,355,389,528,566,728,823,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_42 : valid 2 B597_2_42 := by
  have h := @closed_of_test B597_2_42 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_43 : List M := [0,4,34,64,128,132,257,291,355,389,423,528,562,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_43 : valid 2 B597_2_43 := by
  have h := @closed_of_test B597_2_43 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_44 : List M := [0,4,34,64,98,128,132,257,355,389,528,566,728,766,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_44 : valid 2 B597_2_44 := by
  have h := @closed_of_test B597_2_44 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_45 : List M := [0,10,64,128,228,257,267,331,528,538,666,795,859,923,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_45 : valid 2 B597_2_45 := by
  have h := @closed_of_test B597_2_45 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_46 : List M := [0,4,34,64,128,162,257,261,355,359,389,528,532,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_46 : valid 2 B597_2_46 := by
  have h := @closed_of_test B597_2_46 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_47 : List M := [0,4,34,64,128,132,162,166,257,355,389,528,532,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_47 : valid 2 B597_2_47 := by
  have h := @closed_of_test B597_2_47 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_48 : List M := [0,4,34,38,64,98,102,128,257,355,389,528,562,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_48 : valid 2 B597_2_48 := by
  have h := @closed_of_test B597_2_48 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_49 : List M := [0,4,34,38,64,128,132,166,257,355,389,528,562,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_49 : valid 2 B597_2_49 := by
  have h := @closed_of_test B597_2_49 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_50 : List M := [0,4,34,38,64,128,257,291,355,389,423,528,562,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_50 : valid 2 B597_2_50 := by
  have h := @closed_of_test B597_2_50 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_51 : List M := [0,4,34,38,64,98,102,128,162,257,355,389,528,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_51 : valid 2 B597_2_51 := by
  have h := @closed_of_test B597_2_51 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_52 : List M := [0,4,34,38,64,128,162,257,261,355,359,389,528,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_52 : valid 2 B597_2_52 := by
  have h := @closed_of_test B597_2_52 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_53 : List M := [0,10,64,128,138,257,267,395,528,538,756,766,795,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_53 : valid 2 B597_2_53 := by
  have h := @closed_of_test B597_2_53 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_54 : List M := [0,4,34,64,128,132,257,355,389,528,532,562,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_54 : valid 2 B597_2_54 := by
  have h := @closed_of_test B597_2_54 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_55 : List M := [0,4,34,64,128,132,162,257,355,389,528,562,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_55 : valid 2 B597_2_55 := by
  have h := @closed_of_test B597_2_55 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_56 : List M := [0,4,34,64,128,132,257,355,389,528,562,566,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_56 : valid 2 B597_2_56 := by
  have h := @closed_of_test B597_2_56 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_57 : List M := [0,4,34,64,128,162,257,355,389,528,532,562,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_57 : valid 2 B597_2_57 := by
  have h := @closed_of_test B597_2_57 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_58 : List M := [0,4,34,64,68,128,162,257,355,389,528,532,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_58 : valid 2 B597_2_58 := by
  have h := @closed_of_test B597_2_58 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_59 : List M := [0,4,34,38,64,128,162,257,355,389,528,532,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_59 : valid 2 B597_2_59 := by
  have h := @closed_of_test B597_2_59 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_60 : List M := [0,4,34,64,128,162,257,355,389,528,532,566,728,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_60 : valid 2 B597_2_60 := by
  have h := @closed_of_test B597_2_60 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_61 : List M := [0,4,34,64,128,200,257,291,325,528,532,690,947,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_61 : valid 2 B597_2_61 := by
  have h := @closed_of_test B597_2_61 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_62 : List M := [0,10,64,74,128,257,267,395,528,538,756,795,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_62 : valid 2 B597_2_62 := by
  have h := @closed_of_test B597_2_62 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_63 : List M := [0,10,64,128,257,267,331,395,528,538,756,795,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_63 : valid 2 B597_2_63 := by
  have h := @closed_of_test B597_2_63 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_2_64 : List M := [0,64,128,257,528,1023]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_2_64 : valid 2 B597_2_64 := by
  have h := @closed_of_test B597_2_64 (by decide) (by decide +kernel)
  exact ⟨h, check_sound 2 _ h (by decide +kernel)⟩

private def B597_1_0 : List M := [0,4,16,34,50,64,128,178,256,276,456,513,517,547,581,823,1023]
private def gs597_1_0 : List Group := [
  ([0,1,2,3,4,1,7,8,0,4],B597_2_0,[759,192,320,242,340,887]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_2,[837]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_3,[490,1003,162,675,290,803,0,529,577,641,769,563,691,789,969,68,310]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_4,[631,54,567,20,533]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_5,[182,695]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_12,[597]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_13,[709]),
  ([0,1,2,3,4,1,6,7,0,4],B597_2_14,[434]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_15,[615,38,551]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_16,[460,973,260,773]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_17,[853]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_35,[98,611]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_36,[114]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_37,[132,645]),
  ([0,2,3,2,6,3,7,8,0,6],B597_2_53,[476,80,144,272,472,306,506]),
  ([0,2,3,2,4,3,6,8,0,4],B597_2_45,[384,404,951,438])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_1_0 : valid 3 B597_1_0 := by
  refine ⟨closed_of_test (by decide) (by decide +kernel), ?_⟩
  apply viaGroups gs597_1_0 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_2_0, by decide +kernel⟩,
    ⟨hB597_2_2, by decide +kernel⟩,
    ⟨hB597_2_3, by decide +kernel⟩,
    ⟨hB597_2_4, by decide +kernel⟩,
    ⟨hB597_2_5, by decide +kernel⟩,
    ⟨hB597_2_12, by decide +kernel⟩,
    ⟨hB597_2_13, by decide +kernel⟩,
    ⟨hB597_2_14, by decide +kernel⟩,
    ⟨hB597_2_15, by decide +kernel⟩,
    ⟨hB597_2_16, by decide +kernel⟩,
    ⟨hB597_2_17, by decide +kernel⟩,
    ⟨hB597_2_35, by decide +kernel⟩,
    ⟨hB597_2_36, by decide +kernel⟩,
    ⟨hB597_2_37, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_45, by decide +kernel⟩,trivial⟩

private def B597_1_1 : List M := [0,4,16,34,38,64,102,128,256,472,513,547,675,773,807,1023]
private def gs597_1_1 : List Group := [
  ([0,1,2,3,4,1,7,8,0,4],B597_2_6,[743]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_18,[230]),
  ([0,2,1,3,4,2,8,7,0,4],B597_2_1,[358,192,320,739,837,871]),
  ([0,1,2,3,6,1,7,8,0,6],B597_2_15,[80,144,272,691,789,118,823]),
  ([0,1,3,1,6,3,4,7,0,6],B597_2_53,[931]),
  ([0,2,3,2,6,3,4,8,0,6],B597_2_53,[384,901,935]),
  ([4,3,3,3,6,3,7,8,4,6],B597_2_64,[0,529,577,641,769,517,551,615,985,50,563,20,54,98,611,68,162,132,166,290,803,260,294,506,1019,679,476,989,510])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_1_1 : valid 3 B597_1_1 := by
  refine ⟨closed_of_test (by decide) (by decide +kernel), ?_⟩
  apply viaGroups gs597_1_1 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_2_6, by decide +kernel⟩,
    ⟨hB597_2_18, by decide +kernel⟩,
    ⟨hB597_2_1, by decide +kernel⟩,
    ⟨hB597_2_15, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_64, by decide +kernel⟩,trivial⟩

private def B597_1_2 : List M := [0,4,16,34,64,98,102,128,162,256,472,506,513,675,773,1023]
private def gs597_1_2 : List Group := [
  ([0,1,2,3,4,1,7,8,0,4],B597_2_7,[358,354,192,320,226,739,837]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_8,[871]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_19,[743]),
  ([0,1,2,3,6,1,7,8,0,6],B597_2_38,[80,144,272,114,178,691,789,118]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_39,[230]),
  ([0,1,3,1,6,3,4,7,0,6],B597_2_53,[931]),
  ([0,2,3,2,6,3,4,8,0,6],B597_2_53,[384,901,418,935]),
  ([4,3,3,3,6,3,7,8,4,6],B597_2_64,[0,529,577,641,769,547,611,517,615,985,1019,50,20,68,132,290,260,38,807,166,679,476,510,989])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_1_2 : valid 3 B597_1_2 := by
  refine ⟨closed_of_test (by decide) (by decide +kernel), ?_⟩
  apply viaGroups gs597_1_2 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_2_7, by decide +kernel⟩,
    ⟨hB597_2_8, by decide +kernel⟩,
    ⟨hB597_2_19, by decide +kernel⟩,
    ⟨hB597_2_38, by decide +kernel⟩,
    ⟨hB597_2_39, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_64, by decide +kernel⟩,trivial⟩

private def B597_1_3 : List M := [0,4,16,20,34,64,98,128,256,472,513,517,533,675,773,1023]
private def gs597_1_3 : List Group := [
  ([0,1,2,3,4,1,7,8,0,4],B597_2_12,[871,192,320,739,837]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_40,[226]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_41,[354]),
  ([0,2,1,3,6,2,8,7,0,6],B597_2_4,[631]),
  ([0,2,1,3,6,2,8,7,0,6],B597_2_35,[84]),
  ([0,2,1,3,6,2,8,7,0,6],B597_2_36,[597]),
  ([0,2,1,3,6,2,8,7,0,6],B597_2_3,[148,276,695,80,144,272,114,691,789]),
  ([0,2,1,3,6,2,4,7,0,6],B597_2_3,[931]),
  ([0,2,1,3,6,2,8,7,0,6],B597_2_15,[118]),
  ([0,2,3,2,4,3,6,8,0,4],B597_2_53,[384,661,901,935]),
  ([4,3,3,3,6,3,7,8,4,6],B597_2_64,[0,529,577,641,769,547,611,985,50,68,581,162,132,645,290,260,38,551,54,567,807,506,102,615,679,1019,476,989])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_1_3 : valid 3 B597_1_3 := by
  refine ⟨closed_of_test (by decide) (by decide +kernel), ?_⟩
  apply viaGroups gs597_1_3 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_2_12, by decide +kernel⟩,
    ⟨hB597_2_40, by decide +kernel⟩,
    ⟨hB597_2_41, by decide +kernel⟩,
    ⟨hB597_2_4, by decide +kernel⟩,
    ⟨hB597_2_35, by decide +kernel⟩,
    ⟨hB597_2_36, by decide +kernel⟩,
    ⟨hB597_2_3, by decide +kernel⟩,
    ⟨hB597_2_3, by decide +kernel⟩,
    ⟨hB597_2_15, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_64, by decide +kernel⟩,trivial⟩

private def B597_1_4 : List M := [0,4,16,34,64,102,128,256,472,513,517,547,615,675,773,1023]
private def gs597_1_4 : List Group := [
  ([0,1,2,3,4,1,7,8,0,4],B597_2_9,[230]),
  ([0,2,1,3,4,2,8,7,0,4],B597_2_9,[358]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_6,[743,871,192,320,739,837]),
  ([0,1,2,3,6,1,7,8,0,6],B597_2_42,[80,144,272,691,789,118,631]),
  ([0,2,3,2,6,3,4,8,0,6],B597_2_53,[384,901,935]),
  ([0,1,3,1,6,3,4,7,0,6],B597_2_53,[931]),
  ([4,3,3,3,6,3,7,8,4,6],B597_2_64,[0,529,577,641,769,985,50,563,20,533,98,611,68,581,162,132,645,290,803,260,38,551,807,506,1019,679,476,989,510])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_1_4 : valid 3 B597_1_4 := by
  refine ⟨closed_of_test (by decide) (by decide +kernel), ?_⟩
  apply viaGroups gs597_1_4 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_2_9, by decide +kernel⟩,
    ⟨hB597_2_9, by decide +kernel⟩,
    ⟨hB597_2_6, by decide +kernel⟩,
    ⟨hB597_2_42, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_64, by decide +kernel⟩,trivial⟩

private def B597_1_5 : List M := [0,4,16,34,64,128,178,256,260,276,456,513,517,611,773,1023]
private def gs597_1_5 : List Group := [
  ([0,1,2,3,4,1,7,8,0,4],B597_2_10,[739]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_2,[887,192,320,242,324,837,340]),
  ([0,1,2,3,4,1,6,8,0,4],B597_2_11,[951,384,388,901,404]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_20,[755]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_21,[871]),
  ([0,1,2,3,4,1,6,8,0,4],B597_2_22,[438]),
  ([0,1,2,3,6,1,7,8,0,6],B597_2_23,[506]),
  ([4,2,1,3,6,2,8,7,4,6],B597_2_40,[627]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_43,[310]),
  ([4,1,2,3,7,1,6,8,4,7],B597_2_23,[490,1003,162]),
  ([4,2,1,3,6,2,8,7,4,6],B597_2_3,[182,695,20,533,132,645,460,973,0,529,577,641,769,547,691,789,969,98]),
  ([0,2,1,3,7,2,8,6,0,7],B597_2_3,[476,80,144,272,472]),
  ([4,1,2,3,8,1,6,7,4,8],B597_2_34,[50]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_54,[68,581]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_55,[290]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_49,[38,551,294,807]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_56,[615]),
  ([0,1,3,1,4,3,6,7,0,4],B597_2_45,[867,434])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_1_5 : valid 3 B597_1_5 := by
  refine ⟨closed_of_test (by decide) (by decide +kernel), ?_⟩
  apply viaGroups gs597_1_5 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_2_10, by decide +kernel⟩,
    ⟨hB597_2_2, by decide +kernel⟩,
    ⟨hB597_2_11, by decide +kernel⟩,
    ⟨hB597_2_20, by decide +kernel⟩,
    ⟨hB597_2_21, by decide +kernel⟩,
    ⟨hB597_2_22, by decide +kernel⟩,
    ⟨hB597_2_23, by decide +kernel⟩,
    ⟨hB597_2_40, by decide +kernel⟩,
    ⟨hB597_2_43, by decide +kernel⟩,
    ⟨hB597_2_23, by decide +kernel⟩,
    ⟨hB597_2_3, by decide +kernel⟩,
    ⟨hB597_2_3, by decide +kernel⟩,
    ⟨hB597_2_34, by decide +kernel⟩,
    ⟨hB597_2_54, by decide +kernel⟩,
    ⟨hB597_2_55, by decide +kernel⟩,
    ⟨hB597_2_49, by decide +kernel⟩,
    ⟨hB597_2_56, by decide +kernel⟩,
    ⟨hB597_2_45, by decide +kernel⟩,trivial⟩

private def B597_1_6 : List M := [0,4,16,34,64,102,128,162,256,260,472,510,513,675,773,1023]
private def gs597_1_6 : List Group := [
  ([0,1,2,3,4,1,7,8,0,4],B597_2_1,[743,230,192,320,226,739,324,837]),
  ([0,2,1,3,4,2,8,7,0,4],B597_2_1,[871,358]),
  ([0,1,2,3,6,1,7,8,0,6],B597_2_44,[80,144,272,178,691,276,789,118]),
  ([0,2,3,2,6,3,4,8,0,6],B597_2_53,[384,388,901,418,422,935]),
  ([0,1,3,1,6,3,4,7,0,6],B597_2_53,[931]),
  ([4,3,3,3,6,3,7,8,4,6],B597_2_64,[0,529,577,641,769,547,517,615,985,50,20,98,68,132,290,38,294,807,506,166,679,1019,476,989])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_1_6 : valid 3 B597_1_6 := by
  refine ⟨closed_of_test (by decide) (by decide +kernel), ?_⟩
  apply viaGroups gs597_1_6 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_2_1, by decide +kernel⟩,
    ⟨hB597_2_1, by decide +kernel⟩,
    ⟨hB597_2_44, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_64, by decide +kernel⟩,trivial⟩

private def B597_1_7 : List M := [0,4,16,34,50,64,128,256,310,456,513,611,627,645,1023]
private def gs597_1_7 : List Group := [
  ([4,1,2,3,6,1,7,8,4,6],B597_2_24,[661]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_25,[867,192,320,709,374]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_26,[883]),
  ([0,1,2,3,4,1,6,8,0,4],B597_2_27,[901]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_28,[743]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_29,[887]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_30,[759]),
  ([0,1,3,1,4,3,6,8,0,4],B597_2_45,[951,384,739,755,438]),
  ([4,1,3,1,6,3,7,8,4,6],B597_2_53,[490,1003,290,0,529,577,641,769,547,563,517,823,969,20,98,114,68,132,306,260,38,54,506,615,631,1019,460,973,510]),
  ([4,1,3,1,6,3,7,8,4,6],B597_2_62,[162,679]),
  ([4,1,3,1,6,3,7,8,4,6],B597_2_63,[178,695]),
  ([0,1,2,3,8,1,6,7,0,8],B597_2_15,[80,144,272,472])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_1_7 : valid 3 B597_1_7 := by
  refine ⟨closed_of_test (by decide) (by decide +kernel), ?_⟩
  apply viaGroups gs597_1_7 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_2_24, by decide +kernel⟩,
    ⟨hB597_2_25, by decide +kernel⟩,
    ⟨hB597_2_26, by decide +kernel⟩,
    ⟨hB597_2_27, by decide +kernel⟩,
    ⟨hB597_2_28, by decide +kernel⟩,
    ⟨hB597_2_29, by decide +kernel⟩,
    ⟨hB597_2_30, by decide +kernel⟩,
    ⟨hB597_2_45, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_62, by decide +kernel⟩,
    ⟨hB597_2_63, by decide +kernel⟩,
    ⟨hB597_2_15, by decide +kernel⟩,trivial⟩

private def B597_1_8 : List M := [0,4,16,34,64,128,178,256,276,456,513,547,581,803,1023]
private def gs597_1_8 : List Group := [
  ([0,2,1,3,4,2,8,7,0,4],B597_2_13,[759,192,320,242,867,340]),
  ([0,1,2,3,4,1,6,8,0,4],B597_2_31,[438]),
  ([0,1,2,3,6,1,7,8,0,6],B597_2_32,[506,80,144,272,819,472]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_33,[871]),
  ([0,1,2,3,6,1,7,8,0,6],B597_2_34,[476]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_41,[597]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_3,[310,490,823,1003,50,563,162,675,0,529,577,641,769,691,517,789,969,68,290]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_46,[182]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_47,[807]),
  ([4,2,1,3,7,2,6,8,4,7],B597_2_32,[460,973,20,260]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_57,[98,611]),
  ([4,1,2,3,0,1,8,6,4,0],B597_2_13,[384,931,709,404]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_58,[132]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_59,[38,551]),
  ([4,1,2,3,6,1,7,8,4,6],B597_2_60,[615]),
  ([0,1,2,3,4,1,6,7,0,4],B597_2_61,[947]),
  ([4,2,1,3,0,2,7,6,4,0],B597_2_61,[853]),
  ([0,2,1,3,4,2,6,7,0,4],B597_2_11,[434,837])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_1_8 : valid 3 B597_1_8 := by
  refine ⟨closed_of_test (by decide) (by decide +kernel), ?_⟩
  apply viaGroups gs597_1_8 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_2_13, by decide +kernel⟩,
    ⟨hB597_2_31, by decide +kernel⟩,
    ⟨hB597_2_32, by decide +kernel⟩,
    ⟨hB597_2_33, by decide +kernel⟩,
    ⟨hB597_2_34, by decide +kernel⟩,
    ⟨hB597_2_41, by decide +kernel⟩,
    ⟨hB597_2_3, by decide +kernel⟩,
    ⟨hB597_2_46, by decide +kernel⟩,
    ⟨hB597_2_47, by decide +kernel⟩,
    ⟨hB597_2_32, by decide +kernel⟩,
    ⟨hB597_2_57, by decide +kernel⟩,
    ⟨hB597_2_13, by decide +kernel⟩,
    ⟨hB597_2_58, by decide +kernel⟩,
    ⟨hB597_2_59, by decide +kernel⟩,
    ⟨hB597_2_60, by decide +kernel⟩,
    ⟨hB597_2_61, by decide +kernel⟩,
    ⟨hB597_2_61, by decide +kernel⟩,
    ⟨hB597_2_11, by decide +kernel⟩,trivial⟩

private def B597_1_9 : List M := [0,4,16,34,50,64,102,128,256,472,513,675,773,1023]
private def gs597_1_9 : List Group := [
  ([0,1,2,3,4,1,7,8,0,4],B597_2_48,[230]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_49,[358]),
  ([0,1,2,3,6,1,7,8,0,6],B597_2_15,[823,80,144,272,691,789,118]),
  ([0,2,1,3,4,2,8,7,0,4],B597_2_15,[743,192,320,739,837]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_50,[871]),
  ([0,2,1,3,6,2,8,7,0,6],B597_2_15,[114]),
  ([0,1,2,3,6,1,7,8,0,6],B597_2_38,[178]),
  ([0,1,2,3,6,1,7,8,0,6],B597_2_60,[306]),
  ([0,1,3,1,4,3,6,7,0,4],B597_2_62,[931]),
  ([0,2,3,2,6,3,4,8,0,6],B597_2_53,[384,901,935]),
  ([4,3,3,3,6,3,7,8,4,6],B597_2_64,[0,529,577,641,769,547,563,517,615,985,20,98,68,162,132,290,260,38,807,506,54,679,1019,476,989,510])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_1_9 : valid 3 B597_1_9 := by
  refine ⟨closed_of_test (by decide) (by decide +kernel), ?_⟩
  apply viaGroups gs597_1_9 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_2_48, by decide +kernel⟩,
    ⟨hB597_2_49, by decide +kernel⟩,
    ⟨hB597_2_15, by decide +kernel⟩,
    ⟨hB597_2_15, by decide +kernel⟩,
    ⟨hB597_2_50, by decide +kernel⟩,
    ⟨hB597_2_15, by decide +kernel⟩,
    ⟨hB597_2_38, by decide +kernel⟩,
    ⟨hB597_2_60, by decide +kernel⟩,
    ⟨hB597_2_62, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_64, by decide +kernel⟩,trivial⟩

private def B597_1_10 : List M := [0,4,16,34,64,102,128,256,290,472,513,675,773,1023]
private def gs597_1_10 : List Group := [
  ([0,1,2,3,4,1,7,8,0,4],B597_2_51,[230]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_7,[358,192,320,739,354,837]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_52,[743]),
  ([0,1,2,3,4,1,7,8,0,4],B597_2_8,[871]),
  ([0,1,2,3,6,1,7,8,0,6],B597_2_60,[80,144,272,691,306,789,118]),
  ([0,2,3,2,6,3,4,8,0,6],B597_2_53,[384,418,901,935]),
  ([0,1,3,1,6,3,4,7,0,6],B597_2_53,[931]),
  ([4,3,3,3,6,3,7,8,4,6],B597_2_64,[0,529,577,641,769,547,803,517,615,985,50,20,98,68,162,132,260,38,807,506,679,1019,294,476,989,510])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem hB597_1_10 : valid 3 B597_1_10 := by
  refine ⟨closed_of_test (by decide) (by decide +kernel), ?_⟩
  apply viaGroups gs597_1_10 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_2_51, by decide +kernel⟩,
    ⟨hB597_2_7, by decide +kernel⟩,
    ⟨hB597_2_52, by decide +kernel⟩,
    ⟨hB597_2_8, by decide +kernel⟩,
    ⟨hB597_2_60, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_53, by decide +kernel⟩,
    ⟨hB597_2_64, by decide +kernel⟩,trivial⟩

private def gs597_0_0 : List Group := [
  ([0,1,2,5,4,1,6,8,9,0],B597_1_0,[671,197,402,640,668]),
  ([4,1,3,5,6,1,7,8,9,4],B597_1_1,[542,10,18,0,3,5,9,17,65,129,257,275,513,541,993,6,12,20,68,132,143,260,278,516,996,997]),
  ([4,1,3,5,6,1,7,8,9,4],B597_1_2,[994,130,258]),
  ([4,3,1,5,6,3,7,9,8,4],B597_1_1,[282,24]),
  ([4,3,1,5,6,3,7,9,8,4],B597_1_2,[1000,136,520]),
  ([4,1,2,5,6,1,7,8,9,4],B597_1_3,[85]),
  ([4,1,3,5,6,1,7,8,9,4],B597_1_4,[155]),
  ([0,1,2,5,4,1,7,8,9,0],B597_1_5,[581]),
  ([4,1,3,5,6,1,7,8,9,4],B597_1_6,[1003]),
  ([0,2,3,5,8,2,9,6,7,0],B597_1_6,[1020]),
  ([0,2,3,5,4,2,6,7,9,0],B597_1_7,[343,320,325,384,395,768,796,798]),
  ([4,3,1,5,0,3,9,8,7,4],B597_1_7,[605]),
  ([0,3,2,5,4,3,7,6,9,0],B597_1_7,[411]),
  ([0,1,2,5,4,1,6,8,9,0],B597_1_8,[651]),
  ([4,1,3,5,6,1,7,8,9,4],B597_1_9,[66,71]),
  ([4,1,3,5,6,1,7,8,9,4],B597_1_10,[514]),
  ([4,3,1,5,6,3,7,9,8,4],B597_1_9,[72,77]),
  ([4,3,1,5,6,3,7,9,8,4],B597_1_10,[264]),
  ([4,2,1,5,0,2,8,6,7,4],B597_1_0,[786]),
  ([0,2,3,5,8,2,9,6,7,0],B597_1_1,[80,144,272,528,1008,1010]),
  ([4,1,3,5,0,1,8,9,7,4],B597_1_7,[192,203,338,576,604,207])]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem verifiedSearch : Safe 4 initial := by
  apply viaGroups gs597_0_0 (by decide) (by decide +kernel)
  exact ⟨⟨hB597_1_0, by decide +kernel⟩,
    ⟨hB597_1_1, by decide +kernel⟩,
    ⟨hB597_1_2, by decide +kernel⟩,
    ⟨hB597_1_1, by decide +kernel⟩,
    ⟨hB597_1_2, by decide +kernel⟩,
    ⟨hB597_1_3, by decide +kernel⟩,
    ⟨hB597_1_4, by decide +kernel⟩,
    ⟨hB597_1_5, by decide +kernel⟩,
    ⟨hB597_1_6, by decide +kernel⟩,
    ⟨hB597_1_6, by decide +kernel⟩,
    ⟨hB597_1_7, by decide +kernel⟩,
    ⟨hB597_1_7, by decide +kernel⟩,
    ⟨hB597_1_7, by decide +kernel⟩,
    ⟨hB597_1_8, by decide +kernel⟩,
    ⟨hB597_1_9, by decide +kernel⟩,
    ⟨hB597_1_10, by decide +kernel⟩,
    ⟨hB597_1_9, by decide +kernel⟩,
    ⟨hB597_1_10, by decide +kernel⟩,
    ⟨hB597_1_0, by decide +kernel⟩,
    ⟨hB597_1_1, by decide +kernel⟩,
    ⟨hB597_1_7, by decide +kernel⟩,trivial⟩

end PEqualNP.Outside.Bowtie597

theorem PEqualNP.Outside.L_meta_597 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → ∀ A : Finset ℕ, (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → 5 ≤ A.card :=
  PEqualNP.Outside.Bowtie597.from_safe PEqualNP.Outside.Bowtie597.verifiedSearch
