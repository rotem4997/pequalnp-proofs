import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7449_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves

def gv (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [gv g w]) w

theorem wires_run (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [gv g w]) := rfl

theorem run_app (as bs : List Gate) (w : List Bool) : run (as ++ bs) w = run bs (run as w) := by
  simp [run, List.foldl_append]

theorem run_len : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length
  | [], w => by simp [run_nil]
  | g :: gs, w => by rw [run_cons, run_len gs]; simp; omega

theorem snoc_getD (a : List Bool) (v : Bool) (i : ℕ) :
    (a ++ [v]).getD i false
      = if i < a.length then a.getD i false else if i = a.length then v else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 1 ≤ i - a.length := by omega
    rw [List.getElem?_eq_none (by simpa using this)]
    rfl

theorem getD_big (a : List Bool) (i : ℕ) (h : a.length ≤ i) : a.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem run_low : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false
  | [], w, i, _ => by simp [run_nil]
  | g :: gs, w, i, h => by
    rw [run_cons, run_low gs _ i (by simp; omega), snoc_getD, if_pos h]

def Hop (rel : Bool → Bool → Prop) (g : Gate) : Prop :=
  ∀ f f' : ℕ → Bool, (∀ r, rel (f r) (f' r)) →
    rel (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map f'))

theorem hop_eq (g : Gate) : Hop (fun a b => a = b) g := by
  intro f f' h
  have : f = f' := funext h
  rw [this]

theorem hop_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    Hop (fun a b => a = true → b = true) g := by
  intro f f' h
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    rintro H b ⟨i, hi, rfl⟩
    exact h i (H _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hb⟩

theorem sim (rel : Bool → Bool → Prop) (h00 : rel false false) (n m p : ℕ) (hp : p < n + m) :
    ∀ (post : List Gate) (U V : List Bool), U.length = V.length + 1 → n + m ≤ V.length →
      (∀ g ∈ post, Hop rel g) →
      (∀ r, rel (U.getD r false) (V.getD (eraseRedirect n m p r) false)) →
      ∀ r, rel ((run post U).getD r false)
        ((run (post.map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)) V).getD
          (eraseRedirect n m p r) false)
  | [], U, V, _, _, _, h => by simpa [run_nil] using h
  | g :: gs, U, V, hl, hK, hh, h => by
    rw [List.map_cons, run_cons, run_cons]
    refine sim rel h00 n m p hp gs _ _ (by simp; omega) (by simp; omega)
      (fun g' hg' => hh g' (List.mem_cons_of_mem _ hg')) ?_
    have hab : rel (gv g U) (gv ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ V) := by
      have := hh g List.mem_cons_self (fun i => U.getD i false)
        (fun i => V.getD (eraseRedirect n m p i) false) h
      simpa [gv, List.map_map, Function.comp_def] using this
    intro r
    rw [snoc_getD, snoc_getD]
    have hr := h r
    unfold eraseRedirect at hr ⊢
    by_cases h1 : r < U.length
    · rw [if_pos h1]
      split_ifs at hr ⊢ <;> first | exact hr | omega
    · rw [if_neg h1]
      split_ifs <;> first | exact hab | exact h00 | omega

theorem mono : ∀ (gs : List Gate) (U V : List Bool), U.length = V.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ r, U.getD r false = true → V.getD r false = true) →
    ∀ r, (run gs U).getD r false = true → (run gs V).getD r false = true
  | [], U, V, _, _, h => by simpa [run_nil] using h
  | g :: gs, U, V, hl, hh, h => by
    rw [run_cons, run_cons]
    refine mono gs _ _ (by simp; omega) (fun g' hg' => hh g' (List.mem_cons_of_mem _ hg')) ?_
    intro r
    rw [snoc_getD, snoc_getD, hl]
    split_ifs
    · exact h r
    · exact hop_le g (hh g List.mem_cons_self) _ _ h
    · exact id

theorem ofFn_getD (z : Fin 14 → Bool) (r : ℕ) :
    (List.ofFn z).getD r false = if h : r < 14 then z ⟨r, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

theorem erase_eq (n : ℕ) (C : Circuit) (p : ℕ) (pre post : List Gate) (gm : Gate)
    (hC : C.gates = pre ++ gm :: post) :
    eraseGate n C pre.length p =
      { gates := pre ++ post.map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n pre.length p)⟩)
        output := eraseRedirect n pre.length p C.output } := by
  unfold eraseGate
  rw [if_pos (by rw [hC]; simp), hC]
  simp

theorem erase_rel (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b) (n : ℕ) (C : Circuit)
    (p : ℕ) (pre post : List Gate) (gm : Gate) (hC : C.gates = pre ++ gm :: post)
    (hp : p < n + pre.length) (x : List Bool) (hx : x.length = n)
    (hh : ∀ g ∈ post, Hop rel g)
    (hv : rel (gv gm (run pre x)) ((run pre x).getD p false)) :
    rel (C.eval x) ((eraseGate n C pre.length p).eval x) := by
  rw [erase_eq n C p pre post gm hC]
  unfold Circuit.eval
  rw [wires_run, wires_run, hC]
  simp only []
  rw [run_app, run_cons, run_app]
  have hA : (run pre x).length = n + pre.length := by rw [run_len, hx]
  refine sim rel (hrefl false) n pre.length p hp post _ _ (by simp) (by omega) hh ?_ C.output
  intro r
  rw [snoc_getD]
  unfold eraseRedirect
  by_cases h1 : r = n + pre.length
  · rw [if_neg (by omega), if_pos (by omega), if_pos h1]
    exact hv
  · by_cases h2 : r < n + pre.length
    · rw [if_pos (by omega), if_neg h1, if_neg (by omega)]
      exact hrefl _
    · rw [if_neg (by omega), if_neg (by omega), if_neg h1, if_pos (by omega),
        getD_big _ _ (by omega)]
      exact hrefl _

theorem wire_low (n : ℕ) (C : Circuit) (pre post : List Gate) (gm : Gate)
    (hC : C.gates = pre ++ gm :: post) (x : List Bool) (hx : x.length = n) (q : ℕ)
    (hq : q < n + pre.length) :
    (C.wires x).getD q false = (run pre x).getD q false := by
  have hA : (run pre x).length = n + pre.length := by rw [run_len, hx]
  rw [wires_run, hC, run_app, run_cons, run_low _ _ _ (by simp; omega), snoc_getD,
    if_pos (by omega)]

theorem maxzero (F : (Fin 14 → Bool) → Bool) (z : Fin 14 → Bool) (hz : F z = false) :
    ∃ y, z ≤ y ∧ F y = false ∧ ∀ u, y ≤ u → F u = false → u = y := by
  obtain ⟨y, hzy, hy⟩ := Set.Finite.exists_le_maximal (Set.toFinite {u | F u = false}) hz
  exact ⟨y, hzy, hy.1, fun u hyu hu => le_antisymm (hy.2 hu hyu) hyu⟩

theorem main (C : Circuit) (m : ℕ) (b : Fin 2) (F : (Fin 14 → Bool) → Bool)
    (hAO : PEqualNP.TopForm.IsAO2 14 C) (hF : circuitFun 14 C = F) (hm : m < C.size)
    (hop : (gateAt C m).op = GateOp.and)
    (hyp : ∀ z : Fin 14 → Bool, (F z = false ∧ ∀ u : Fin 14 → Bool, z ≤ u → F u = false → u = z) →
      PEqualNP.CleanedNonEdge.wireVal 14 C (PEqualNP.TopForm.opnd C m b) z = true →
      PEqualNP.CleanedNonEdge.wireVal 14 C (PEqualNP.TopForm.opnd C m (1 - b)) z = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 14 D ∧ circuitFun 14 D = F ∧ D.size < C.size := by
  obtain ⟨hA, hR, h2⟩ := hAO
  have hm' : m < C.gates.length := hm
  obtain ⟨pre, gm, post, hC, hlen⟩ : ∃ pre gm post, C.gates = pre ++ gm :: post ∧
      pre.length = m :=
    ⟨C.gates.take m, C.gates[m], C.gates.drop (m + 1), by simp, by simp; omega⟩
  subst hlen
  have hgm : gateAt C pre.length = gm := by simp [gateAt, hC]
  rw [hgm] at hop
  have hmem : gm ∈ C.gates := by rw [hC]; simp
  obtain ⟨a0, a1, hin⟩ : ∃ a0 a1, gm.inputs = [a0, a1] := by
    have := h2 gm hmem
    match hi : gm.inputs, this with
    | [a0, a1], _ => exact ⟨a0, a1, rfl⟩
  have hRm := hR pre.length hm'
  rw [hgm, hin] at hRm
  have ha0 : a0 < 14 + pre.length := hRm a0 (by simp)
  have ha1 : a1 < 14 + pre.length := hRm a1 (by simp)
  have hgv : ∀ w : List Bool, gv gm w = (w.getD a0 false && w.getD a1 false) := by
    intro w
    simp [gv, hop, hin, GateOp.eval]
  have hopnd : ∀ c : Fin 2, PEqualNP.TopForm.opnd C pre.length c = if c = 0 then a0 else a1 := by
    intro c
    fin_cases c <;> simp [PEqualNP.TopForm.opnd, hgm, hin]
  have hp : PEqualNP.TopForm.opnd C pre.length b < 14 + pre.length := by
    rw [hopnd]; split_ifs <;> assumption
  have hq : PEqualNP.TopForm.opnd C pre.length (1 - b) < 14 + pre.length := by
    rw [hopnd]; split_ifs <;> assumption
  have hgv2 : ∀ w : List Bool, gv gm w = (w.getD (PEqualNP.TopForm.opnd C pre.length b) false &&
      w.getD (PEqualNP.TopForm.opnd C pre.length (1 - b)) false) := by
    intro w
    rw [hgv, hopnd, hopnd]
    fin_cases b
    · simp
    · simp [Bool.and_comm]
  generalize PEqualNP.TopForm.opnd C pre.length b = p at *
  generalize PEqualNP.TopForm.opnd C pre.length (1 - b) = q at *
  have hpostAO : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    exact hA g (by rw [hC]; simp [hg])
  have hD := erase_eq 14 C p pre post gm hC
  have hle : ∀ z : Fin 14 → Bool, circuitFun 14 C z = true →
      circuitFun 14 (eraseGate 14 C pre.length p) z = true := by
    intro z
    refine erase_rel (fun a b => a = true → b = true) (fun _ => id) 14 C p pre post gm hC hp
      (List.ofFn z) (by simp) (fun g hg => hop_le g (hpostAO g hg)) ?_
    rw [hgv2]
    intro h
    simp only [Bool.and_eq_true] at h
    exact h.1
  have heq : ∀ z : Fin 14 → Bool, (F z = false ∧ ∀ u : Fin 14 → Bool, z ≤ u → F u = false → u = z) →
      circuitFun 14 C z = circuitFun 14 (eraseGate 14 C pre.length p) z := by
    intro z hz
    refine erase_rel (fun a b => a = b) (fun _ => rfl) 14 C p pre post gm hC hp
      (List.ofFn z) (by simp) (fun g _ => hop_eq g) ?_
    rw [hgv2]
    have h1 := hyp z hz
    unfold PEqualNP.CleanedNonEdge.wireVal at h1
    rw [wire_low 14 C pre post gm hC _ (by simp) p hp,
      wire_low 14 C pre post gm hC _ (by simp) q hq] at h1
    cases hpv : (run pre (List.ofFn z)).getD p false
    · simp
    · rw [h1 hpv]; rfl
  have hDAO : ∀ g ∈ (eraseGate 14 C pre.length p).gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    rw [hD] at hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hA g (by rw [hC]; simp [hg])
    · exact hpostAO g' hg'
  have hmonoD : ∀ z y : Fin 14 → Bool, z ≤ y →
      circuitFun 14 (eraseGate 14 C pre.length p) z = true →
      circuitFun 14 (eraseGate 14 C pre.length p) y = true := by
    intro z y hzy
    unfold circuitFun Circuit.eval
    rw [wires_run, wires_run]
    refine mono _ _ _ (by simp) hDAO ?_ _
    intro r
    rw [ofFn_getD, ofFn_getD]
    split_ifs
    · exact fun h => le_antisymm le_top (h ▸ hzy _)
    · exact id
  refine ⟨eraseGate 14 C pre.length p, ?_, ?_, ?_, ?_⟩
  · intro g hg
    refine ⟨?_, ?_⟩
    · rcases hDAO g hg with h | h <;> simp [h]
    · rw [hD] at hg
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g', hg', rfl⟩
      · exact le_of_eq (h2 g (by rw [hC]; simp [hg]))
      · simpa using le_of_eq (h2 g' (by rw [hC]; simp [hg']))
  · intro j hj i hi
    rw [hD] at hj hi
    simp only [gateAt] at hi
    simp only [List.length_append, List.length_map] at hj
    by_cases hjl : j < pre.length
    · have e : (pre ++ List.map (fun g : Gate =>
          (⟨g.op, g.inputs.map (eraseRedirect 14 pre.length p)⟩ : Gate)) post).getD j
          ⟨GateOp.or, []⟩ = gateAt C j := by
        simp [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append, hjl]
      rw [e] at hi
      exact hR j (by rw [hC]; simp; omega) i hi
    · have hk : j - pre.length < post.length := by omega
      have e : (pre ++ List.map (fun g : Gate =>
          (⟨g.op, g.inputs.map (eraseRedirect 14 pre.length p)⟩ : Gate)) post).getD j
          ⟨GateOp.or, []⟩ = ⟨(post[j - pre.length]).op,
            (post[j - pre.length]).inputs.map (eraseRedirect 14 pre.length p)⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append, hjl, hk]
      rw [e] at hi
      simp only [List.mem_map] at hi
      obtain ⟨i', hi', rfl⟩ := hi
      have e2 : gateAt C (j + 1) = post[j - pre.length] := by
        have e3 : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        have e4 : ¬ j + 1 < pre.length := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append, e3, e4, hk]
      have := hR (j + 1) (by rw [hC]; simp; omega) i' (by rw [e2]; exact hi')
      unfold eraseRedirect
      split_ifs <;> omega
  · funext z
    have hCz : circuitFun 14 C z = F z := by rw [hF]
    cases hFz : F z
    · obtain ⟨y, hzy, hy0, hymax⟩ := maxzero F z hFz
      have h1 := heq y ⟨hy0, hymax⟩
      have hCy : circuitFun 14 C y = F y := by rw [hF]
      rw [hCy, hy0] at h1
      cases hDz : circuitFun 14 (eraseGate 14 C pre.length p) z
      · rfl
      · have h3 := hmonoD z y hzy hDz
        rw [h3] at h1
        cases h1
    · exact hle z (by rw [hCz, hFz])
  · rw [hD]
    simp [Circuit.size, hC]


end PEqualNP.Outside.L_meta_7449_aux

theorem PEqualNP.Outside.L_meta_7449 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin (2 : ℕ)),   have x4 : (Fin (14 : ℕ) → Bool) → Bool := fun (x4 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ∈ PEqualNP.CircuitLowerBounds.fanoLines x6 ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true);   have x5 : (Fin (14 : ℕ) → Bool) → Prop := fun (x5 : Fin (14 : ℕ) → Bool) => x4 x5 = Bool.false ∧ ∀ (x6 : Fin (14 : ℕ) → Bool), x5 ≤ x6 → x4 x6 = Bool.false → x6 = x5;   have x6 : ℕ → Fin (2 : ℕ) → (Fin (14 : ℕ) → Bool) → Bool := fun (x6 : ℕ) (x7 : Fin (2 : ℕ)) (x8 : Fin (14 : ℕ) → Bool) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x6 x7) x8;   PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = x4 → x2 < x1.size → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x11 : Fin (14 : ℕ) → Bool), x5 x11 → x6 x2 x3 x11 = Bool.true → x6 x2 ((1 : Fin (2 : ℕ)) - x3) x11 = Bool.true) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x12 ∧ PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x12 = x4 ∧ x12.size < x1.size := by
  intro x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5
  exact PEqualNP.Outside.L_meta_7449_aux.main x1 x2 x3 x4 h1 h2 h3 h4 h5
