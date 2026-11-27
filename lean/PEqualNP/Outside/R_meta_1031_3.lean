import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1031_3
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D →
          PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
          C.size ≤ D.size) ∧
        PEqualNP.EdgeOwnership.HasStarProfile n G C)
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D →
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        C.size ≤ D.size) →
      PEqualNP.EdgeOwnership.HasStarProfile n G C →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C' ∧
        PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        C'.size ≤ C.size ∧
        PEqualNP.EdgeOwnership.HasStarProfile n G C' ∧
        ∀ j : ℕ, j < C'.gates.length →
          (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ u v : Fin n, G.Adj u v ∧ PEqualNP.EdgeOwnership.Owns n C' j u v) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.EdgeOwnership in
  (intro n G _ htf hc4
   obtain ⟨C0, hM0, hF0, hL0, hS0⟩ := h1 n G htf hc4
   obtain ⟨C, hM, hF, hsz, hS, hN⟩ := h2 n G C0 htf hc4 hM0 hF0 hL0 hS0
   have key : ∀ x : Fin n → Bool, graphFun G ∅ x = true ↔
       ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true := by
     intro x
     show (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
       decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
     simp
   have hstep : ∀ (cs : List (List ℕ)) (g : Gate), coneStep n cs g = cs ++
       [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
         (fun w => (w - n) :: cs.getD (w - n) [])] := fun _ _ => rfl
   have hlen : ∀ (gs : List Gate) (cs : List (List ℕ)),
       (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
     intro gs
     induction gs with
     | nil => intro cs; simp
     | cons g gs ih =>
       intro cs
       rw [List.foldl_cons, ih, hstep]
       simp
       omega
   have hstlt : ∀ (cs : List (List ℕ)) (g : Gate) (m : ℕ), m < cs.length →
       (coneStep n cs g).getD m [] = cs.getD m [] := by
     intro cs g m hm
     rw [hstep]
     simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
   have hstlast : ∀ (cs : List (List ℕ)) (g : Gate),
       (coneStep n cs g).getD cs.length [] =
         (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
           (fun w => (w - n) :: cs.getD (w - n) []) := by
     intro cs g
     rw [hstep]
     simp [List.getD_eq_getElem?_getD]
   have hgetlt : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ), k < cs.length →
       (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
     intro gs
     induction gs with
     | nil => intro cs k hk; rfl
     | cons g gs ih =>
       intro cs k hk
       simp only [List.foldl_cons]
       rw [ih (coneStep n cs g) k (by rw [hstep]; simp; omega)]
       exact hstlt cs g k hk
   have hsplit : ∀ (gs : List Gate) (j : ℕ) (hj : j < gs.length),
       ∃ (pre post : List Gate) (gj : Gate),
         gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
     intro gs j hj
     refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
     rw [List.cons_getElem_drop_succ, List.take_append_drop]
   have hgat : ∀ (k : ℕ) (hk : k < C.gates.length), gateAt C k = C.gates[k] := by
     intro k hk
     show C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k]
     simp [List.getD_eq_getElem?_getD, hk]
   have hiff : ∀ (i k : ℕ), k < C.gates.length →
       (InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
         (i = w - n ∨ InCone n C i (w - n))) := by
     intro i k hk
     obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := hsplit C.gates k hk
     have hga : gateAt C k = gk := by rw [hgat k hk]; exact hgk
     rw [hga]
     have hc : cones n C =
         post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
       show List.foldl (coneStep n) [] C.gates = _
       rw [hgs, List.foldl_append, List.foldl_cons]
     have hl0 : (pre.foldl (coneStep n) []).length = k := by
       rw [hlen]; simp [hpre_len]
     have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
       rw [hstep]
       simp [hl0]
     have e1 : (cones n C).getD k [] =
         (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
           (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
       rw [hc, hgetlt post _ k (by omega)]
       have h := hstlast (pre.foldl (coneStep n) []) gk
       rw [hl0] at h
       exact h
     have e2 : ∀ m, m < k →
         (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
       intro m hm
       rw [hc, hgetlt post _ m (by omega)]
       exact hstlt _ gk m (by omega)
     show (i ∈ (cones n C).getD k []) ↔ ∃ w ∈ gk.inputs, n ≤ w ∧ w < n + k ∧
       (i = w - n ∨ i ∈ (cones n C).getD (w - n) [])
     rw [e1]
     simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
     constructor
     · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
       refine ⟨w, hw, hn, hlt, ?_⟩
       rcases h with h | h
       · exact Or.inl h
       · right
         rw [e2 (w - n) (by omega)]
         exact h
     · rintro ⟨w, hw, hn, hlt, h⟩
       refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
       rcases h with h | h
       · exact Or.inl h
       · right
         rw [← e2 (w - n) (by omega)]
         exact h
   have hclt : ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
     intro k
     induction k using Nat.strong_induction_on with
     | _ k ih =>
       intro hk i hi
       obtain ⟨w, _, hn, hlt, h⟩ := (hiff i k hk).mp hi
       rcases h with h | h
       · omega
       · have := ih (w - n) (by omega) (by omega) i h
         omega
   have hRlt : ∀ a b : ℕ, Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : Gate),
       b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) a b → a < b := by
     intro a b h
     induction h with
     | single h => exact h.1
     | tail _ h ih => exact lt_trans ih h.1
   have hto : ∀ k, k < C.gates.length → ∀ i, InCone n C i k →
       Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : Gate),
         b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + i) (n + k) := by
     intro k
     induction k using Nat.strong_induction_on with
     | _ k ih =>
       intro hk i hi
       obtain ⟨w, hw, hn, hlt, h⟩ := (hiff i k hk).mp hi
       have hstep : w < n + k ∧ ∃ (k' : ℕ) (h : Gate),
           n + k = n + k' ∧ C.gates[k']? = some h ∧ w ∈ h.inputs :=
         ⟨hlt, k, C.gates[k], rfl, List.getElem?_eq_getElem hk, by rw [← hgat k hk]; exact hw⟩
       rcases h with h | h
       · have e : n + i = w := by omega
         rw [e]
         exact Relation.TransGen.single hstep
       · have h' := ih (w - n) (by omega) (by omega) i h
         have e : n + (w - n) = w := by omega
         rw [e] at h'
         exact Relation.TransGen.tail h' hstep
   have hfrom : ∀ (i b : ℕ), Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : Gate),
       b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + i) b →
       ∀ k, b = n + k → k < C.gates.length ∧ InCone n C i k := by
     intro i b h
     induction h with
     | single h =>
       intro k hb
       obtain ⟨hlt, k', g', hb', hg', hmem⟩ := h
       have hkk : k' = k := by omega
       subst hkk
       obtain ⟨hk, hgk⟩ := List.getElem?_eq_some_iff.mp hg'
       refine ⟨hk, (hiff i k' hk).mpr ⟨n + i, ?_, by omega, by omega, Or.inl (by omega)⟩⟩
       rw [hgat k' hk, hgk]
       exact hmem
     | tail hprev h ih =>
       intro k hb
       obtain ⟨hlt, k', g', hb', hg', hmem⟩ := h
       have hc1 := hRlt _ _ hprev
       have hkk : k' = k := by omega
       subst hkk
       obtain ⟨hk, hgk⟩ := List.getElem?_eq_some_iff.mp hg'
       rename_i c d
       obtain ⟨_, hin2⟩ := ih (c - n) (by omega)
       refine ⟨hk, (hiff i k' hk).mpr ⟨c, ?_, by omega, by omega, Or.inr hin2⟩⟩
       rw [hgat k' hk, hgk]
       exact hmem
   refine ⟨C, ?_, ?_, ?_, ?_⟩
   · intro g hg
     exact ⟨(Set.mem_insert_iff.mp (hM g hg).1).imp id Set.mem_singleton_iff.mp, (hM g hg).2⟩
   · intro x
     have h := congrFun hF x
     refine Bool.eq_iff_iff.mpr ?_
     refine Iff.trans ?_ (@decide_eq_true_iff _ _).symm
     rw [← key x, ← h]
     exact Iff.rfl
   · intro D hD1 hD2
     have hMD : Monotone2 D := fun g hg =>
       ⟨Set.mem_insert_iff.mpr ((hD1 g hg).1.imp id Set.mem_singleton_iff.mpr), (hD1 g hg).2⟩
     have hFD : circuitFun n D = graphFun G ∅ := by
       funext x
       show D.eval (List.ofFn x) = graphFun G ∅ x
       rw [hD2 x]
       refine Bool.eq_iff_iff.mpr ?_
       exact (@decide_eq_true_iff _ _).trans (key x).symm
     exact le_trans hsz (hL0 D hMD hFD)
   · intro t g hg hop
     obtain ⟨ht, hgt⟩ := List.getElem?_eq_some_iff.mp hg
     have hga : gateAt C t = g := by rw [hgat t ht]; exact hgt
     have hopt : (gateAt C t).op = GateOp.and := by rw [hga]; exact hop
     obtain ⟨u0, v0, hadj0, hO0⟩ := hN t ht hopt
     have hfw : ∀ u v : Fin n, Owns n C t u v →
         ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧
           ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
             Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : Gate),
               b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) →
             (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false
               = false) := by
       intro u v hO
       obtain ⟨_, _, hval, hlow⟩ := hO
       refine ⟨hval, ?_⟩
       intro t' g' hg' hop' htr
       obtain ⟨_, hin⟩ := hfrom t' (n + t) htr t rfl
       have hlt' : t' < t := hclt t ht t' hin
       obtain ⟨ht', hgt'⟩ := List.getElem?_eq_some_iff.mp hg'
       have hga' : gateAt C t' = g' := by rw [hgat t' ht']; exact hgt'
       exact hlow t' hlt' hin (by rw [hga']; exact hop')
     have hbw : ∀ u v : Fin n,
         ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧
           ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
             Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : Gate),
               b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) →
             (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false
               = false) → Owns n C t u v := by
       intro u v hO
       refine ⟨ht, hopt, hO.1, ?_⟩
       intro i hi hin hopi
       have hilen : i < C.gates.length := lt_trans hi ht
       exact hO.2 i C.gates[i] (List.getElem?_eq_getElem hilen)
         (by rw [← hgat i hilen]; exact hopi) (hto t ht i hin)
     rcases hS t ht hopt with hnone | ⟨c, hc⟩
     · exact absurd hO0 (hnone u0 v0 hadj0)
     · exact ⟨c, ⟨u0, v0, hadj0, hfw u0 v0 hO0⟩, fun u v hadj hO => hc u v hadj (hbw u v hO)⟩)
