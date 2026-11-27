import Mathlib
import PEqualNP.Defs

-- Peel the output gate of a circuit for one of the seven free-OR patterns.
-- Fan-in below two cannot meet the rows. A binary gate leaves the same rows
-- on two earlier wires, so the size bound is the bound on those wires plus one.

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3803_1
    (orW : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ) (s : List ℕ),
      s ∈ ([[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]] : List (List ℕ)) →
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 C →
      a < 27 + C.size → b < 27 + C.size →
      (∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l →
        ((C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l} ++
          [s.any fun i => (PEqualNP.GenericRejection.incidenceInput {p} {l}).getD i false])).getD a false ||
          (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l} ++
            [s.any fun i => (PEqualNP.GenericRejection.incidenceInput {p} {l}).getD i false])).getD b false) = true) →
      (∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
        (C.wires (PEqualNP.GenericRejection.incidenceInput Q
          (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) ++
          [s.any fun i => (PEqualNP.GenericRejection.incidenceInput Q
            (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)).getD i false])).getD a false = false ∧
        (C.wires (PEqualNP.GenericRejection.incidenceInput Q
          (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) ++
          [s.any fun i => (PEqualNP.GenericRejection.incidenceInput Q
            (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)).getD i false])).getD b false = false) →
      62 ≤ C.size)
    (andW : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ) (s : List ℕ),
      s ∈ ([[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]] : List (List ℕ)) →
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 C →
      a < 27 + C.size → b < 27 + C.size →
      (∀ p l : Fin 13, p ∈ PEqualNP.HeptadCover.singerLines3 l →
        (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l} ++
          [s.any fun i => (PEqualNP.GenericRejection.incidenceInput {p} {l}).getD i false])).getD a false = true ∧
        (C.wires (PEqualNP.GenericRejection.incidenceInput {p} {l} ++
          [s.any fun i => (PEqualNP.GenericRejection.incidenceInput {p} {l}).getD i false])).getD b false = true) →
      (∀ Q : Finset (Fin 13), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q →
        (C.wires (PEqualNP.GenericRejection.incidenceInput Q
          (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) ++
          [s.any fun i => (PEqualNP.GenericRejection.incidenceInput Q
            (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)).getD i false])).getD a false = false ∨
        (C.wires (PEqualNP.GenericRejection.incidenceInput Q
          (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) ++
          [s.any fun i => (PEqualNP.GenericRejection.incidenceInput Q
            (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q)).getD i false])).getD b false = false) →
      62 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); have x5 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : List ℕ) =>   have x7 : List Bool → List Bool := fun (x7 : List Bool) => x7 ++ [x6.any fun (x8 : ℕ) => x7.getD x8 Bool.false];   (∀ (x8 x9 : Fin (13 : ℕ)), x8 - x9 ∈ x1 → x5.eval (x7 (x2 x8 x9)) = Bool.true) ∧ ∀ (x8 : Finset (Fin (13 : ℕ))), x4 x8 → x5.eval (x7 (x3 x8)) = Bool.false; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]], PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x10 : Fin x6.gates.length), ∀ x11 ∈ (x6.gates.get x10).inputs, x11 < (27 : ℕ) + ↑x10) → x5 x6 x7 → (63 : ℕ) ≤ x6.size :=
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.HeptadCover PEqualNP.GenericRejection in by
  intro D P N good spec C s hs mono read fit
  by_cases hbig : 63 ≤ C.size
  · exact hbig
  · have hsize : C.size ≤ 62 := by omega
    let ext (x : List Bool) : List Bool := x ++ [s.any fun i => x.getD i false]
    have fit' :
        (∀ p l : Fin 13, p - l ∈ D → C.eval (ext (P p l)) = true) ∧
        (∀ Q : Finset (Fin 13), good Q → C.eval (ext (N Q)) = false) := by
      simpa [spec, ext] using fit
    rcases fit' with ⟨pos, neg⟩
    have geom : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p - l ∈ D := by
      decide
    have pin (p l : Fin 13) : incidenceInput ({p} : Finset (Fin 13)) ({l} : Finset (Fin 13)) = P p l := by
      change (List.ofFn (fun u : Fin 13 => decide (u ∈ ({p} : Finset (Fin 13)))) ++
          List.ofFn (fun v : Fin 13 => decide (v ∈ ({l} : Finset (Fin 13))))) = _
      simp only [P]
      apply congrArg₂ (· ++ ·)
      · apply congrArg List.ofFn
        funext u
        simp [Finset.mem_singleton]
      · apply congrArg List.ofFn
        funext v
        simp [Finset.mem_singleton]
    have isQ (Q : Finset (Fin 13)) : IsQuadrangle singerLines3 Q ↔ good Q := by
      have eq (l : Fin 13) : Q ∩ singerLines3 l = Q.filter fun p => p - l ∈ D := by
        ext p
        simp only [Finset.mem_inter, Finset.mem_filter]
        exact and_congr_right fun _ => geom p l
      dsimp [IsQuadrangle, good]
      simp only [eq]
    have nrow (Q : Finset (Fin 13)) :
        incidenceInput Q (missLines singerLines3 Q) = N Q := by
      change (List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
          List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))) = N Q
      simp only [N]
      apply congrArg (fun tail => List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++ tail)
      apply congrArg List.ofFn
      funext l
      apply decide_eq_decide.mpr
      change (l ∈ Finset.univ.filter fun l => Disjoint (singerLines3 l) Q) ↔ (∀ r ∈ Q, r - l ∉ D)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right, geom]
    have goodOne : good ({0, 1, 2, 5} : Finset (Fin 13)) := by decide
    have inc22 : (2 : Fin 13) - 2 ∈ D := by decide
    have inc33 : (3 : Fin 13) - 3 ∈ D := by decide
    have inc00 : (0 : Fin 13) - 0 ∈ D := by decide
    have raw : ∀ t ∈ ([[], [0], [13], [0, 1], [13, 14], [0, 13], [0, 14]] : List (List ℕ)),
        ∀ i < 27,
        ((P (2 : Fin 13) 2 ++ [t.any fun j => (P 2 2).getD j false]).getD i false &&
          (P (3 : Fin 13) 3 ++ [t.any fun j => (P 3 3).getD j false]).getD i false) = false := by
      decide
    let V (gs : List Gate) (w : ℕ) (x : List Bool) : Bool :=
      (Circuit.wires ⟨gs, 0⟩ x).getD w false
    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have wires_fold (gs : List Gate) (x : List Bool) :
        Circuit.wires ⟨gs, 0⟩ x = gs.foldl step x := rfl
    have extend : ∀ (gs : List Gate) (x : List Bool),
        ∃ y, Circuit.wires ⟨gs, 0⟩ x = x ++ y ∧ y.length = gs.length := by
      intro gs
      induction gs with
      | nil => intro x; exact ⟨[], (List.append_nil x).symm, rfl⟩
      | cons g gs ih =>
        intro x
        let z := g.op.eval (g.inputs.map fun i => x.getD i false)
        obtain ⟨y, hy, hyl⟩ := ih (x ++ [z])
        refine ⟨z :: y, ?_, by simp [hyl]⟩
        have hstep : Circuit.wires ⟨g :: gs, 0⟩ x = Circuit.wires ⟨gs, 0⟩ (x ++ [z]) := rfl
        rw [hstep, hy]
        simp [List.append_assoc]
    have wires_len (gs : List Gate) (x : List Bool) :
        (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
      obtain ⟨y, hy, hl⟩ := extend gs x
      rw [hy, List.length_append, hl]
    have preserves (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
        V gs w x = x.getD w false := by
      obtain ⟨y, hy, _⟩ := extend gs x
      dsimp [V]
      rw [hy, List.getD_append _ _ _ _ hw]
    have append (gs rest : List Gate) (x : List Bool) :
        Circuit.wires ⟨gs ++ rest, 0⟩ x = Circuit.wires ⟨rest, 0⟩ (Circuit.wires ⟨gs, 0⟩ x) := by
      change (gs ++ rest).foldl step x = rest.foldl step (gs.foldl step x)
      rw [List.foldl_append]
    have finalValue (pre post : List Gate) (g : Gate) (x : List Bool) (hx : x.length = 27) :
        V (pre ++ g :: post) (27 + pre.length) x =
          g.op.eval (g.inputs.map fun w => V pre w x) := by
      let y := Circuit.wires ⟨pre, 0⟩ x
      let z := g.op.eval (g.inputs.map fun w => y.getD w false)
      have hy : y.length = 27 + pre.length := by rw [wires_len, hx]
      have eq : Circuit.wires ⟨pre ++ g :: post, 0⟩ x = Circuit.wires ⟨post, 0⟩ (y ++ [z]) := by
        rw [append]; rfl
      change (Circuit.wires ⟨pre ++ g :: post, 0⟩ x).getD (27 + pre.length) false = z
      rw [eq]
      change V post (27 + pre.length) (y ++ [z]) = z
      rw [preserves post _ _ (by simp [hy])]
      rw [← hy]
      simp
    have split : ∀ (gs : List Gate) (i : ℕ) (g : Gate), gs[i]? = some g →
        ∃ pre post, gs = pre ++ g :: post ∧ pre.length = i := by
      intro gs
      induction gs with
      | nil => intro i g h; simp at h
      | cons a gs ih =>
        intro i g h
        cases i with
        | zero =>
          simp at h
          subst g
          exact ⟨[], gs, rfl, rfl⟩
        | succ i =>
          have hg : gs[i]? = some g := by simpa using h
          obtain ⟨pre, post, rfl, hl⟩ := ih i g hg
          exact ⟨a :: pre, post, rfl, by simp [hl]⟩
    have evalAnd (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
      cases a <;> cases b <;> rfl
    have evalOr (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
      cases a <;> cases b <;> rfl
    have unary (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (b : Bool) :
        op.eval [b] = b := by
      rcases hop with rfl | rfl <;> cases b <;> rfl
    have elen (x : List Bool) (hx : x.length = 26) : (ext x).length = 27 := by
      simp [ext, hx]
    have plen (p l : Fin 13) : (P p l).length = 26 := by
      simp [P]
    have nlen (Q : Finset (Fin 13)) : (N Q).length = 26 := by
      simp [N]
    have rbFull : ReadsBack 27 C := by
      intro j hj w hw
      have hget : gateAt C j = C.gates[j] := by
        have hg : gateAt C j =
            C.gates.getD j ({ op := GateOp.or, inputs := [] } : Gate) := rfl
        rw [hg]
        exact List.getD_eq_getElem C.gates ({ op := GateOp.or, inputs := [] } : Gate) hj
      rw [hget] at hw
      exact read ⟨j, hj⟩ w hw
    let u := C.output
    have pos00 := pos 0 0 inc00
    have hsizeEq : C.size = C.gates.length := rfl
    have wlen0 : (C.wires (ext (P 0 0))).length = 27 + C.size := by
      rw [show C.wires (ext (P 0 0)) = Circuit.wires ⟨C.gates, 0⟩ (ext (P 0 0)) from rfl, wires_len,
        elen _ (plen 0 0), hsizeEq]
    by_cases hu : u < 27 + C.size
    · by_cases hlo : u < 27
      · have b22 := pos 2 2 inc22
        have b33 := pos 3 3 inc33
        have pe22 : (ext (P 2 2)).length = 27 := elen _ (plen 2 2)
        have pe33 : (ext (P 3 3)).length = 27 := elen _ (plen 3 3)
        rw [show C.eval (ext (P 2 2)) = V C.gates u (ext (P 2 2)) from rfl, preserves _ _ _ (by omega)] at b22
        rw [show C.eval (ext (P 3 3)) = V C.gates u (ext (P 3 3)) from rfl, preserves _ _ _ (by omega)] at b33
        have hraw := raw s hs u (by omega)
        rw [show (P (2 : Fin 13) 2 ++ [s.any fun j => (P 2 2).getD j false]) = ext (P 2 2) from rfl] at hraw
        rw [show (P (3 : Fin 13) 3 ++ [s.any fun j => (P 3 3).getD j false]) = ext (P 3 3) from rfl] at hraw
        rw [b22, b33] at hraw
        simp at hraw
      · let i := u - 27
        have hi : i < C.gates.length := by
          dsimp [i, u]
          rw [← hsizeEq]
          omega
        let g := C.gates[i]
        have hgi : C.gates[i]? = some g := by simp [g, hi]
        obtain ⟨pre, post, hgs, hlen⟩ := split C.gates i g hgi
        have huEq : u = 27 + pre.length := by dsimp [u, i]; omega
        have hpreLt : pre.length + 1 ≤ C.size := by
          rw [hsizeEq, hgs]
          simp
        have close (h62 : 62 ≤ (⟨pre, 0⟩ : Circuit).size) : 63 ≤ C.size := by
          have h62' : 62 ≤ pre.length := by
            rw [show (⟨pre, 0⟩ : Circuit).size = pre.length from rfl] at h62
            exact h62
          omega
        have hgin : g ∈ C.gates := by
          rw [hgs]
          exact List.mem_append_right pre (List.mem_cons_self (a := g) (l := post))
        have hgm := mono g hgin
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hgm.1
        have gateAtOut : gateAt C pre.length = g := by
          have hg : gateAt C pre.length =
              C.gates.getD pre.length ({ op := GateOp.or, inputs := [] } : Gate) := rfl
          rw [hg, hgs]
          rw [List.getD_append_right pre (g :: post)
            ({ op := GateOp.or, inputs := [] } : Gate) pre.length (Nat.le_refl _)]
          simp
        have hgr : ∀ w ∈ g.inputs, w < 27 + pre.length := by
          intro w hw
          have hj : pre.length < C.gates.length := by
            rw [hgs, List.length_append]
            exact Nat.lt_add_of_pos_right (by simp : 0 < (g :: post).length)
          have hw' : w ∈ (gateAt C pre.length).inputs := by rw [gateAtOut]; exact hw
          exact rbFull pre.length hj w hw'
        have monoPre : Monotone2 ⟨pre, 0⟩ := by
          intro g' hg'
          exact mono g' (by rw [hgs]; exact List.mem_append_left (g :: post) hg')
        have rbPre : ReadsBack 27 ⟨pre, 0⟩ := by
          intro j hj w hw
          have hj0 : j < pre.length := hj
          have hj' : j < C.gates.length := by
            rw [hgs, List.length_append]
            exact Nat.lt_trans hj0 (Nat.lt_add_of_pos_right (by simp : 0 < (g :: post).length))
          have same : gateAt ⟨pre, 0⟩ j = gateAt C j := by
            have h1 : gateAt ⟨pre, 0⟩ j =
                pre.getD j ({ op := GateOp.or, inputs := [] } : Gate) := rfl
            have h2 : gateAt C j =
                C.gates.getD j ({ op := GateOp.or, inputs := [] } : Gate) := rfl
            rw [h1, h2, hgs]
            rw [List.getD_append pre (g :: post)
              ({ op := GateOp.or, inputs := [] } : Gate) j hj0]
          rw [same] at hw
          exact rbFull j hj' w hw
        have gate (x : List Bool) (hx : x.length = 27) :
            V C.gates u x = g.op.eval (g.inputs.map fun w => V pre w x) := by
          rw [hgs, huEq]
          exact finalValue pre post g x hx
        have ha_size (w : ℕ) (hw : w < 27 + pre.length) : w < 27 + (⟨pre, 0⟩ : Circuit).size := by
          rw [show (⟨pre, 0⟩ : Circuit).size = pre.length from rfl]
          exact hw
        have asBit {w : ℕ} {U Vset : Finset (Fin 13)} {x : List Bool}
            (hx : incidenceInput U Vset = x) :
            ((⟨pre, 0⟩ : Circuit).wires
              (incidenceInput U Vset ++
                [s.any fun i => (incidenceInput U Vset).getD i false])).getD w false
              = V pre w (ext x) := by
          simp [V, ext, hx]
        cases he : g.inputs with
        | nil =>
          rcases hop with hand | hor
          · have H := neg _ goodOne
            rw [show C.eval (ext (N {0, 1, 2, 5})) = V C.gates u (ext (N {0, 1, 2, 5})) from rfl,
              gate _ (elen _ (nlen _)), he, hand] at H
            change true = false at H
            cases H
          · have H := pos 0 0 inc00
            rw [show C.eval (ext (P 0 0)) = V C.gates u (ext (P 0 0)) from rfl,
              gate _ (elen _ (plen _ _)), he, hor] at H
            change false = true at H
            cases H
        | cons a rest =>
          cases er : rest with
          | nil =>
            have ha := hgr a (by simp [he, er])
            have lonePos : ∀ p l : Fin 13, p ∈ singerLines3 l →
                V pre a (ext (P p l)) = true := by
              intro p l hl
              have hv := pos p l ((geom p l).mp hl)
              rw [show C.eval (ext (P p l)) = V C.gates u (ext (P p l)) from rfl,
                gate _ (elen _ (plen _ _)), he, er] at hv
              simpa [unary g.op hop] using hv
            have loneNeg : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
                V pre a (ext (N Q)) = false := by
              intro Q hQ
              have hv := neg Q ((isQ Q).mp hQ)
              rw [show C.eval (ext (N Q)) = V C.gates u (ext (N Q)) from rfl,
                gate _ (elen _ (nlen _)), he, er] at hv
              simpa [unary g.op hop] using hv
            have h62 : 62 ≤ (⟨pre, 0⟩ : Circuit).size :=
              orW ⟨pre, 0⟩ a a s hs monoPre rbPre (ha_size a ha) (ha_size a ha)
                (by
                  intro p l hl
                  rw [asBit (pin p l)]
                  rw [lonePos p l hl]
                  rw [Bool.or_self])
                (by
                  intro Q hQ
                  rw [asBit (nrow Q)]
                  rw [loneNeg Q hQ]
                  exact ⟨rfl, rfl⟩)
            exact absurd (close h62) hbig
          | cons b rest' =>
            have erest : rest' = [] := by
              have h := hgm.2
              rw [he, er] at h
              cases rest' with
              | nil => rfl
              | cons c cs => simp at h
            subst erest
            have ha := hgr a (by simp [he, er])
            have hb := hgr b (by simp [he, er])
            rcases hop with hand | hor
            · have bothPos : ∀ p l : Fin 13, p ∈ singerLines3 l →
                  V pre a (ext (P p l)) = true ∧ V pre b (ext (P p l)) = true := by
                intro p l hl
                have z := pos p l ((geom p l).mp hl)
                rw [show C.eval (ext (P p l)) = V C.gates u (ext (P p l)) from rfl,
                  gate _ (elen _ (plen _ _)), he, er, hand] at z
                simp only [List.map_cons, List.map_nil, evalAnd] at z
                cases haB : V pre a (ext (P p l)) <;> cases hbB : V pre b (ext (P p l))
                · simp [haB, hbB] at z
                · simp [haB, hbB] at z
                · simp [haB, hbB] at z
                · exact ⟨rfl, rfl⟩
              have oneNeg : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
                  V pre a (ext (N Q)) = false ∨ V pre b (ext (N Q)) = false := by
                intro Q hQ
                have z := neg Q ((isQ Q).mp hQ)
                rw [show C.eval (ext (N Q)) = V C.gates u (ext (N Q)) from rfl,
                  gate _ (elen _ (nlen _)), he, er, hand] at z
                simp only [List.map_cons, List.map_nil, evalAnd] at z
                cases haB : V pre a (ext (N Q))
                · exact Or.inl rfl
                · cases hbB : V pre b (ext (N Q))
                  · exact Or.inr rfl
                  · simp [haB, hbB] at z
              have h62 : 62 ≤ (⟨pre, 0⟩ : Circuit).size :=
                andW ⟨pre, 0⟩ a b s hs monoPre rbPre (ha_size a ha) (ha_size b hb)
                  (by
                    intro p l hl
                    rw [asBit (pin p l), asBit (pin p l)]
                    exact bothPos p l hl)
                  (by
                    intro Q hQ
                    rw [asBit (nrow Q), asBit (nrow Q)]
                    exact oneNeg Q hQ)
              exact absurd (close h62) hbig
            · have somePos : ∀ p l : Fin 13, p ∈ singerLines3 l →
                  (V pre a (ext (P p l)) || V pre b (ext (P p l))) = true := by
                intro p l hl
                have z := pos p l ((geom p l).mp hl)
                rw [show C.eval (ext (P p l)) = V C.gates u (ext (P p l)) from rfl,
                  gate _ (elen _ (plen _ _)), he, er, hor] at z
                simp only [List.map_cons, List.map_nil, evalOr] at z
                exact z
              have bothNeg : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
                  V pre a (ext (N Q)) = false ∧ V pre b (ext (N Q)) = false := by
                intro Q hQ
                have z := neg Q ((isQ Q).mp hQ)
                rw [show C.eval (ext (N Q)) = V C.gates u (ext (N Q)) from rfl,
                  gate _ (elen _ (nlen _)), he, er, hor] at z
                simp only [List.map_cons, List.map_nil, evalOr] at z
                cases haB : V pre a (ext (N Q)) <;> cases hbB : V pre b (ext (N Q))
                · exact ⟨rfl, rfl⟩
                · simp [haB, hbB] at z
                · simp [haB, hbB] at z
                · simp [haB, hbB] at z
              have h62 : 62 ≤ (⟨pre, 0⟩ : Circuit).size :=
                orW ⟨pre, 0⟩ a b s hs monoPre rbPre (ha_size a ha) (ha_size b hb)
                  (by
                    intro p l hl
                    rw [asBit (pin p l), asBit (pin p l)]
                    exact somePos p l hl)
                  (by
                    intro Q hQ
                    rw [asBit (nrow Q), asBit (nrow Q)]
                    exact bothNeg Q hQ)
              exact absurd (close h62) hbig
    · have H := pos 0 0 inc00
      rw [show C.eval (ext (P 0 0)) = (C.wires (ext (P 0 0))).getD u false from rfl] at H
      rw [List.getD_eq_default _ _ (by rw [wlen0]; omega)] at H
      simp at H
