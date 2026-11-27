import Mathlib.Tactic.Tauto
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 24000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2590_932
  (edgeOr : let E : List (Fin 10 × Fin 10) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
    ∀ ws : List ((Fin 10 → Bool) → Bool), ws.length ≤ 18 →
    (∀ k : Fin ws.length,
      let p := ((fun _ => false) :: (fun _ => true) :: List.ofFn (fun (i : Fin 10) x => x i)) ++
        [fun x => x 0 || x 1] ++ ws.take k.val
      ws.get k ∉ p ∧
        ∃ a ∈ p, ∃ b ∈ p, ws.get k = (fun x => a x && b x) ∨ ws.get k = (fun x => a x || b x)) →
    (∀ w ∈ ws, ∀ i j : Fin 10, i ≠ j → ¬ (E.any fun e => decide ((i, j) = e ∨ (j, i) = e)) = true → w ≠ fun x => x i && x j) →
    (fun x => E.any fun e => x e.1 && x e.2) ∉ ws)
  (nonedgeOr : let E : List (Fin 10 × Fin 10) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
    ∀ ws : List ((Fin 10 → Bool) → Bool), ws.length ≤ 18 →
    (∀ k : Fin ws.length,
      let p := ((fun _ => false) :: (fun _ => true) :: List.ofFn (fun (i : Fin 10) x => x i)) ++
        [fun x => x 0 || x 2] ++ ws.take k.val
      ws.get k ∉ p ∧
        ∃ a ∈ p, ∃ b ∈ p, ws.get k = (fun x => a x && b x) ∨ ws.get k = (fun x => a x || b x)) →
    (∀ w ∈ ws, ∀ i j : Fin 10, i ≠ j →
      let A := (E.any fun e => decide ((i, j) = e ∨ (j, i) = e)) = true
      (¬ A → w ≠ fun x => x i && x j) ∧ (A → w ≠ fun x => x i || x j)) →
    (fun x => E.any fun e => x e.1 && x e.2) ∉ ws)
  (edgeAnd : let E : List (Fin 10 × Fin 10) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
    ∀ ws : List ((Fin 10 → Bool) → Bool), ws.length ≤ 18 →
    (∀ k : Fin ws.length,
      let p := ((fun _ => false) :: (fun _ => true) :: List.ofFn (fun (i : Fin 10) x => x i)) ++
        [fun x => x 0 && x 1] ++ ws.take k.val
      ws.get k ∉ p ∧
        ∃ a ∈ p, ∃ b ∈ p, ws.get k = (fun x => a x && b x) ∨ ws.get k = (fun x => a x || b x)) →
    (∀ w ∈ ws, ∀ i j : Fin 10, i ≠ j →
      (¬ (E.any fun e => decide ((i, j) = e ∨ (j, i) = e)) = true → w ≠ fun x => x i && x j) ∧
      (w ≠ fun x => x i || x j)) →
    (fun x => E.any fun e => x e.1 && x e.2) ∉ ws) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → ¬∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C mono budget comp
  let Point := Fin 10 → Bool
  let Wire := Point → Bool
  let pin (i : Fin 10) : Wire := fun x => x i
  let zero : Wire := fun _ => false
  let one : Wire := fun _ => true
  let meet (a b : Wire) : Wire := fun x => a x && b x
  let join (a b : Wire) : Wire := fun x => a x || b x
  let pins : List Wire := List.ofFn pin
  let base : List Wire := zero :: one :: pins

  let Step (prior : List Wire) (w : Wire) : Prop :=
    ∃ a ∈ prior, ∃ b ∈ prior, w = meet a b ∨ w = join a b

  let Trace (prior gs : List Wire) : Prop :=
    List.rec (motive := fun _ => List Wire → Prop) (fun _ => True)
      (fun w _ rec p => Step p w ∧ rec (p ++ [w])) gs prior

  have step_mono {p q : List Wire} {w : Wire} (h : Step p w) (sub : p ⊆ q) : Step q w := by
    obtain ⟨a, ha, b, hb, hw⟩ := h
    exact ⟨a, sub ha, b, sub hb, hw⟩

  have trace_mono {p q gs : List Wire} (h : Trace p gs) (sub : p ⊆ q) : Trace q gs := by
    induction gs generalizing p q with
    | nil => trivial
    | cons w gs ih =>
      refine ⟨step_mono h.1 sub, ih h.2 ?_⟩
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact List.mem_append_left _ (sub ha)
      · exact List.mem_append_right _ ha

  have trace_append_iff {p u v : List Wire} :
      Trace p (u ++ v) ↔ Trace p u ∧ Trace (p ++ u) v := by
    induction u generalizing p with
    | nil => simp [Trace]
    | cons w u ih =>
      have he : p ++ [w] ++ u = p ++ w :: u := by simp [List.append_assoc]
      simp [Trace, ih, he, and_assoc]

  have move_first {p gs : List Wire} {w : Wire} (h : Trace p gs) (hmem : w ∈ gs)
      (hstep : Step p w) : ∃ rest, gs.length = rest.length + 1 ∧
        Trace p (w :: rest) ∧ ∀ a, a ∈ w :: rest ↔ a ∈ gs := by
    obtain ⟨u, v, rfl⟩ := List.mem_iff_append.mp hmem
    rw [trace_append_iff] at h
    refine ⟨u ++ v, by simp; omega, ⟨hstep, ?_⟩, ?_⟩
    · change Trace (p ++ [w]) (u ++ v)
      rw [trace_append_iff]
      refine ⟨trace_mono h.1 (fun _ ha => List.mem_append_left _ ha), trace_mono h.2.2 ?_⟩
      intro a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
      tauto
    · intro a
      simp only [List.mem_append, List.mem_cons]
      tauto

  let symbolicGate (ws : List Wire) (g : Gate) : Wire :=
    fun x => g.op.eval (g.inputs.map fun i => (ws.getD i zero) x)

  let symbolic (ws : List Wire) (gs : List Gate) : List Wire :=
    List.rec (motive := fun _ => List Wire → List Wire) (fun _ => [])
      (fun g _ rec p => symbolicGate p g :: rec (p ++ [symbolicGate p g])) gs ws

  have getD_mem (ws : List Wire) (i : ℕ) : ws.getD i zero ∈ zero :: one :: ws := by
    by_cases h : i < ws.length
    · rw [List.getD_eq_getElem _ _ h]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.getElem_mem h))
    · rw [List.getD_eq_default _ _ (by omega)]
      simp

  have and_eval (xs : List Bool) : GateOp.eval .and xs = xs.all id := rfl
  have or_eval (xs : List Bool) : GateOp.eval .or xs = xs.any id := rfl

  have symbolicGate_step (ws : List Wire) (g : Gate)
      (mono : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      Step (zero :: one :: ws) (symbolicGate ws g) := by
    obtain ⟨op, len⟩ := mono
    change g.op = .and ∨ g.op = .or at op
    have had (b : Wire) (hb : b ∈ zero :: one :: ws) (h : symbolicGate ws g = b) :
        Step (zero :: one :: ws) (symbolicGate ws g) := by
      refine ⟨b, hb, b, hb, Or.inl ?_⟩
      rw [h]
      funext x
      simp [meet]
    cases hs : g.inputs with
    | nil =>
        rcases op with op | op
        · exact had one (by simp) (by funext x; simp [symbolicGate, hs, op, and_eval, one])
        · exact had zero (by simp) (by funext x; simp [symbolicGate, hs, op, or_eval, zero])
    | cons i is =>
      cases is with
      | nil =>
        apply had _ (getD_mem ws i)
        funext x
        rcases op with op | op
        · simp [symbolicGate, hs, op, and_eval]
        · simp [symbolicGate, hs, op, or_eval]
      | cons j js =>
        have eq : js = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [hs, List.length_cons] at len
          omega
        subst js
        refine ⟨_, getD_mem ws i, _, getD_mem ws j, ?_⟩
        rcases op with op | op
        · left; funext x; simp [symbolicGate, hs, op, and_eval, meet]
        · right; funext x; simp [symbolicGate, hs, op, or_eval, join]

  have symbolic_trace (ws : List Wire) (gs : List Gate)
      (mono : Monotone2 ⟨gs, 0⟩) : Trace (zero :: one :: ws) (symbolic ws gs) := by
    induction gs generalizing ws with
    | nil => trivial
    | cons g gs ih =>
      exact ⟨symbolicGate_step ws g (mono g List.mem_cons_self),
        ih (ws ++ _) (fun a ha => mono a (List.mem_cons_of_mem _ ha))⟩

  have symbolic_length (ws : List Wire) (gs : List Gate) : (symbolic ws gs).length = gs.length := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih => simp [symbolic, ih]

  have wires_unfold (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := rfl

  have eval_unfold (C : Circuit) (x : List Bool) :
      C.eval x = (C.wires x).getD C.output false := rfl

  have eval_symbolic (ws : List Wire) (gs : List Gate) (x : Point) :
      (((⟨gs, 0⟩ : Circuit).wires (ws.map fun a => a x)))
        = (ws ++ symbolic ws gs).map (fun a => a x) := by
    induction gs generalizing ws with
    | nil => simp [wires_unfold, symbolic]
    | cons g gs ih =>
      rw [wires_unfold]
      simp only [List.foldl_cons]
      have he : g.op.eval (g.inputs.map fun i => (ws.map fun a => a x).getD i false)
          = symbolicGate ws g x := by
        unfold symbolicGate
        congr 1
        apply List.map_congr_left
        intro i _
        exact List.getD_map ws zero (fun a => a x)
      rw [he]
      change (⟨gs, 0⟩ : Circuit).wires ((ws.map fun a => a x) ++ [symbolicGate ws g x]) = _
      have eq : (ws.map fun a => a x) ++ [symbolicGate ws g x]
          = (ws ++ [symbolicGate ws g]).map (fun a => a x) := by simp
      rw [eq, ih]
      simp [List.append_assoc, symbolic]

  have eval_pins (x : Point) : pins.map (fun a => a x) = List.ofFn x := by
    simp [pins, pin]

  have circuit_trace (C : Circuit) (hC : Monotone2 C) (f : Wire)
      (hf : ∀ x, C.eval (List.ofFn x) = f x) :
      ∃ gs, gs.length = C.size ∧ Trace base gs ∧ f ∈ base ++ gs := by
    let gs := symbolic pins C.gates
    refine ⟨gs, symbolic_length _ _, symbolic_trace _ _ hC, ?_⟩
    have eq : f = (pins ++ gs).getD C.output zero := by
      funext x
      rw [← hf x, eval_unfold, ← eval_pins x]
      change ((⟨C.gates, 0⟩ : Circuit).wires (pins.map fun a => a x)).getD C.output false = _
      rw [eval_symbolic]
      exact List.getD_map _ zero (fun a => a x)
    rw [eq]
    exact getD_mem (pins ++ gs) _

  let edges : List (Fin 10 × Fin 10) :=
      [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (4,9),
       (5,7), (7,9), (9,6), (6,8), (8,5)]

  let adjacent (i j : Fin 10) : Bool := edges.any fun e => decide ((i,j) = e ∨ (j,i) = e)
  let Edge (i j : Fin 10) : Prop := adjacent i j = true

  have edge_iff (i j : Fin 10) : Edge i j ↔ (i,j) ∈ edges ∨ (j,i) ∈ edges := by
    unfold Edge adjacent
    constructor
    · intro h
      obtain ⟨p, hp, he⟩ := List.any_eq_true.mp h
      rcases of_decide_eq_true he with he | he
      · exact Or.inl (he ▸ hp)
      · exact Or.inr (he ▸ hp)
    · intro h
      rcases h with h | h
      · exact List.any_eq_true.mpr ⟨(i,j), h, decide_eq_true (Or.inl rfl)⟩
      · exact List.any_eq_true.mpr ⟨(j,i), h, decide_eq_true (Or.inr rfl)⟩
  let target : Wire := fun x => edges.any (fun e => x e.1 && x e.2)
  let pair (e : Fin 10 × Fin 10) : Point := fun i => decide (i = e.1 ∨ i = e.2)

  let Increasing (a : Wire) : Prop := Monotone a

  have trace_increasing {p gs : List Wire} (hp : ∀ a ∈ p, Increasing a)
      (h : Trace p gs) : ∀ a ∈ p ++ gs, Increasing a := by
    induction gs generalizing p with
    | nil => simpa using hp
    | cons w gs ih =>
      have hw : Increasing w := by
        obtain ⟨a, ha, b, hb, rfl | rfl⟩ := h.1
        · exact fun x y hxy => inf_le_inf (hp a ha hxy) (hp b hb hxy)
        · exact fun x y hxy => sup_le_sup (hp a ha hxy) (hp b hb hxy)
      rw [← List.singleton_append, ← List.append_assoc]
      apply ih _ h.2
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hp a ha
      · simpa using (List.mem_singleton.mp ha).symm ▸ hw

  have base_increasing : ∀ w ∈ base, Increasing w := by
    intro w hw
    simp only [base, List.mem_cons] at hw
    rcases hw with rfl | rfl | hw
    · exact fun _ _ _ => le_rfl
    · exact fun _ _ _ => le_rfl
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      exact fun _ _ h => h i

  let MaskRel (a b : Wire) : Prop :=
    (∀ x, b x ≤ a x) ∧ ∀ e ∈ edges, b (pair e) = a (pair e)

  have mask_refl (a : Wire) : MaskRel a a := ⟨fun _ => le_rfl, fun _ _ => rfl⟩

  have mask_meet {a b c d : Wire} (ac : MaskRel a c) (bd : MaskRel b d) :
      MaskRel (meet a b) (meet c d) := by
    exact ⟨fun x => inf_le_inf (ac.1 x) (bd.1 x), fun e he => by unfold meet; rw [ac.2 e he, bd.2 e he]⟩

  have mask_join {a b c d : Wire} (ac : MaskRel a c) (bd : MaskRel b d) :
      MaskRel (join a b) (join c d) := by
    exact ⟨fun x => sup_le_sup (ac.1 x) (bd.1 x), fun e he => by unfold join; rw [ac.2 e he, bd.2 e he]⟩

  let Covers (p q : List Wire) : Prop := ∀ a ∈ p, ∃ b ∈ q, MaskRel a b

  have replace_trace {p q gs : List Wire} (h : Trace p gs) (hc : Covers p q) :
      ∃ rest, rest.length = gs.length ∧ Trace q rest ∧ Covers (p ++ gs) (q ++ rest) := by
    induction gs generalizing p q with
    | nil => exact ⟨[], rfl, trivial, by simpa using hc⟩
    | cons w gs ih =>
      have one_step : ∃ w', Step q w' ∧ MaskRel w w' := by
        obtain ⟨a, ha, b, hb, hw⟩ := h.1
        obtain ⟨c, hcm, hac⟩ := hc a ha
        obtain ⟨d, hdm, hbd⟩ := hc b hb
        rcases hw with rfl | rfl
        · exact ⟨meet c d, ⟨c, hcm, d, hdm, Or.inl rfl⟩, mask_meet hac hbd⟩
        · exact ⟨join c d, ⟨c, hcm, d, hdm, Or.inr rfl⟩, mask_join hac hbd⟩
      obtain ⟨w', gen, mask⟩ := one_step
      have extra : Covers (p ++ [w]) (q ++ [w']) := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨b, hb, hab⟩ := hc _ ha
          exact ⟨b, List.mem_append_left _ hb, hab⟩
        · obtain rfl := List.mem_singleton.mp ha
          exact ⟨w', by simp, mask⟩
      obtain ⟨tail, hlen, htrace, hcover⟩ := ih h.2 extra
      exact ⟨w' :: tail, by simp [hlen], ⟨gen, htrace⟩, by simpa [List.append_assoc] using hcover⟩

  have target_pair (e : Fin 10 × Fin 10) (he : e ∈ edges) : target (pair e) = true := by
    exact List.any_eq_true.mpr ⟨e, he, by simp [pair]⟩

  have mask_target {w : Wire} (hm : MaskRel target w) (hi : Increasing w) : w = target := by
    funext x
    cases ht : target x with
    | false => have h := hm.1 x; rw [ht] at h; exact le_antisymm h (Bool.false_le _)
    | true =>
      have h : edges.any (fun e => x e.1 && x e.2) = true := ht
      obtain ⟨e, he, hv⟩ := List.any_eq_true.mp h
      have hp : pair e ≤ x := by
        intro i
        by_cases h : i = e.1 ∨ i = e.2
        · simp only [Bool.and_eq_true] at hv
          obtain ⟨h₁, h₂⟩ := hv
          rcases h with rfl | rfl <;> simp [h₁, h₂]
        · simp [pair, show i ≠ e.1 from fun eq => h (Or.inl eq),
            show i ≠ e.2 from fun eq => h (Or.inr eq)]
      have res := hi hp
      rw [hm.2 e he, target_pair e he] at res
      exact le_antisymm (Bool.le_true _) res

  have nonedge_mask (i j : Fin 10) (ne : i ≠ j) (notAdj : ¬ Edge i j) :
      MaskRel (meet (pin i) (pin j)) zero := by
    refine ⟨fun _ => Bool.false_le _, ?_⟩
    intro e he
    rw [eq_comm]
    apply Bool.eq_false_iff.mpr
    intro h
    have hh : pair e i && pair e j = true := h
    simp only [Bool.and_eq_true] at hh
    obtain ⟨hi, hj⟩ := hh
    apply notAdj
    rw [edge_iff]
    have hi' : i = e.1 ∨ i = e.2 := of_decide_eq_true hi
    have hj' : j = e.1 ∨ j = e.2 := of_decide_eq_true hj
    clear hi hj
    rcases hi' with hi | hi <;> rcases hj' with hj | hj
    · exact (ne (hi.trans hj.symm)).elim
    · left; simpa [hi, hj] using he
    · right; simpa [hi, hj] using he
    · exact (ne (hi.trans hj.symm)).elim

  have delete_nonedge (i j : Fin 10) (ne : i ≠ j) (notAdj : ¬ Edge i j)
      (gs : List Wire) (ht : Trace base (meet (pin i) (pin j) :: gs))
      (hf : target ∈ base ++ (meet (pin i) (pin j) :: gs)) :
      ∃ rest, rest.length = gs.length ∧ Trace base rest ∧ target ∈ base ++ rest := by
    have hc : Covers (base ++ [meet (pin i) (pin j)]) base := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact ⟨w, hw, mask_refl _⟩
      · obtain rfl := List.mem_singleton.mp hw
        exact ⟨zero, by simp [base], nonedge_mask i j ne notAdj⟩
    obtain ⟨rest, sz, tr, cv⟩ := replace_trace ht.2 hc
    obtain ⟨w, hw, wr⟩ := cv target (by simpa [List.append_assoc] using hf)
    have eq := mask_target wr (trace_increasing base_increasing tr w hw)
    exact ⟨rest, sz, tr, eq ▸ hw⟩

  have trace_indexed {p gs : List Wire} (h : Trace p gs) (j : Fin gs.length) :
      Step (p ++ gs.take j) (gs.get j) := by
    induction gs generalizing p with
    | nil => exact Fin.elim0 j
    | cons w gs ih =>
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using h.1
      · simpa [List.append_assoc] using ih h.2 j

  have split_at {α : Type} (gs : List α) (j : Fin gs.length) :
      gs = gs.take j ++ gs.get j :: gs.drop (j.val + 1) := by
    conv_lhs => rw [← List.take_append_drop j.val gs]
    congr 1
    exact List.drop_eq_getElem_cons j.isLt


  let Solves (gs : List Wire) : Prop := Trace base gs ∧ target ∈ base ++ gs
  let Smallest (gs : List Wire) : Prop := Solves gs ∧ ∀ rest, Solves rest → gs.length ≤ rest.length

  have smallest_of_exists (gs : List Wire) (h : Solves gs) :
      ∃ rest, Smallest rest ∧ rest.length ≤ gs.length := by
    classical
    let S : ℕ → Prop := fun n => ∃ rest, rest.length = n ∧ Solves rest
    have hn : ∃ n, S n := ⟨gs.length, gs, rfl, h⟩
    obtain ⟨rest, len, solves⟩ := Nat.find_spec hn
    exact ⟨rest, ⟨solves, fun t ht => len.trans_le (Nat.find_min' hn ⟨t, rfl, ht⟩)⟩,
      len.trans_le (Nat.find_min' hn ⟨gs, rfl, h⟩)⟩

  have shortest_fresh {gs : List Wire} (hs : Smallest gs) (j : Fin gs.length) :
      gs.get j ∉ base ++ gs.take j := by
    intro hmem
    let w := gs.get j
    let front := gs.take j.val
    let tail := gs.drop (j.val + 1)
    have eq : gs = front ++ w :: tail := split_at gs j
    have htr := hs.1.1
    rw [eq, trace_append_iff] at htr
    have sub : (base ++ front) ++ [w] ⊆ base ++ front := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact ha
      · exact List.mem_singleton.mp ha ▸ hmem
    have ht : Trace base (front ++ tail) := trace_append_iff.mpr ⟨htr.1, trace_mono htr.2.2 sub⟩
    have hf : target ∈ (base ++ front ++ [w]) ++ tail := by
      have h := hs.1.2
      rw [eq] at h
      simpa only [List.append_assoc, List.singleton_append] using h
    have hnew : target ∈ base ++ (front ++ tail) := by
      rw [← List.append_assoc]
      rcases List.mem_append.mp hf with hf | hf
      · exact List.mem_append_left _ (sub hf)
      · exact List.mem_append_right _ hf
    have hsize := hs.2 _ ⟨ht, hnew⟩
    rw [eq] at hsize
    simp only [List.length_append, List.length_cons] at hsize
    omega

  have mem_base (w : Wire) : w ∈ base ↔ w = zero ∨ w = one ∨ ∃ i, w = pin i := by
    simp only [base, pins, List.mem_cons, List.mem_ofFn, eq_comm]

  have pin_in_base (i : Fin 10) : pin i ∈ base := (mem_base _).2 (Or.inr (Or.inr ⟨i, rfl⟩))

  have classify_first {w : Wire} (h : Step base w) :
      w ∈ base ∨ ∃ i j : Fin 10, i ≠ j ∧
        (w = meet (pin i) (pin j) ∨ w = join (pin i) (pin j)) := by
    obtain ⟨a, ha, b, hb, hw⟩ := h
    rw [mem_base] at ha hb
    have lz (b : Wire) : meet zero b = zero ∧ join zero b = b := by
      constructor <;> funext x <;> simp [meet, join, zero]
    have rz (a : Wire) : meet a zero = zero ∧ join a zero = a := by
      constructor <;> funext x <;> simp [meet, join, zero]
    have lo (b : Wire) : meet one b = b ∧ join one b = one := by
      constructor <;> funext x <;> simp [meet, join, one]
    have ro (a : Wire) : meet a one = a ∧ join a one = one := by
      constructor <;> funext x <;> simp [meet, join, one]
    have idem (i j : Fin 10) (h : i = j) :
        meet (pin i) (pin j) ∈ base ∧ join (pin i) (pin j) ∈ base := by
      subst j
      have a : meet (pin i) (pin i) = pin i := by funext x; simp [meet]
      have b : join (pin i) (pin i) = pin i := by funext x; simp [join]
      exact ⟨by rw [a, mem_base]; exact Or.inr (Or.inr ⟨i, rfl⟩),
        by rw [b, mem_base]; exact Or.inr (Or.inr ⟨i, rfl⟩)⟩
    rcases ha with rfl | rfl | ⟨i, rfl⟩ <;> rcases hb with rfl | rfl | ⟨j, rfl⟩ <;>
      rcases hw with rfl | rfl
    all_goals try
      (left
       first | rw [(lz _).1] | rw [(lz _).2] | rw [(rz _).1] | rw [(rz _).2] |
         rw [(lo _).1] | rw [(lo _).2] | rw [(ro _).1] | rw [(ro _).2]
       first | exact pin_in_base _ | simp [base])
    all_goals
      by_cases hi : i = j
      · left
        first | exact (idem i j hi).1 | exact (idem i j hi).2
      · right
        exact ⟨i, j, hi, by first | exact Or.inl rfl | exact Or.inr rfl⟩

  have raw_join (i j : Fin 10) : Step base (join (pin i) (pin j)) :=
    ⟨pin i, pin_in_base i, pin j, pin_in_base j, Or.inr rfl⟩

  have raw_meet (i j : Fin 10) : Step base (meet (pin i) (pin j)) :=
    ⟨pin i, pin_in_base i, pin j, pin_in_base j, Or.inl rfl⟩

  have not_base : target ∉ base := by
    intro h
    rcases (mem_base _).1 h with h | h | ⟨i, hi⟩
    · have no : target (fun _ => true) ≠ zero (fun _ => true) := by decide
      exact no (congrFun h (fun _ => true))
    · have no : target (fun _ => false) ≠ one (fun _ => false) := by decide
      exact no (congrFun h (fun _ => false))
    · have no : ∀ i : Fin 10, target (fun j => decide (i = j)) ≠ pin i (fun j => decide (i = j)) := by decide
      exact no i (congrFun hi (fun j => decide (i = j)))

  let spin (p : Fin 10 → Fin 10) (w : Wire) : Wire := fun x => w (x ∘ p)

  have trace_spin {p gs : List Wire} (h : Trace p gs) (r : Fin 10 → Fin 10) :
      Trace (p.map (spin r)) (gs.map (spin r)) := by
    induction gs generalizing p with
    | nil => trivial
    | cons w gs ih =>
      refine ⟨?_, ?_⟩
      · obtain ⟨a, ha, b, hb, hw⟩ := h.1
        exact ⟨spin r a, List.mem_map_of_mem ha, spin r b, List.mem_map_of_mem hb,
          hw.elim (fun h => Or.inl (congrArg (spin r) h))
            (fun h => Or.inr (congrArg (spin r) h))⟩
      · simpa using ih h.2

  have trace_spin_base {gs : List Wire} (h : Trace base gs) (r : Fin 10 → Fin 10) :
      Trace base (gs.map (spin r)) := by
    apply trace_mono (trace_spin h r)
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    rcases (mem_base _).1 hv with rfl | rfl | ⟨i,rfl⟩
    · exact (mem_base _).2 (Or.inl rfl)
    · exact (mem_base _).2 (Or.inr (Or.inl rfl))
    · exact pin_in_base (r i)

  let cycleA : Fin 10 → Fin 10 := ![2, 3, 4, 9, 7, 1, 8, 0, 6, 5]
  let cycleB : Fin 10 → Fin 10 := ![0, 4, 3, 8, 5, 1, 9, 2, 6, 7]

  have cycleA_inv : spin cycleA target = target := by
    funext x
    dsimp [spin, cycleA, target, edges, Function.comp_def]
    simp only [Bool.or_false]
    ac_rfl

  have cycleB_inv : spin cycleB target = target := by
    funext x
    dsimp [spin, cycleB, target, edges, Function.comp_def]
    simp only [Bool.or_false]
    ac_rfl

  have cycleA_bij : Function.Bijective cycleA := by
    constructor
    · change ∀ i j : Fin 10, cycleA i = cycleA j → i = j
      decide
    · change ∀ j, ∃ i, cycleA i = j
      decide

  have cycleB_bij : Function.Bijective cycleB := by
    constructor
    · change ∀ i j : Fin 10, cycleB i = cycleB j → i = j
      decide
    · change ∀ j, ∃ i, cycleB i = j
      decide

  have cycleA_edges : ∀ i j, Edge (cycleA i) (cycleA j) ↔ Edge i j := by
    decide

  have cycleB_edges : ∀ i j, Edge (cycleB i) (cycleB j) ↔ Edge i j := by
    decide

  let move (word : List Bool) (i : Fin 10) : Fin 10 :=
    word.foldl (fun j b => if b then cycleB j else cycleA j) i

  have move_cons (bit : Bool) (word : List Bool) :
      move (bit :: word) = move word ∘ (if bit then cycleB else cycleA) := by
    cases bit <;> rfl

  have sym_move (word : List Bool) :
      spin (move word) target = target ∧ Function.Bijective (move word) ∧
      ∀ i j, Edge (move word i) (move word j) ↔ Edge i j := by
    induction word with
    | nil => exact ⟨rfl, Function.bijective_id, fun _ _ => Iff.rfl⟩
    | cons b ws ih =>
      rw [move_cons]
      cases b
      · exact ⟨(congrArg (spin (move ws)) cycleA_inv).trans ih.1,
          ih.2.1.comp cycleA_bij, fun i j => (ih.2.2 _ _).trans (cycleA_edges i j)⟩
      · exact ⟨(congrArg (spin (move ws)) cycleB_inv).trans ih.1,
          ih.2.1.comp cycleB_bij, fun i j => (ih.2.2 _ _).trans (cycleB_edges i j)⟩

  let routes : List (List Bool) := (List.range 7).flatMap fun n =>
    (List.range (2 ^ n)).map fun m => (List.range n).map m.testBit

  have routes_cover : ∀ i j : Fin 10, routes.any (fun w =>
        decide (move w i = 0 ∧ (move w j = 0 ∨ move w j = 1 ∨ move w j = 2))) = true := by decide

  have orbit (i j : Fin 10) (ne : i ≠ j) :
      ∃ r, r i = 0 ∧ r j = (if Edge i j then 1 else 2) ∧
        spin r target = target ∧ Function.Bijective r ∧
        ∀ u v, Edge (r u) (r v) ↔ Edge u v := by
    classical
    obtain ⟨w, _, hw⟩ := List.any_eq_true.mp (routes_cover i j)
    have hm := of_decide_eq_true hw
    have hs := sym_move w
    refine ⟨move w, hm.1, ?_, hs⟩
    rcases hm.2 with h | h | h
    · exact (ne (hs.2.1.1 (hm.1.trans h.symm))).elim
    · have edge : Edge i j := (hs.2.2 i j).1 (by rw [hm.1, h]; exact by decide)
      simp [edge, h]
    · have notEdge : ¬ Edge i j := fun e => by
        have e' := (hs.2.2 i j).2 e
        rw [hm.1, h] at e'
        exact (by decide : ¬ Edge 0 2) e'
      simp [notEdge, h]

  let raw (andGate : Bool) (i j : Fin 10) : Wire :=
    if andGate then meet (pin i) (pin j) else join (pin i) (pin j)

  have spin_raw (r : Fin 10 → Fin 10) (op : Bool) (i j : Fin 10) :
      spin r (raw op i j) = raw op (r i) (r j) := by
    cases op <;> rfl

  have spin_injective {r : Fin 10 → Fin 10} (hr : Function.Injective r) :
      Function.Injective (spin r) := by
    classical
    intro a b hab
    funext x
    have eq : (x ∘ Function.invFun r) ∘ r = x := by
      funext k
      change x (Function.invFun r (r k)) = x k
      rw [Function.leftInverse_invFun hr k]
    have h := congrFun hab (x ∘ Function.invFun r)
    change a ((x ∘ Function.invFun r) ∘ r) = b ((x ∘ Function.invFun r) ∘ r) at h
    rwa [eq] at h

  let NoRawJoin (edgesOnly : Bool) (gs : List Wire) : Prop :=
    ∀ w ∈ gs, ∀ i j : Fin 10, i ≠ j → (edgesOnly = true → Edge i j) →
      w ≠ join (pin i) (pin j)

  have spin_exclusion {r : Fin 10 → Fin 10} {gs : List Wire}
      (hr : Function.Bijective r) (symm : ∀ u v, Edge (r u) (r v) ↔ Edge u v)
      {edgesOnly : Bool} (no : NoRawJoin edgesOnly gs) :
      NoRawJoin edgesOnly (gs.map (spin r)) := by
    intro w hw i j ne hE heq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hw
    obtain ⟨u, hu⟩ := hr.2 i
    obtain ⟨v, hv⟩ := hr.2 j
    have h : spin r a = spin r (raw false u v) := by
      rw [spin_raw, hu, hv]
      exact heq
    apply no a ha u v
    · intro eq
      exact ne (hu.symm.trans ((congrArg r eq).trans hv))
    · intro hmode
      apply (symm u v).1
      rw [hu, hv]
      exact hE hmode
    · exact spin_injective hr.1 h

  have transport {gs : List Wire} (hs : Smallest gs) (op : Bool) {i j : Fin 10}
      (hne : i ≠ j) (hw : raw op i j ∈ gs) :
      ∃ rest, Smallest (raw op 0 (if Edge i j then 1 else 2) :: rest) ∧
        rest.length + 1 = gs.length ∧
        ∀ mode, NoRawJoin mode gs → NoRawJoin mode rest := by
    obtain ⟨r, hi, hj, inv, bij, symm⟩ := orbit i j hne
    let rs := gs.map (spin r)
    let first := raw op 0 (if Edge i j then 1 else 2)
    have htr : Trace base rs := trace_spin_base hs.1.1 r
    have hfirst : first ∈ rs := by
      have h := List.mem_map_of_mem (f := spin r) hw
      rwa [spin_raw, hi, hj] at h
    have hstep : Step base first := by
      cases op
      · exact raw_join _ _
      · exact raw_meet _ _
    obtain ⟨rest, sz, tr, hm⟩ := move_first htr hfirst hstep
    have hf : target ∈ base ++ first :: rest := by
      have h := List.mem_append.mp hs.1.2
      rcases h with x | x
      · exact not_base x |>.elim
      · have y : spin r target ∈ rs := List.mem_map_of_mem x
        rw [inv] at y
        exact List.mem_append_right _ ((hm _).2 y)
    have len : rest.length + 1 = gs.length := by
      simpa [rs] using sz.symm
    refine ⟨rest, ⟨⟨tr, hf⟩, ?_⟩, len, ?_⟩
    · intro t ht
      simpa [len, Nat.add_comm] using hs.2 t ht
    · intro mode forbid w hw
      exact spin_exclusion bij symm forbid w ((hm _).1 (List.mem_cons_of_mem _ hw))

  let Normal (w : Wire) (gs : List Wire) : Prop :=
    ∀ j : Fin gs.length,
      let p := (base ++ [w]) ++ gs.take j.val
      gs.get j ∉ p ∧ Step p (gs.get j)

  have normal_of_minimal {w : Wire} {gs : List Wire} (hs : Smallest (w :: gs)) :
      Normal w gs := by
    intro i
    exact ⟨by simpa [List.append_assoc] using shortest_fresh (gs := w :: gs) hs i.succ,
      trace_indexed hs.1.1.2 i⟩

  have target_ne_raw_join (i j : Fin 10) : target ≠ join (pin i) (pin j) := by
    have hp : ∀ k : Fin 10, target (fun t => decide (t = k)) = false := by decide
    intro h
    have hx := congrFun h (fun t => decide (t = i))
    simp [hp, join, pin] at hx

  have target_ne_raw_and : target ≠ meet (pin 0) (pin 1) := by
    intro h
    have hx := congrFun h (pair (1, 2))
    exact (by decide : target (pair (1, 2)) ≠ meet (pin 0) (pin 1) (pair (1, 2))) hx

  have out_in_rest {w : Wire} {gs : List Wire} (hs : Smallest (w :: gs))
      (ne : target ≠ w) : target ∈ gs := by
    rcases List.mem_append.mp hs.1.2 with hab | hab
    · exact (not_base hab).elim
    · rcases List.mem_cons.mp hab with hab | hab
      · exact (ne hab).elim
      · exact hab


  let NoNonedgeMeet (gs : List Wire) : Prop :=
    ∀ w ∈ gs, ∀ i j : Fin 10, i ≠ j → ¬ Edge i j → w ≠ meet (pin i) (pin j)

  have smallest_no_nonedge_meet {gs : List Wire} (hs : Smallest gs) : NoNonedgeMeet gs := by
    intro w hw i j ne noEq eq
    subst w
    obtain ⟨rest, len, ht, hm⟩ := move_first hs.1.1 hw (raw_meet i j)
    have hf : target ∈ base ++ meet (pin i) (pin j) :: rest := by
      rcases List.mem_append.mp hs.1.2 with hf | hf
      · exact (not_base hf).elim
      · exact List.mem_append_right _ ((hm _).2 hf)
    obtain ⟨rest', len', ht', hf'⟩ := delete_nonedge i j ne noEq rest ht hf
    have h := hs.2 rest' ⟨ht', hf'⟩
    omega

  have tail_no_nonedge_meet {w : Wire} {gs : List Wire} (hs : Smallest (w :: gs)) :
      NoNonedgeMeet gs := by
    intro a ha
    exact smallest_no_nonedge_meet hs a (List.mem_cons_of_mem _ ha)

  have exclude (firstEdge : ∀ gs, gs.length ≤ 18 → Normal (raw false 0 1) gs →
        NoNonedgeMeet gs → target ∉ gs)
      (firstNonedge : ∀ gs, gs.length ≤ 18 → Normal (raw false 0 2) gs →
        NoNonedgeMeet gs → NoRawJoin true gs → target ∉ gs)
      (firstAnd : ∀ gs, gs.length ≤ 18 → Normal (raw true 0 1) gs →
        NoNonedgeMeet gs → NoRawJoin false gs → target ∉ gs)
      {gs : List Wire} (hs : Solves gs) (budget : gs.length ≤ 19) : False := by
    obtain ⟨gs, hm, hlen⟩ := smallest_of_exists gs hs
    have bound := hlen.trans budget
    by_cases edgeJoin : ∃ i j : Fin 10, i ≠ j ∧ Edge i j ∧ raw false i j ∈ gs
    · obtain ⟨i, j, ne, edge, mem⟩ := edgeJoin
      obtain ⟨rest, minR, lenR, _⟩ := transport hm false ne mem
      rw [ite_eq_left edge] at minR
      exact firstEdge rest (by omega) (normal_of_minimal minR) (tail_no_nonedge_meet minR)
        (out_in_rest minR (target_ne_raw_join 0 1))
    have noEdge : NoRawJoin true gs := by
      intro w hw i j ne edge eq
      exact edgeJoin ⟨i, j, ne, edge rfl, (show join (pin i) (pin j) ∈ gs from eq ▸ hw)⟩
    by_cases someJoin : ∃ i j : Fin 10, i ≠ j ∧ raw false i j ∈ gs
    · obtain ⟨i, j, ne, mem⟩ := someJoin
      have notEdge : ¬ Edge i j := fun he => edgeJoin ⟨i, j, ne, he, mem⟩
      obtain ⟨rest, minR, lenR, noR⟩ := transport hm false ne mem
      rw [ite_eq_right notEdge] at minR
      exact firstNonedge rest (by omega) (normal_of_minimal minR) (tail_no_nonedge_meet minR)
        (noR _ noEdge)
        (out_in_rest minR (target_ne_raw_join 0 2))
    have noJoin : NoRawJoin false gs := by
      intro w hw i j ne _ eq
      exact someJoin ⟨i, j, ne, (show join (pin i) (pin j) ∈ gs from eq ▸ hw)⟩
    cases gs with
    | nil => exact not_base (by simpa using hm.1.2)
    | cons w gs =>
      have fresh : w ∉ base := shortest_fresh (gs := w :: gs) hm ⟨0, by simp⟩
      rcases classify_first hm.1.1.1 with hw | ⟨i, j, ne, hw | hw⟩
      · exact fresh hw
      · subst w
        by_cases edge : Edge i j
        · have mem : raw true i j ∈ meet (pin i) (pin j) :: gs := List.mem_cons_self
          obtain ⟨rest, minR, lenR, noR⟩ := transport hm true ne mem
          rw [ite_eq_left edge] at minR
          simp only [List.length_cons] at lenR bound
          exact firstAnd rest (by omega) (normal_of_minimal minR) (tail_no_nonedge_meet minR)
            (noR _ noJoin)
            (out_in_rest minR target_ne_raw_and)
        · obtain ⟨rest, sz, tr, hf⟩ := delete_nonedge i j ne edge gs hm.1.1 hm.1.2
          have hsize := hm.2 rest ⟨tr, hf⟩
          simp only [List.length_cons, sz] at hsize
          omega
      · exact someJoin ⟨i, j, ne, List.mem_cons.mpr (Or.inl hw.symm)⟩

  have same : ∀ x, C.eval (List.ofFn x) = target x := by
    intro x
    rw [comp x]
    simp only [target, edges, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  obtain ⟨gs, len, tr, hout⟩ := circuit_trace C mono target same
  apply exclude _ _ _ ⟨tr, hout⟩ (len.trans_le budget)
  · exact edgeOr
  · intro gs sz normal nom no
    apply nonedgeOr gs sz normal
    intro w hw i j ne
    exact ⟨nom w hw i j ne, fun edge => no w hw i j ne (fun _ => edge)⟩
  · intro gs sz normal nom no
    apply edgeAnd gs sz normal
    intro w hw i j ne
    exact ⟨nom w hw i j ne, no w hw i j ne (by intro impossible; cases impossible)⟩

