import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2200000 in
theorem PEqualNP.Outside.R_meta_8193_451
    (small : ∀ X Y : Fin 21 → Bool,
      (∀ p l : Fin 21, p-l ∈ ([0, 1, 4, 14, 16] : List (Fin 21)) → X p = false ∨ Y l = false) →
      (List.ofFn X).count true ≤ 6 ∨ (List.ofFn Y).count true ≤ 6)
    (search :
      let offsets : List (Fin 21) := [0, 1, 4, 14, 16]
      let off (s : Bool) (X : Fin 21 → Bool) (i : Fin 21) :=
        !(offsets.any fun d => X (if s then i+d else i-d))
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 124 ∧
        (∀ p l : Fin 21, p-l ∈ offsets →
          C.eval (List.ofFn (Fin.append (fun i => decide (i=p)) (fun i => decide (i=l)))) = true) ∧
        ∀ X : Fin 21 → Bool, (List.ofFn X).count true ≤ 6 →
          C.eval (List.ofFn (Fin.append X (off true X))) = false ∧
          C.eval (List.ofFn (Fin.append (off false X) X)) = false) :
    have x1 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x1 x2 : Fin (21 : ℕ)) => x1 - x2 ∈ [(0 : Fin (21 : ℕ)), (1 : Fin (21 : ℕ)), (4 : Fin (21 : ℕ)), (14 : Fin (21 : ℕ)), (16 : Fin (21 : ℕ))]; have x2 : (Fin (21 : ℕ) → Bool) → Fin (21 : ℕ) → Bool := fun (x2 : Fin (21 : ℕ) → Bool) (x3 : Fin (21 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (21 : ℕ))) || x2 (x3 + (4 : Fin (21 : ℕ))) || x2 (x3 + (14 : Fin (21 : ℕ))) || x2 (x3 + (16 : Fin (21 : ℕ)))); ∃ x3 ≤ (124 : ℕ), ∃ (x4 : ℕ → Set ((Fin (21 : ℕ) × Fin (21 : ℕ)) × (Fin (21 : ℕ) → Bool))), (∀ (x5 : Fin (21 : ℕ)), ∀ x6 ∈ x4 ↑x5, x6.1.1 = x5 ∧ x6.2 x5 = Bool.false) ∧ (∀ (x5 : Fin (21 : ℕ)), ∀ x6 ∈ x4 ((21 : ℕ) + ↑x5), x6.1.2 = x5 ∧ x2 x6.2 x5 = Bool.false) ∧ (∀ x5 < x3, (∀ x7 ∈ x4 ((42 : ℕ) + x5), ∀ x9 ∈ x4 ((42 : ℕ) + x5), (x7.1, x9.2) ∈ x4 ((42 : ℕ) + x5)) ∧ ∃ x7 < (42 : ℕ) + x5, ∃ x8 < (42 : ℕ) + x5, x4 ((42 : ℕ) + x5) ⊆ x4 x7 ∪ x4 x8) ∧ ∃ x5 < (42 : ℕ) + x3, ∀ (x6 x7 : Fin (21 : ℕ)), x1 x6 x7 → ∀ (x9 : Fin (21 : ℕ) → Bool), (∀ (x10 : Fin (21 : ℕ)), x9 x10 = Bool.false → ∃ (x12 : Fin (21 : ℕ)), x1 x10 x12 ∧ x2 x9 x12 = Bool.true) → ((x6, x7), x9) ∈ x4 x5 := by
  have circuitRectangles (n : ℕ) (hn : 0 < n) (α β : Type)
      (P : α → List Bool) (B : β → List Bool)
      (pLen : ∀ a, (P a).length = n) (bLen : ∀ b, (B b).length = n)
      (C : Circuit) (fan : Monotone2 C) :
      ∃ R : ℕ → Set (α × β),
        (∀ i < n, ∀ z ∈ R i, (P z.1).getD i false = true ∧ (B z.2).getD i false = false) ∧
        (∀ j < C.size,
          (∀ x ∈ R (n + j), ∀ y ∈ R (n + j), (x.1, y.2) ∈ R (n + j)) ∧
          ∃ a < n+j, ∃ b < n+j, R (n+j) ⊆ R a ∪ R b) ∧
        ∀ a b, C.eval (P a) = true → C.eval (B b) = false →
          C.output < n + C.size ∧ (a,b) ∈ R C.output := by
    let run : List Bool → Gate → List Bool := fun w g =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have length (gs : List Gate) (w : List Bool) : (gs.foldl run w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp only [run, List.length_append, List.length_cons, List.length_nil]
        omega
    have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl run w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih (run w g) (by simp [run]; omega)]
        exact List.getD_append _ _ _ _ hi
    let sig (x : List Bool) (i : ℕ) := (C.wires x).getD i false
    let R (i : ℕ) : Set (α × β) := {z | sig (P z.1) i = true ∧ sig (B z.2) i = false}
    refine ⟨R, ?_, ?_, ?_⟩
    · intro i hi z hz
      change sig (P z.1) i = true ∧ sig (B z.2) i = false at hz
      have keepP := keep C.gates (P z.1) i (by rw [pLen]; exact hi)
      have keepB := keep C.gates (B z.2) i (by rw [bLen]; exact hi)
      change sig (P z.1) i = (P z.1).getD i false at keepP
      change sig (B z.2) i = (B z.2).getD i false at keepB
      rwa [keepP, keepB] at hz
    · intro j hj
      refine ⟨fun x hx y hy => ⟨hx.1,hy.2⟩, ?_⟩
      let g := C.gates[j]'hj
      let pre := C.gates.take j
      let post := C.gates.drop (j+1)
      have split : pre ++ g :: post = C.gates := by
        change C.gates.take j ++ _ = _
        rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
      let beforeGate (w : List Bool) := pre.foldl run w
      have len (w : List Bool) (hw : w.length = n) : (beforeGate w).length = n+j := by
        change (pre.foldl run w).length = _
        rw [length, hw]
        have jlt : j < C.gates.length := hj
        simp only [pre, List.length_take, Nat.min_eq_left jlt.le]
      have whole (w : List Bool) : C.wires w = post.foldl run (run (beforeGate w) g) := by
        change C.gates.foldl run w = _
        conv_lhs => rw [← split, List.foldl_append, List.foldl_cons]
      have below (w : List Bool) (hw : w.length = n) (i : ℕ) (hi : i < n+j) :
          (beforeGate w).getD i false = sig w i := by
        change _ = (C.wires w).getD i false
        rw [whole, keep post _ i (by simp [run,len w hw]; omega)]
        exact (List.getD_append _ _ _ _ (by rw [len w hw]; exact hi)).symm
      have value (w : List Bool) (hw : w.length = n) :
          sig w (n+j) = g.op.eval (g.inputs.map fun i => (beforeGate w).getD i false) := by
        change (C.wires w).getD (n+j) false = _
        rw [whole, keep post _ (n+j) (by simp [run,len w hw])]
        change ((beforeGate w) ++ [_]).getD (n+j) false = _
        rw [List.getD_append_right _ _ _ _ (by rw [len w hw]), len w hw, Nat.sub_self]
        rfl
      have opLen := fan g (List.getElem_mem hj)
      have gateOp : g.op = .and ∨ g.op = .or := by simpa using opLen.1
      let hook (i : ℕ) := if i < n+j then i else 0
      have hookBound (i : ℕ) : hook i < n+j := by
        dsimp only [hook]
        split <;> omega
      have member (i : ℕ) (hi : i ∈ g.inputs) :
          i = g.inputs.getD 0 0 ∨ i = g.inputs.getD 1 0 := by
        have bound := opLen.2
        cases h : g.inputs with
        | nil => simp [h] at hi
        | cons a tail =>
          cases ht : tail with
          | nil => simp [h,ht] at hi ⊢; exact Or.inl hi
          | cons b tail =>
            cases tail with
            | nil => simpa [h,ht] using hi
            | cons c rest =>
              rw [h,ht] at bound
              simp at bound
      refine ⟨hook (g.inputs.getD 0 0), hookBound _, hook (g.inputs.getD 1 0), hookBound _, ?_⟩
      intro z hz
      have hpos := hz.1
      have hneg := hz.2
      change sig (P z.1) (n+j) = true at hpos
      change sig (B z.2) (n+j) = false at hneg
      rw [value _ (pLen _)] at hpos
      rw [value _ (bLen _)] at hneg
      let zp := fun i => (beforeGate (P z.1)).getD i false
      let zn := fun i => (beforeGate (B z.2)).getD i false
      have one : ∃ i ∈ g.inputs, zp i = true ∧ zn i = false := by
        rcases gateOp with and | or
        · rw [and] at hpos hneg
          change (g.inputs.map zp).all id = true at hpos
          change (g.inputs.map zn).all id = false at hneg
          have positive (i : ℕ) (hi : i ∈ g.inputs) : zp i = true :=
            List.all_eq_true.mp hpos _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
          have someFalse : ∃ i ∈ g.inputs, zn i = false := by
            by_contra none
            have allTrue : (g.inputs.map zn).all id = true := by
              apply List.all_eq_true.mpr
              intro b hb
              obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
              cases he : zn i
              · exact False.elim (none ⟨i,hi,he⟩)
              · rfl
            rw [hneg] at allTrue
            cases allTrue
          obtain ⟨i,hi,value⟩ := someFalse
          exact ⟨i,hi,positive i hi,value⟩
        · rw [or] at hpos hneg
          change (g.inputs.map zp).any id = true at hpos
          change (g.inputs.map zn).any id = false at hneg
          obtain ⟨v,hv,vtrue⟩ := List.any_eq_true.mp hpos
          obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
          have no : zn i = false := by
            cases he : zn i
            · rfl
            · have yes : (g.inputs.map zn).any id = true :=
                List.any_eq_true.mpr ⟨zn i,List.mem_map.mpr ⟨i,hi,rfl⟩,he⟩
              rw [hneg] at yes
              cases yes
          exact ⟨i,hi,vtrue,no⟩
      obtain ⟨i,hi,pos,neg⟩ := one
      have idx : i < n+j := by
        by_contra! big
        change (beforeGate (P z.1)).getD i false = true at pos
        rw [List.getD_eq_default _ _ (by rw [len _ (pLen _)]; exact big)] at pos
        cases pos
      have inR : z ∈ R (hook i) := by
        change sig (P z.1) _ = true ∧ sig (B z.2) _ = false
        rw [show hook i = i by simp [hook,idx], ← below _ (pLen _) _ idx, ← below _ (bLen _) _ idx]
        exact ⟨pos,neg⟩
      rcases member i hi with eq | eq
      · exact Or.inl (eq ▸ inR)
      · exact Or.inr (eq ▸ inR)
    · intro a b yes no
      have bound : C.output < n + C.size := by
        by_contra! tooLarge
        have l : (C.wires (P a)).length = n + C.size := by
          exact (length C.gates (P a)).trans (by rw [pLen]; rfl)
        change (C.wires (P a)).getD C.output false = true at yes
        rw [List.getD_eq_default _ _ (by rw [l]; exact tooLarge)] at yes
        cases yes
      exact ⟨bound,yes,no⟩
  let offsets : List (Fin 21) := [0, 1, 4, 14, 16]
  let incident (p l : Fin 21) := p-l ∈ offsets
  let off (s : Bool) (X : Fin 21 → Bool) (i : Fin 21) :=
    !(offsets.any fun d => X (if s then i+d else i-d))
  let Z (X : Fin 21 → Bool) (l : Fin 21) :=
    !(X l || X (l+1) || X (l+4) || X (l+14) || X (l+16))
  let posInput (e : Fin 21 × Fin 21) : List Bool :=
    List.ofFn (Fin.append (fun i => decide (i=e.1)) (fun i => decide (i=e.2)))
  let negInput (X : Fin 21 → Bool) : List Bool :=
    List.ofFn (Fin.append X (Z X))
  have offLeft (X : Fin 21 → Bool) (l : Fin 21) : off true X l = Z X l := by
    simp only [off, offsets, Z, List.any_cons, List.any_nil, Bool.or_false,
      ite_true, add_zero, Bool.or_assoc]
  have misses (X : Fin 21 → Bool) {p l : Fin 21} (hit : incident p l)
      (free : Z X l = true) : X p = false := by
    cases hx : X p
    · rfl
    · have shift : l + (p-l) = p := by abel
      have present : (offsets.any fun d => X (if true then l+d else l-d)) = true :=
        List.any_eq_true.mpr ⟨p-l,hit,by simp only [ite_true,shift,hx]⟩
      rw [← offLeft] at free
      change !(offsets.any fun d => X (if true then l+d else l-d)) = true at free
      rw [present] at free
      cases free
  have dual (X : Fin 21 → Bool)
      (closed : ∀ p, X p=false → ∃ l, incident p l ∧ Z X l=true) :
      off false (Z X) = X := by
    funext p
    change (!(offsets.any fun d => Z X (p-d))) = X p
    cases hx : X p
    · obtain ⟨l,hit,free⟩ := closed p hx
      have shift : p-(p-l) = l := by abel
      have has : (offsets.any fun d => Z X (p-d)) = true :=
        List.any_eq_true.mpr ⟨p-l,hit,by rw [shift]; exact free⟩
      rw [has]
      rfl
    · cases has : (offsets.any fun d => Z X (p-d))
      · rfl
      · obtain ⟨d,hd,free⟩ := List.any_eq_true.mp has
        have shift : p-(p-d) = d := by abel
        have hit : incident p (p-d) := by
          change p-(p-d) ∈ offsets
          rwa [shift]
        have impossible := misses X hit free
        rw [hx] at impossible
        cases impossible
  obtain ⟨C,fan,cap,accept,reject⟩ := search
  have right (X : Fin 21 → Bool)
      (closed : ∀ p, X p=false → ∃ l, incident p l ∧ Z X l=true) :
      C.eval (negInput X) = false := by
    have independent (p l : Fin 21) (hit : incident p l) : X p=false ∨ Z X l=false := by
      cases hl : Z X l
      · exact Or.inr rfl
      · exact Or.inl (misses X hit hl)
    rcases small X (Z X) independent with hX | hZ
    · have h := (reject X hX).1
      change C.eval (List.ofFn (Fin.append X (off true X))) = false at h
      have equal : off true X = Z X := funext (offLeft X)
      rw [equal] at h
      exact h
    · have h := (reject (Z X) hZ).2
      change C.eval (List.ofFn (Fin.append (off false (Z X)) (Z X))) = false at h
      rw [dual X closed] at h
      exact h
  obtain ⟨R, leaf, splits, output⟩ := circuitRectangles 42 (by decide)
    (Fin 21 × Fin 21) (Fin 21 → Bool) posInput negInput
    (fun _ => List.length_ofFn) (fun _ => List.length_ofFn) C fan
  have validOutput : C.output < 42 + C.size :=
    (output (0,0) (fun _ => true) (accept 0 0 (by decide)) (right _ (by simp))).1
  have readInput (x : Fin 42 → Bool) (i : Fin 42) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  refine ⟨C.size, cap, R, ?_, ?_, splits, C.output, validOutput, ?_⟩
  · intro p z hz
    have h := leaf p.val (by have := p.isLt; omega) z hz
    have eqp := readInput (Fin.append (fun i => decide (i=z.1.1)) (fun i => decide (i=z.1.2))) (Fin.castAdd 21 p)
    have eqn := readInput (Fin.append z.2 (Z z.2)) (Fin.castAdd 21 p)
    change (posInput z.1).getD p.val false = _ at eqp
    change (negInput z.2).getD p.val false = _ at eqn
    rw [eqp,eqn] at h
    simp only [Fin.append_left, decide_eq_true_eq] at h
    exact ⟨h.1.symm, h.2⟩
  · intro l z hz
    have h := leaf (21+l.val) (by have := l.isLt; omega) z hz
    have eqp := readInput (Fin.append (fun i => decide (i=z.1.1)) (fun i => decide (i=z.1.2))) (Fin.natAdd 21 l)
    have eqn := readInput (Fin.append z.2 (Z z.2)) (Fin.natAdd 21 l)
    change (posInput z.1).getD (21+l.val) false = _ at eqp
    change (negInput z.2).getD (21+l.val) false = _ at eqn
    rw [eqp,eqn] at h
    simp only [Fin.append_right, decide_eq_true_eq] at h
    exact ⟨h.1.symm, h.2⟩
  · intro p l hit X closed
    exact (output (p,l) X (accept p l hit) (right X closed)).2
