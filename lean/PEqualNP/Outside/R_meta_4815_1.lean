import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- On every positive edge input the supplied nonedge AND is false. An
-- AND/OR continuation still computes the function when that signal is
-- replaced by false, so the first gate can be deleted from that case.
-- The other continuations use the pair stabilizer, or discard a copied wire.
set_option maxHeartbeats 6500000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_4815_1
    (monoBound : ∀ C : Circuit, Monotone2 C → C.size ≤ 18 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (copied : ∀ C : Circuit, FanInTwo C → ¬ Monotone2 C → C.size ≤ 17 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 && x 2, false]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (properOr : ∀ (C : Circuit) (p : Fin 121), p ∈ [1, 2, 3, 4, 6, 8, 14, 17, 19, 21, 37, 38, 39, 40, 41, 42, 43, 74, 76, 97, 98] →
      FanInTwo C → ¬ Monotone2 C → C.size ≤ 17 →
      ∃ x : Fin 10 → Bool,
        let w := List.ofFn x ++ [x 0 && x 2]
        C.eval (w ++ [w.getD (p.val / 11) false || w.getD (p.val % 11) false]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (12 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ (x6 : Fin (10 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))];           x1.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : Fin (12 : ℕ)) => x7.getD (↑x8) Bool.false) x2)]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x6 := by
  intro C pins fan size atMost
  by_contra noWitness
  let es : List (Fin 10 × Fin 10) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
  let target (x : Fin 10 → Bool) := es.any fun e => x e.1 && x e.2
  let hint (x : Fin 10 → Bool) := x 0 && x 2
  let seed (x : Fin 10 → Bool) (b : Bool) := List.ofFn x ++ [b]
  let read (x : Fin 10 → Bool) (b : Bool) (i : ℕ) :=
    if hi : i < 10 then x ⟨i,hi⟩ else if i = 10 then b else false
  have seedLen (x : Fin 10 → Bool) (b : Bool) : (seed x b).length = 11 := by
    simp [seed]
  have readSeed (x : Fin 10 → Bool) (b : Bool) (i : ℕ) :
      (seed x b).getD i false = read x b i := by
    by_cases lt : i < 10
    · rw [show read x b i = x ⟨i,lt⟩ by simp [read,lt]]
      change (List.ofFn x ++ [b]).getD i false = _
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using lt)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, lt, dite_true, Option.getD_some]
    · by_cases hi : i = 10
      · subst i
        change (List.ofFn x ++ [b]).getD 10 false = _
        rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self]
        rfl
      · have hlen : (seed x b).length ≤ i := by rw [seedLen]; omega
        rw [List.getD_eq_default _ _ hlen]
        simp [read, lt, hi]
  let fed (x : Fin 10 → Bool) (b : Bool) :=
    seed x b ++ [GateOp.or.eval (pins.map fun i => (seed x b).getD i.val false)]
  have targetFormula (x : Fin 10 → Bool) : target x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    simp only [target, es, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  have computes (x : Fin 10 → Bool) : C.eval (fed x (hint x)) = target x := by
    by_contra bad
    apply noWitness
    refine ⟨x, ?_⟩
    dsimp only
    rw [← targetFormula x]
    exact bad
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let reroute (n q : ℕ) (r : Fin n → ℕ) (i : ℕ) :=
    if h : i < n then r ⟨i,h⟩ else q + (i - n)
  let mapGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩
  let mapCircuit (n q : ℕ) (r : Fin n → ℕ) (D : Circuit) : Circuit :=
    ⟨D.gates.map (mapGate (reroute n q r)), reroute n q r D.output⟩
  have foldMap (n q : ℕ) (r : Fin n → ℕ) (gs : List Gate) (t : ℕ)
      (old fresh : List Bool) (ho : old.length = n+t) (hf : fresh.length = q+t)
      (slots : ∀ i, r i < q ∨ q+t+gs.length ≤ r i)
      (known : ∀ i, fresh.getD (reroute n q r i) false = old.getD i false) :
      ∀ i, ((gs.map (mapGate (reroute n q r))).foldl step fresh).getD (reroute n q r i) false =
        (gs.foldl step old).getD i false := by
    induction gs generalizing t old fresh with
    | nil => exact known
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih (t+1)
      · simp [step, ho, Nat.add_assoc]
      · simp [step, hf, Nat.add_assoc]
      · intro i
        rcases slots i with h | h
        · exact Or.inl h
        · exact Or.inr (by simp only [List.length_cons] at h; omega)
      · intro i
        change (fresh ++ [_]).getD (reroute n q r i) false = (old ++ [_]).getD i false
        by_cases hn : i < n
        · have atOld : i < old.length := by omega
          rw [List.getD_append _ _ _ _ atOld]
          have eq : reroute n q r i = r ⟨i,hn⟩ := by simp [reroute,hn]
          rcases slots ⟨i,hn⟩ with h | h
          · rw [List.getD_append _ _ _ _ (by rw [eq,hf]; omega)]
            exact known i
          · have past : q + t + 1 ≤ reroute n q r i := by
              simp only [List.length_cons] at h
              rw [eq]
              omega
            have basePast : fresh.length ≤ reroute n q r i := by rw [hf]; omega
            rw [List.getD_eq_default _ _ (by simpa [hf, Nat.add_assoc] using past),
              ← known i, List.getD_eq_default _ _ basePast]
        · have eq : reroute n q r i = q + (i-n) := by simp [reroute,hn]
          by_cases hi : i < old.length
          · rw [List.getD_append _ _ _ _ (by rw [eq,hf]; omega), List.getD_append _ _ _ _ hi]
            exact known i
          · have hnew : fresh.length ≤ reroute n q r i := by rw [eq,hf]; omega
            have hoff : reroute n q r i - fresh.length = i - old.length := by rw [eq,ho,hf]; omega
            rw [List.getD_append_right _ _ _ _ hnew, List.getD_append_right _ _ _ _ (by omega), hoff]
            have same : (mapGate (reroute n q r) g).op.eval
                ((mapGate (reroute n q r) g).inputs.map (fun j => fresh.getD j false)) =
                g.op.eval (g.inputs.map (fun j => old.getD j false)) := by
              simp only [mapGate,List.map_map]
              congr 1
              exact List.map_congr_left (fun j _ => known j)
            rw [same]
  have mapEval (n q : ℕ) (r : Fin n → ℕ) (D : Circuit) (old fresh : List Bool)
      (ho : old.length = n) (hf : fresh.length = q)
      (slots : ∀ i, r i < q ∨ q+D.gates.length ≤ r i)
      (reads : ∀ i, fresh.getD (r i) false = old.getD i.val false) :
      (mapCircuit n q r D).eval fresh = D.eval old := by
    have known (i : ℕ) : fresh.getD (reroute n q r i) false = old.getD i false := by
      by_cases hi : i < n
      · simpa only [reroute,hi,dite_true] using reads ⟨i,hi⟩
      · have hnew : fresh.length ≤ reroute n q r i := by simp [reroute,hf,hi]
        rw [List.getD_eq_default _ _ hnew,List.getD_eq_default _ _ (by omega)]
    exact foldMap n q r D.gates 0 old fresh (by simpa using ho) (by simpa using hf)
      (by simpa using slots) known D.output
  have mapFan (n q : ℕ) (r : Fin n → ℕ) (D : Circuit) (hD : FanInTwo D) :
      FanInTwo (mapCircuit n q r D) := by
    intro g hg
    change g ∈ D.gates.map (mapGate (reroute n q r)) at hg
    obtain ⟨old,member,rfl⟩ := List.mem_map.mp hg
    simpa [mapGate] using hD old member
  have mapMono (n q : ℕ) (r : Fin n → ℕ) (D : Circuit) :
      Monotone2 (mapCircuit n q r D) ↔ Monotone2 D := by
    constructor
    · intro h g hg
      have hm := h (mapGate (reroute n q r) g) (List.mem_map_of_mem hg)
      simpa [mapGate] using hm
    · intro h g hg
      change g ∈ D.gates.map (mapGate (reroute n q r)) at hg
      obtain ⟨old,member,rfl⟩ := List.mem_map.mp hg
      simpa [mapGate] using h old member
  have mapSize (n q : ℕ) (r : Fin n → ℕ) (D : Circuit) :
      (mapCircuit n q r D).size = D.size := by
    change (D.gates.map (mapGate (reroute n q r))).length = D.gates.length
    exact List.length_map _
  have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have andEval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have orPair (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by
    cases a <;> cases b <;> rfl
  have orSingle (a : Bool) : GateOp.or.eval [a] = a := by
    cases a <;> rfl
  by_cases mono : Monotone2 C
  · let Le (l r : List Bool) := ∀ i, l.getD i false = true → r.getD i false = true
    have extend {l r : List Bool} {a b : Bool} (len : l.length = r.length) (le : Le l r)
        (value : a = true → b = true) : Le (l ++ [a]) (r ++ [b]) := by
      intro i hit
      by_cases hi : i < l.length
      · rw [List.getD_append _ _ _ _ (by rw [← len]; exact hi)]
        rw [List.getD_append _ _ _ _ hi] at hit
        exact le i hit
      · have leLen : l.length ≤ i := by omega
        rw [List.getD_append_right _ _ _ _ leLen] at hit
        rw [List.getD_append_right _ _ _ _ (by omega), ← len]
        by_cases eq : i = l.length
        · have e : i - l.length = 0 := by omega
          rw [e] at hit ⊢
          exact value hit
        · have after : [a].length ≤ i - l.length := by simp; omega
          rw [List.getD_eq_default _ _ after] at hit
          contradiction
    have gateLe (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) (l r : List Bool)
        (le : Le l r) :
        g.op.eval (g.inputs.map fun i => l.getD i false) = true →
          g.op.eval (g.inputs.map fun i => r.getD i false) = true := by
      rcases h with h | h
      · simp only [h,andEval,List.all_map]
        rw [List.all_eq_true,List.all_eq_true]
        exact fun hit i hi => le i (hit i hi)
      · simp only [h,orEval,List.any_map]
        rw [List.any_eq_true,List.any_eq_true]
        rintro ⟨i,hi,hit⟩
        exact ⟨i,hi,le i hit⟩
    have foldLe (gs : List Gate) (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
        (l r : List Bool) (len : l.length = r.length) (le : Le l r) :
        Le (gs.foldl step l) (gs.foldl step r) := by
      induction gs generalizing l r with
      | nil => exact le
      | cons g gs ih =>
        simp only [List.foldl_cons]
        exact ih (fun h hmem => ops h (List.mem_cons_of_mem _ hmem)) _ _
          (by simp [step,len])
          (extend len le (gateLe g (ops g (List.mem_cons_self ..)) l r le))
    let g : Gate := ⟨GateOp.or,pins.map Fin.val⟩
    have gmono : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      simpa [g] using atMost
    have feedLe (x y : Fin 10 → Bool) (a b : Bool) (xy : ∀ i, x i = true → y i = true)
        (ab : a = true → b = true) : Le (fed x a) (fed y b) := by
      have base : Le (seed x a) (seed y b) := by
        intro i hit
        simp only [readSeed] at hit ⊢
        by_cases small : i < 10
        · simp only [read,small,dite_true] at hit ⊢
          exact xy _ hit
        · by_cases eq : i = 10
          · simp only [read,eq,ite_true] at hit ⊢
            exact ab hit
          · simp [read,small,eq] at hit
      have edge : g.op.eval (g.inputs.map fun i => (seed x a).getD i false) = true →
          g.op.eval (g.inputs.map fun i => (seed y b).getD i false) = true :=
        gateLe g (Or.inr rfl) _ _ base
      have full := extend ((seedLen x a).trans (seedLen y b).symm) base edge
      simpa only [fed, g, List.map_map, Function.comp_def] using full
    have feedLen (x : Fin 10 → Bool) (b : Bool) : (fed x b).length = 12 := by
      simp [fed, seedLen]
    have monotoneEval (x y : Fin 10 → Bool) (a b : Bool)
        (xy : ∀ i, x i = true → y i = true) (ab : a = true → b = true) :
        C.eval (fed x a) = true → C.eval (fed y b) = true :=
      foldLe C.gates (fun g hg => by simpa using (mono g hg).1)
        _ _ ((feedLen x a).trans (feedLen y b).symm) (feedLe x y a b xy ab) C.output
    let justEdge (e : Fin 10 × Fin 10) (i : Fin 10) := decide (i = e.1 ∨ i = e.2)
    have noHint : ∀ e ∈ es, hint (justEdge e) = false := by
      dsimp [es, hint, justEdge]
      decide +kernel
    have correct (x : Fin 10 → Bool) : C.eval (fed x false) = target x := by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro h
        have h' := monotoneEval x x false (hint x) (fun _ hi => hi) (by simp) h
        exact (computes x).symm ▸ h'
      · intro h
        obtain ⟨e, he, heval⟩ := List.any_eq_true.mp h
        have both := Bool.and_eq_true_iff.mp heval
        have left : target (justEdge e) = true := by
          exact List.any_eq_true.mpr ⟨e,he,by simp [justEdge]⟩
        have h' := computes (justEdge e)
        rw [noHint e he, left] at h'
        refine monotoneEval (justEdge e) x false false (fun i hi => ?_) id h'
        have inEdge : i = e.1 ∨ i = e.2 := of_decide_eq_true hi
        exact inEdge.elim (fun eq => eq.symm ▸ both.1) (fun eq => eq.symm ▸ both.2)
    let drop (i : Fin 12) : ℕ := if i.val < 10 then i.val else if i.val = 10 then 100 else 10
    let D := mapCircuit 12 11 drop C
    let E : Circuit := ⟨g :: D.gates, D.output⟩
    have monoD := (mapMono 12 11 drop C).mpr mono
    have monoE : Monotone2 E := by
      intro k hk
      change k ∈ g :: D.gates at hk
      rcases List.mem_cons.mp hk with rfl | hm
      · exact gmono
      · exact monoD k hm
    have sizeE : E.size ≤ 18 := by
      change D.size + 1 ≤ 18
      have hd : D.size = C.size := mapSize _ _ _ _
      omega
    obtain ⟨x,hx⟩ := monoBound E monoE sizeE
    apply hx
    rw [← targetFormula x]
    let b := GateOp.or.eval (pins.map fun i => (seed x false).getD i.val false)
    have sameRaw (i : ℕ) : (List.ofFn x).getD i false = (seed x false).getD i false := by
      by_cases small : i < 10
      · exact (List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using small)).symm
      · rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt small),
          readSeed]
        simp [read,small]
    have sameGate : g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = b := by
      change GateOp.or.eval ((pins.map Fin.val).map (fun i => (List.ofFn x).getD i false)) = b
      simp only [b,List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => sameRaw i.val)
    change D.eval (List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)]) = target x
    rw [sameGate]
    refine (mapEval 12 11 drop C (fed x false) (List.ofFn x ++ [b]) (feedLen _ _) (by simp) ?_ ?_).trans
      (correct x)
    · intro i
      dsimp [drop]
      by_cases hi : i.val < 10
      · exact Or.inl (by simp [hi]; omega)
      · by_cases he : i.val = 10
        · change C.gates.length ≤ 17 at size
          exact Or.inr (by simp [he]; omega)
        · exact Or.inl (by simp [hi,he])
    · intro i
      by_cases hi : i.val < 10
      · rw [show drop i = i.val by simp [drop,hi],
          List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using hi)]
        change (List.ofFn x).getD i.val false = (seed x false ++ [b]).getD i.val false
        rw [List.getD_append _ _ _ _ (by rw [seedLen]; omega)]
        exact sameRaw i.val
      · by_cases he : i.val = 10
        · rw [show drop i = 100 by simp [drop,he], List.getD_eq_default _ _ (by simp)]
          change false = (seed x false ++ [b]).getD i.val false
          rw [List.getD_append _ _ _ _ (by rw [seedLen,he]; decide), readSeed,he]
          rfl
        · have last : i.val = 11 := by have := i.isLt; omega
          rw [show drop i = 10 by simp [drop,hi,he], last]
          change (List.ofFn x ++ [b]).getD 10 false = (seed x false ++ [b]).getD 11 false
          rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by rw [seedLen]),
            List.length_ofFn, seedLen]
  · let bank (x : Fin 10 → Bool) := seed x (hint x)
    have bankLen (x : Fin 10 → Bool) : (bank x).length = 11 := seedLen x _
    have bankEarly (x : Fin 10 → Bool) (b : Bool) (i : ℕ) (hi : i < 11) :
        (bank x ++ [b]).getD i false = (bank x).getD i false :=
      List.getD_append (bank x) [b] false i (by simpa only [bankLen] using hi)
    have bankLast (x : Fin 10 → Bool) (b : Bool) : (bank x ++ [b]).getD 11 false = b := by
      rw [List.getD_append_right (bank x) [b] false 11 (by rw [bankLen]), bankLen]
      rfl
    let duplicate (a : Fin 12) (i : Fin 12) : ℕ := if i.val < 11 then i.val else a.val
    have dropSecond (a : Fin 12)
        (given : ∀ x : Fin 10 → Bool, C.eval (bank x ++ [(bank x ++ [false]).getD a.val false]) = target x) :
        False := by
      let D := mapCircuit 12 12 (duplicate a) C
      have monoD : ¬ Monotone2 D := fun h => mono ((mapMono 12 12 (duplicate a) C).mp h)
      obtain ⟨x,hx⟩ := copied D (mapFan _ _ _ _ fan) monoD
        (by rw [mapSize]; exact size)
      apply hx
      rw [← targetFormula x]
      let u := bank x ++ [false]
      let v := bank x ++ [u.getD a.val false]
      have same : D.eval u = C.eval v := by
        apply mapEval 12 12 (duplicate a) C _ _ (by simp [v,bankLen]) (by simp [u,bankLen])
        · intro i
          left
          dsimp [duplicate]
          split
          · omega
          · exact a.isLt
        · intro i
          by_cases hi : i.val < 11
          · rw [show duplicate a i = i.val by simp [duplicate,hi]]
            exact (bankEarly x false i.val hi).trans (bankEarly x (u.getD a.val false) i.val hi).symm
          · have last : i.val = 11 := by have := i.isLt; omega
            rw [show duplicate a i = a.val by simp [duplicate,hi],last]
            exact (bankLast x (u.getD a.val false)).symm
      exact same.trans (given x)
    let perm (p : Fin 4) (i : Fin 10) : Fin 10 :=
      ((#[(#[0,1,2,3,4,5,6,7,8,9] : Array (Fin 10)),
        #[0,1,2,7,5,4,6,3,9,8], #[2,1,0,4,3,7,6,5,9,8],
        #[2,1,0,5,7,3,6,4,8,9]][p.val]?.getD #[])[i.val]?).getD 0
    let lift (p : Fin 4) (i : Fin 12) : ℕ := if h : i.val < 10 then (perm p ⟨i.val,h⟩).val else i.val
    let encode (a b : ℕ) : Fin 121 := Fin.ofNat 121 (11*a+b)
    let absorbing (i j : Fin 12) := (i = 10 ∧ (j = 0 ∨ j = 2)) ∨ (j = 10 ∧ (i = 0 ∨ i = 2))
    have fixes : ∀ p : Fin 4, (perm p 0 = 0 ∧ perm p 2 = 2) ∨ (perm p 0 = 2 ∧ perm p 2 = 0) := by
      dsimp [perm]
      decide +kernel
    have keepHint (p : Fin 4) (x : Fin 10 → Bool) : hint (x ∘ perm p) = hint x := by
      rcases fixes p with ⟨a,b⟩ | ⟨a,b⟩
      · simp [hint,Function.comp_apply,a,b]
      · simp [hint,Function.comp_apply,a,b,Bool.and_comm]
    have sends : ∀ (p : Fin 4) (u v : Fin 10), (u,v) ∈ es →
        (perm p u,perm p v) ∈ es ∨ (perm p v,perm p u) ∈ es := by
      dsimp [perm,es]
      decide +kernel
    have inverse : ∀ p : Fin 4, ∃ q : Fin 4, ∀ i : Fin 10, perm p (perm q i) = i := by
      dsimp [perm]
      decide +kernel
    have forward (p : Fin 4) (x : Fin 10 → Bool) : target (x ∘ perm p) = true → target x = true := by
      intro yes
      obtain ⟨⟨u,v⟩,he,hv⟩ := List.any_eq_true.mp yes
      exact (sends p u v he).elim
        (fun hm => List.any_eq_true.mpr ⟨(perm p u,perm p v),hm,hv⟩)
        (fun hm => List.any_eq_true.mpr ⟨(perm p v,perm p u),hm,by simpa only [Function.comp_apply,Bool.and_comm] using hv⟩)
    have keepTarget (p : Fin 4) (x : Fin 10 → Bool) : target (x ∘ perm p) = target x := by
      apply Bool.eq_iff_iff.mpr
      refine ⟨forward p x, ?_⟩
      intro yes
      obtain ⟨q,inv⟩ := inverse p
      have eq : (x ∘ perm p) ∘ perm q = x := by funext i; simp [Function.comp_apply,inv i]
      exact forward q (x ∘ perm p) (eq.symm ▸ yes)
    have readsLift (p : Fin 4) (i : Fin 12) (x : Fin 10 → Bool) :
        (bank x).getD (lift p i) false = (bank (x ∘ perm p)).getD i.val false := by
      change (seed x (hint x)).getD (lift p i) false = (seed (x ∘ perm p) (hint (x ∘ perm p))).getD i.val false
      rw [readSeed,readSeed,keepHint]
      by_cases raw : i.val < 10
      · have h : (perm p ⟨i.val,raw⟩).val < 10 := (perm p ⟨i.val,raw⟩).isLt
        simp only [lift,raw,dite_true,read,h,Function.comp_apply]
      · simp [lift,raw,read]
    have evalLift (p : Fin 4) (x : Fin 10 → Bool) (b : Bool) :
        (mapCircuit 12 12 (lift p) C).eval (bank x ++ [b]) = C.eval (bank (x ∘ perm p) ++ [b]) := by
      apply mapEval 12 12 (lift p) C _ _ (by simp [bankLen]) (by simp [bankLen])
      · intro i
        left
        dsimp [lift]
        split
        · exact Nat.lt_trans (Fin.isLt _) (by decide)
        · exact i.isLt
      · intro i
        by_cases early : i.val < 11
        · have h : lift p i < 11 := by
            dsimp [lift]
            split
            · exact Nat.lt_trans (Fin.isLt _) (by decide)
            · exact early
          rw [bankEarly x b (lift p i) h, bankEarly (x ∘ perm p) b i.val early]
          exact readsLift p i x
        · have last : i.val = 11 := by have := i.isLt; omega
          rw [show lift p i = 11 by simp [lift,last],last,bankLast,bankLast]
    have align : ∀ i j : Fin 12, i.val < 11 → j.val < 11 → i ≠ j → ¬ absorbing i j →
        ∃ p : Fin 4, (encode (lift p i) (lift p j) ∈ [1, 2, 3, 4, 6, 8, 14, 17, 19, 21, 37, 38, 39, 40, 41, 42, 43, 74, 76, 97, 98] ∧ lift p i < 11 ∧ lift p j < 11) ∨
          (encode (lift p j) (lift p i) ∈ [1, 2, 3, 4, 6, 8, 14, 17, 19, 21, 37, 38, 39, 40, 41, 42, 43, 74, 76, 97, 98] ∧ lift p j < 11 ∧ lift p i < 11) := by
      dsimp [encode,lift,perm,absorbing]
      decide +kernel
    have decode (a b : ℕ) (ha : a < 11) (hb : b < 11) :
        (encode a b).val / 11 = a ∧ (encode a b).val % 11 = b := by
      change (11 * a + b) % 121 / 11 = a ∧ (11 * a + b) % 121 % 11 = b
      rw [Nat.mod_eq_of_lt (by omega : 11*a+b < 121)]
      constructor <;> omega
    have excludePair (i j : Fin 12) (hi : i.val < 11) (hj : j.val < 11)
        (distinct : i ≠ j) (nonabs : ¬ absorbing i j)
        (guess : ∀ x, C.eval (bank x ++ [((bank x).getD i.val false || (bank x).getD j.val false)]) = target x) :
        False := by
      obtain ⟨p,choice⟩ := align i j hi hj distinct nonabs
      let D := mapCircuit 12 12 (lift p) C
      have dfan := mapFan 12 12 (lift p) C fan
      have dsign := fun h : Monotone2 D => mono ((mapMono 12 12 (lift p) C).mp h)
      have dsize : D.size ≤ 17 := by change (mapCircuit 12 12 (lift p) C).size ≤ 17; rw [mapSize]; exact size
      have prove (a b : ℕ) (ac : encode a b ∈ [1, 2, 3, 4, 6, 8, 14, 17, 19, 21, 37, 38, 39, 40, 41, 42, 43, 74, 76, 97, 98]) (ha : a < 11) (hb : b < 11)
          (two : ∀ x, ((bank x).getD a false || (bank x).getD b false) =
            ((bank (x ∘ perm p)).getD i.val false || (bank (x ∘ perm p)).getD j.val false)) : False := by
        obtain ⟨x,hx⟩ := properOr D (encode a b) ac dfan dsign dsize
        apply hx
        rw [← targetFormula x]
        change D.eval (bank x ++ [((bank x).getD ((encode a b).val / 11) false ||
          (bank x).getD ((encode a b).val % 11) false)]) = target x
        rw [(decode a b ha hb).1,(decode a b ha hb).2,two x]
        exact (evalLift p x _).trans ((guess _).trans (keepTarget p x))
      rcases choice with ⟨hp,h1,h2⟩ | ⟨hp,h1,h2⟩
      · exact prove _ _ hp h1 h2 (by intro x; rw [readsLift,readsLift])
      · exact prove _ _ hp h1 h2 (by intro x; rw [readsLift,readsLift,Bool.or_comm])
    have missing (x : Fin 10 → Bool) : (bank x).getD 11 false = false :=
      List.getD_eq_default _ _ (by rw [bankLen])
    have readCopy (x : Fin 10 → Bool) (i : Fin 12) :
        (bank x ++ [false]).getD i.val false = (bank x).getD i.val false := by
      by_cases hi : i.val < 11
      · exact List.getD_append _ _ _ _ (by simpa only [bankLen] using hi)
      · have last : i.val = 11 := by have := i.isLt; omega
        rw [last,bankLast,missing]
    have collapses (i : Fin 12) (known : i = 0 ∨ i = 2) (x : Fin 10 → Bool) :
        ((bank x).getD 10 false || (bank x).getD i.val false) = (bank x).getD i.val false := by
      rcases known with rfl | rfl
      · change (x 0 && x 2 || x 0) = x 0
        cases x 0 <;> cases x 2 <;> rfl
      · change (x 0 && x 2 || x 2) = x 2
        cases x 0 <;> cases x 2 <;> rfl
    have collapseBank (i : Fin 12)
        (equals : ∀ x, GateOp.or.eval (pins.map (fun j => (bank x).getD j.val false)) =
          (bank x).getD i.val false) : False := by
      apply dropSecond i
      intro x
      rw [readCopy, ← equals]
      exact computes x
    cases pins with
    | nil =>
      exact collapseBank 11 (fun x => (missing x).symm)
    | cons i rest =>
      cases rest with
      | nil =>
        exact collapseBank i (fun x => orSingle ((bank x).getD i.val false))
      | cons j rest =>
        cases rest with
        | cons k rest => simp at atMost
        | nil =>
          have gate (x : Fin 10 → Bool) :
              GateOp.or.eval ([i,j].map (fun p => (bank x).getD p.val false)) =
                ((bank x).getD i.val false || (bank x).getD j.val false) := orPair _ _
          by_cases h1 : i = 11
          · exact collapseBank j (by intro x; rw [gate,h1]; change ((bank x).getD 11 false || _) = _; rw [missing]; rfl)
          by_cases h2 : j = 11
          · exact collapseBank i (by intro x; rw [gate,h2]; change (_ || (bank x).getD 11 false) = _; rw [missing,Bool.or_false])
          by_cases eq : i = j
          · exact collapseBank j (by intro x; rw [gate,eq,Bool.or_self])
          by_cases contra : absorbing i j
          · rcases contra with ⟨eq,other⟩ | ⟨eq,other⟩
            · exact collapseBank j (by intro x; rw [gate,eq]; exact collapses j other x)
            · exact collapseBank i (by intro x; rw [gate,eq,Bool.or_comm]; exact collapses i other x)
          · have lt (a : Fin 12) (hne : a ≠ 11) : a.val < 11 := by
              have hlt := a.isLt
              by_contra! h
              exact hne (Fin.ext (by change a.val = 11; omega))
            apply excludePair i j (lt i h1) (lt j h2) eq contra
            intro x
            rw [← gate x]
            exact computes x
