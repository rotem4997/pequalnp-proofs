import PEqualNP.Defs

namespace PEqualNP.Outside.V_meta_9528__k2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word16 := BitVec 16

def Allowed (op : GateOp) : Prop :=
  op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not

def Known (w : List Word16) (a : Word16) : Prop :=
  a = 0 ∨ a = BitVec.allOnes 16 ∨ a ∈ w

def wordOp (op : GateOp) (as : List Word16) : Word16 :=
  match op, as with
  | .and, [] => BitVec.allOnes 16
  | .and, [a] => a
  | .and, a :: b :: _ => a &&& b
  | .or, [] => 0
  | .or, [a] => a
  | .or, a :: b :: _ => a ||| b
  | .not, [] => BitVec.allOnes 16
  | .not, a :: _ => ~~~a
  | _, _ => 0

def wordStep (ws : List Word16) (g : Gate) : Word16 :=
  wordOp g.op (g.inputs.map fun i => ws.getD i 0)

def wordRun (ws : List Word16) : List Gate → List Word16
  | [] => ws
  | g :: gs => wordRun (ws ++ [wordStep ws g]) gs

def bits (ws : List Word16) (j : ℕ) : List Bool :=
  ws.map fun w => w.getLsbD j

lemma bits_get (ws : List Word16) (i j : ℕ) :
    (bits ws j).getD i false = (ws.getD i 0).getLsbD j := by
  simp only [bits, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : ws[i]? with
  | none => simp
  | some w => simp

lemma wordOp_bits (op : GateOp) (as : List Word16) (j : ℕ) (hj : j < 16)
    (h : Allowed op) (hlen : as.length ≤ 2) :
    (wordOp op as).getLsbD j = op.eval (bits as j) := by
  have hz : (0 : Word16).getLsbD j = false := BitVec.getLsbD_zero
  rcases h with rfl | rfl | rfl <;>
    cases as with
    | nil =>
      simp only [wordOp, GateOp.eval, bits, List.map_nil, List.all_nil,
        List.any_nil, List.headD_nil, BitVec.getLsbD_allOnes, hj, decide_true, Bool.not_false, hz]
    | cons a rest =>
      cases rest with
      | nil =>
        simp only [wordOp, GateOp.eval, bits, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons,
          Bool.and_true, Bool.or_false, BitVec.getLsbD_not, hj, decide_true, Bool.true_and, id_eq]
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          simp only [wordOp, GateOp.eval, bits, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons,
            Bool.and_true, Bool.or_false, BitVec.getLsbD_and, BitVec.getLsbD_or,
            BitVec.getLsbD_not, hj, decide_true, Bool.true_and, id_eq]
        | cons c rest3 => simp at hlen

lemma wordStep_bits (ws : List Word16) (g : Gate) (j : ℕ) (hj : j < 16)
    (h : Allowed g.op) (hlen : g.inputs.length ≤ 2) :
    (wordStep ws g).getLsbD j = g.op.eval (g.inputs.map fun i => (bits ws j).getD i false) := by
  unfold wordStep
  rw [wordOp_bits g.op _ j hj h (by simpa using hlen)]
  congr 1
  simp only [bits, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simpa [bits] using (bits_get ws i j).symm

lemma wordRun_bits (ws : List Word16) (gs : List Gate) (j : ℕ) (hj : j < 16)
    (hok : ∀ g ∈ gs, Allowed g.op ∧ g.inputs.length ≤ 2) :
    bits (wordRun ws gs) j = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (bits ws j) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := hok g List.mem_cons_self
    have hrest : ∀ g' ∈ gs, Allowed g'.op ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hok g' (List.mem_cons_of_mem g hg')
    simp only [wordRun, List.foldl_cons]
    rw [ih (ws ++ [wordStep ws g]) hrest]
    congr 1
    simp only [bits, List.map_append, List.map_cons, List.map_nil]
    rw [wordStep_bits ws g j hj hg.1 hg.2]
    rfl

def Next (w : List Word16) (z : Word16) : Prop :=
  (∃ a ∈ w, z = ~~~a) ∨ (∃ a ∈ w, ∃ b ∈ w, z = a &&& b ∨ z = a ||| b)

def Reach : List Word16 → ℕ → Word16 → Prop
  | w, 0, t => t ∈ w
  | w, k + 1, t => t ∈ w ∨ ∃ z, z ∉ w ∧ z ≠ 0 ∧ z ≠ BitVec.allOnes 16 ∧ Next w z ∧ Reach (z :: w) k t

lemma reach_mono {w : List Word16} {k : ℕ} {t : Word16} (h : Reach w k t) : Reach w (k + 1) t := by
  induction k generalizing w with
  | zero => exact Or.inl h
  | succ k ih =>
    rcases h with ht | ⟨z, h1, h2, h3, h4, hr⟩
    · exact Or.inl ht
    · exact Or.inr ⟨z, h1, h2, h3, h4, ih hr⟩

lemma known_get {w ws : List Word16} (h : ∀ a ∈ ws, Known w a) (i : ℕ) : Known w (ws.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : ws[i]? with
  | none => exact Or.inl rfl
  | some a => exact h a (List.mem_of_getElem? hi)

lemma wordOp_next (w : List Word16) (op : GateOp) (as : List Word16)
    (ha : ∀ a ∈ as, Known w a) (hok : Allowed op) :
    Known w (wordOp op as) ∨ Next w (wordOp op as) := by
  have hnot : ∀ a, Known w a → Known w (~~~a) ∨ Next w (~~~a) := by
    intro a ha'
    rcases ha' with rfl | rfl | hm
    · exact Or.inl (Or.inr (Or.inl (by decide)))
    · exact Or.inl (Or.inl (by decide))
    · exact Or.inr (Or.inl ⟨a, hm, rfl⟩)
  have hand : ∀ a b, Known w a → Known w b → Known w (a &&& b) ∨ Next w (a &&& b) := by
    intro a b ha' hb'
    rcases ha' with rfl | rfl | hma
    · exact Or.inl (Or.inl BitVec.zero_and)
    · rw [BitVec.allOnes_and]; exact Or.inl hb'
    · rcases hb' with rfl | rfl | hmb
      · exact Or.inl (Or.inl BitVec.and_zero)
      · rw [BitVec.and_allOnes]; exact Or.inl (Or.inr (Or.inr hma))
      · exact Or.inr (Or.inr ⟨a, hma, b, hmb, Or.inl rfl⟩)
  have hor : ∀ a b, Known w a → Known w b → Known w (a ||| b) ∨ Next w (a ||| b) := by
    intro a b ha' hb'
    rcases ha' with rfl | rfl | hma
    · rw [show (0 : Word16) ||| b = b from BitVec.zero_or]; exact Or.inl hb'
    · exact Or.inl (Or.inr (Or.inl (BitVec.allOnes_or)))
    · rcases hb' with rfl | rfl | hmb
      · rw [show a ||| (0 : Word16) = a from BitVec.or_zero]; exact Or.inl (Or.inr (Or.inr hma))
      · exact Or.inl (Or.inr (Or.inl (BitVec.or_allOnes)))
      · exact Or.inr (Or.inr ⟨a, hma, b, hmb, Or.inr rfl⟩)
  rcases hok with rfl | rfl | rfl <;> cases as with
  | nil =>
    first | exact Or.inl (Or.inr (Or.inl rfl)) | exact Or.inl (Or.inl rfl)
  | cons a rest =>
    cases rest with
    | nil =>
      first
      | exact Or.inl (ha a List.mem_cons_self)
      | exact hnot a (ha a List.mem_cons_self)
    | cons b rest2 =>
      first
      | exact hand a b (ha a List.mem_cons_self) (ha b (List.mem_cons_of_mem _ List.mem_cons_self))
      | exact hor a b (ha a List.mem_cons_self) (ha b (List.mem_cons_of_mem _ List.mem_cons_self))
      | exact hnot a (ha a List.mem_cons_self)

lemma reachable (w ws : List Word16) (gs : List Gate) (k o : ℕ) (t : Word16)
    (hk : gs.length ≤ k) (hknown : ∀ a ∈ ws, Known w a)
    (hok : ∀ g ∈ gs, Allowed g.op) (h0 : t ≠ 0) (h1 : t ≠ BitVec.allOnes 16)
    (ht : (wordRun ws gs).getD o 0 = t) : Reach w k t := by
  induction gs generalizing ws w k with
  | nil =>
    change ws.getD o 0 = t at ht
    have h := known_get hknown o
    rw [ht] at h
    have hm := (h.resolve_left h0).resolve_left h1
    induction k with
    | zero => exact hm
    | succ k ih => exact Or.inl hm
  | cons g gs ih =>
    let z := wordStep ws g
    change (wordRun (ws ++ [z]) gs).getD o 0 = t at ht
    have hrest := fun g' (hg' : g' ∈ gs) => hok g' (List.mem_cons_of_mem g hg')
    cases k with
    | zero => simp at hk
    | succ k =>
      have hlen : gs.length ≤ k := by simpa using hk
      by_cases h : Known w z
      · apply reach_mono
        apply ih w (ws ++ [z]) k hlen _ hrest ht
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hknown a ha
        · exact h
      · have hz : Known w z ∨ Next w z :=
          wordOp_next w g.op _ (fun a ha => by
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
            exact known_get hknown i) (hok g List.mem_cons_self)
        refine Or.inr ⟨z, fun hm => h (Or.inr (Or.inr hm)), fun hz0 => h (Or.inl hz0),
          fun hz1 => h (Or.inr (Or.inl hz1)), hz.resolve_left h, ?_⟩
        apply ih (z :: w) (ws ++ [z]) k hlen _ hrest ht
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · rcases hknown a ha with h0' | h1' | hm
          · exact Or.inl h0'
          · exact Or.inr (Or.inl h1')
          · exact Or.inr (Or.inr (List.mem_cons_of_mem z hm))
        · exact Or.inr (Or.inr List.mem_cons_self)

def inputCols : List Word16 := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

def row4 (j : ℕ) (i : Fin 4) : Bool := (inputCols.getD i.val 0).getLsbD j

lemma table_reach {f : (Fin 4 → Bool) → Bool} {k : ℕ} {t : Word16}
    (hf : HasCircuitSize 4 f k) (h0 : t ≠ 0) (h1 : t ≠ BitVec.allOnes 16)
    (hb : ∀ j : Fin 16, f (row4 j.val) = t.getLsbD j.val) : Reach inputCols k t := by
  obtain ⟨C, hok, hs, hev⟩ := hf
  have hok' : ∀ g ∈ C.gates, Allowed g.op ∧ g.inputs.length ≤ 2 := hok
  refine reachable inputCols inputCols C.gates k C.output t hs ?_ (fun g hg => (hok' g hg).1) h0 h1 ?_
  · intro a ha; exact Or.inr (Or.inr ha)
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [← bits_get, wordRun_bits _ _ _ hj hok']
    have hinput : bits inputCols j = List.ofFn (row4 j) := by rfl
    rw [hinput]
    exact (hev (row4 j)).trans (hb ⟨j, hj⟩)

def cands (w : List Word16) : List Word16 :=
  (w.map (fun a => ~~~a) ++
    w.flatMap (fun a => w.flatMap (fun b => [a &&& b, a ||| b]))).filter
      (fun z => !w.contains z && z != 0 && z != BitVec.allOnes 16)

lemma mem_cands {w : List Word16} {z : Word16}
    (h1 : z ∉ w) (h2 : z ≠ 0) (h3 : z ≠ BitVec.allOnes 16) (hn : Next w z) : z ∈ cands w := by
  unfold cands
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    rcases hn with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl | rfl⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨a, ha, b, hb, Or.inl rfl⟩
    · exact Or.inr ⟨a, ha, b, hb, Or.inr rfl⟩
  · simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq]
    refine ⟨⟨?_, h2⟩, h3⟩
    by_contra hc
    have hc' : w.contains z = true := by cases h : w.contains z <;> simp_all
    exact h1 (List.contains_iff_mem.mp hc')

def noReach : List Word16 → ℕ → Word16 → Bool
  | w, 0, t => !w.contains t
  | w, k + 1, t => !w.contains t && (cands w).all fun z => noReach (z :: w) k t

lemma noReach_sound : ∀ k (w : List Word16) (t : Word16),
    noReach w k t = true → ¬ Reach w k t
  | 0, w, t, h, hr => by
    simp [noReach] at h
    exact h hr
  | k + 1, w, t, h, hr => by
    simp only [noReach, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    rcases hr with ht | ⟨z, h1, h2, h3, hn, hr'⟩
    · have hc : w.contains t = true := List.contains_iff_mem.mpr ht
      rw [hc] at h; exact Bool.noConfusion h.1
    · exact noReach_sound k (z :: w) t (h.2 z (mem_cands h1 h2 h3 hn)) hr'

def targetWord : Word16 := 0x000f

def targetFn (x : Fin 4 → Bool) : Bool :=
  (15 : ℕ).testBit (tableIndex x)

def witnessCirc : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩

lemma upper_all : ∀ a0 a1 a2 a3 : Bool,
    witnessCirc.eval (List.ofFn ![a0, a1, a2, a3]) = targetFn ![a0, a1, a2, a3] := by
  decide

lemma upper : HasCircuitSize 4 targetFn 2 := by
  refine ⟨witnessCirc, by simp [FanInTwo, witnessCirc], by decide, ?_⟩
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3] := by funext i; fin_cases i <;> rfl
  rw [hx]
  exact upper_all (x 0) (x 1) (x 2) (x 3)

lemma lower : ∀ t : ℕ, HasCircuitSize 4 targetFn t → 2 ≤ t := by
  intro t h
  by_contra! hlt
  obtain ⟨C, legal, sz, ev⟩ := h
  have hsm : HasCircuitSize 4 targetFn 1 := ⟨C, legal, by omega, ev⟩
  have hr : Reach inputCols 1 targetWord :=
    table_reach hsm (by decide) (by decide) (by decide)
  exact noReach_sound 1 inputCols targetWord (by decide) hr

end PEqualNP.Outside.V_meta_9528__k2

open PEqualNP.Outside.V_meta_9528__k2 in
theorem PEqualNP.Outside.V_meta_9528__k2 :
PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (15 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 2 ∧
  ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (15 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 2 ≤ t :=
  ⟨upper, lower⟩
