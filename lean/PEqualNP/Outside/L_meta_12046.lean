import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_12046
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 128
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
lemma flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  interval_cases d <;> decide
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^128) (hb : b < 2^128) : bin d a b < 2^128 := by
  have h1 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x &&& y) < 2^128 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ||| y) < 2^128 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ^^^ y) < 2^128 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b : Nat) (ha : a.testBit 0 = false) (hb : b.testBit 0 = false) :
    (bin d a b).testBit 0 = false := by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h : Live T k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht := ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def swZero : SWire := (false, 0)
def swFlip (a : SWire) : SWire := (!a.1, a.2)
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b : SWire) : SWire := (a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b : SWire) : SWire := swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j : Nat) (a : SWire) : Bool := a.1 != a.2.testBit j
lemma swRead_zero (j : Nat) : swRead j swZero = false := by simp [swRead, swZero]
lemma swRead_flip (j : Nat) (a : SWire) : swRead j (swFlip a) = !(swRead j a) := by
  cases a with | mk s v => cases s <;> cases h : v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j : Nat) (a b : SWire) : swRead j (swMeet a b) = (swRead j a && swRead j b) := by
  obtain ⟨s, u⟩ := a; obtain ⟨t, v⟩ := b
  cases s <;> cases t <;> cases hu : u.testBit j <;> cases hv : v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j : Nat) (a b : SWire) : swRead j (swJoin a b) = (swRead j a || swRead j b) := by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w : List SWire) (g : Gate) : SWire :=
  let arg := fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs : List Gate) (w : List SWire) : List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma swGate_priced (w : List SWire) (g : Gate) : priced w (isBin g) (swGate w g).2 := by
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | not => exact Or.inl (get_simple w _)
  | _ => exact Or.inl (Or.inl rfl)
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^128 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^128 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^128 ∧ (w.getD i swZero).2.testBit 0 = false := by
    simp only [List.getD_eq_getElem?_getD]
    cases eq : w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | not => exact hg (xs.headD w.length)
  | _ => exact hz
lemma swExec_lt (gs : List Gate) (w : List SWire)
    (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j : Nat) (w : List SWire) (i : Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w : List SWire) (g : Gate)
    (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j : Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false) := by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j : Nat) (gs : List Gate) (w : List SWire)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT : T ≠ 0) (gs : List Gate) (w : List SWire)
    (found : T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩ := ih (w ++ [swGate w g]) found
    have sub' : ∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2] := by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩ := pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e : isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma normPack_lt (f : Wire) : normPack f < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 128 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 128 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^128) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T : Nat) (cap : Nat) (S : Finset Nat) : Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (ess : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hnz : normPack (obs T) ≠ 0 := by rwa [hnormT]
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw : List Nat) (T d : Nat) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Nat),
    (∀ r : Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a : Nat) : Bool := (a &&& d == 0) || (a &&& d == d)
def availM (d : Nat) (pm : List Nat) (a : Nat) : Bool :=
  let m := a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (b &&& d)) : restrictW f (obs a) = restrictW f (obs b) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = 0) : restrictW f (obs a) = fun _ => false := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = d) : restrictW f (obs a) = fun _ => true := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (d ^^^ (b &&& d))) : restrictW f (obs a) = invW (restrictW f (obs b)) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f : Row → Row) (bank : List Wire) (pool : List Nat) : Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f : Row → Row} {d a : Nat} {bank : List Wire} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hs : poolSupply f bank pool)
    (ok : availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)) := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv := avail_inv (hs v hv)
    have hcomp : restrictW f (obs a) = invW (restrictW f (obs v)) := by
      have hx : (a &&& d) = d ^^^ (v &&& d) := by
        have := congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice := Nat × Nat × Nat
def choiceVal (c : Choice) : Nat := bin c.1 c.2.1 c.2.2
def choiceOK (d : Nat) (pm : List Nat) (c : Choice) : Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d : Nat) (pool : List Nat) : List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
lemma pay_choice {f : Row → Row} {d : Nat} {roots bank q} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha := availM_sound dom hs valid.1.2
  have hb := availM_sound dom hs valid.2
  have hprep : ∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y := by
    have hd := valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩ := hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv : restrictW f (obs (choiceVal c)) = comb2 op x y := by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {res} (ok : makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (ws : List Nat) : ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)) := by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h : isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc : Constant (restrictW f (obs a)) := by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n : Nat) (out : List Wire) (hr : Reach (roots.map obs) n out)
      (hsup : poolSupply f out (choiceVal op :: rest))
      (hle : n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat) : False := by
    have hcov : Supply out (((choiceVal op :: rest).map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo := lo q next hq hav
    have hcm := count_constM dom (choiceVal op :: rest)
    have hineq := cut.1.1
    omega
  cases hav : availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (127 ^^^ z)) ||| o) % 128, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 128
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 128 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^128) (hb : b < 2^128) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 128 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^128) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^128 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^128 := hS a (by simp)
    have hblt : b < 2^128 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^128 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^128 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^128 := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr := ih tail htail_lt
    simp only [Finset.image_insert, renameW_bin] at nr ⊢
    refine ⟨U.image (renameW f), renameW f a, renameW f b, d, hd, rfl,
      fun hz => ha (renameW_inj f onto halt (by decide) (hz.trans (renameW_zero f).symm)),
      fun hz => hb (renameW_inj f onto hblt (by decide) (hz.trans (renameW_zero f).symm)),
      fun heq => hab (renameW_inj f onto halt hblt heq), ?_, nr⟩
    intro hm
    rw [← renameW_bin] at hm
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt halt heq]; simp)
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt hblt heq]; simp)
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^128) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
lemma lower_count {roots : List Nat} {T : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (singles : Finset Nat) (ess : ∀ a ∈ singles, Essential T roots a) :
    Lower roots T (singles.card - 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have hsub : singles ⊆ S := fun a ha' => raw_required run roots a sub (ess a ha')
  have hle := (Finset.card_le_card hsub).trans (live_size run)
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0
def ALL128 : Nat := 0xffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 128, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL128 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 7) (hj : j < 7) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 7 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL128 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩ := hr.1 hms
    rw [heq]
    by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) : swapWord i j w < 2^128 := by
  have hi : i < 7 := by omega
  have h1 : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^128 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^128 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^128 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 7)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^128) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^128 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) :
    Function.Surjective (permRow swaps) := by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩ := ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) (r : Row) :
    permRow swaps.reverse (permRow swaps r) = r := by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n : Nat} {ws : List Nat} (hi : Impossible T n ws.toFinset)
    (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (hT : T < 2^128) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^128) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^128 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^128 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run' := live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT' : renameW (permRow swaps.reverse) T = T := by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS' : (ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor := Nat × Nat × Nat
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x : Decor) : Nat := x.2.1 ^^^ x.2.2
def projBits (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows : List Nat) (w i : Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r := by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide : 0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0 : (if w.testBit r then (1 : Nat) else 0).testBit (i + 1) = false := by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows : List Nat) (d a b : Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg : List Nat) (x : Decor) : Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d : Nat) (hx : faithful pos neg x) (hy : faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T : Nat) (pos neg : List Nat) : Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n : Nat) : Nat := (1 <<< n) - 1
abbrev Cov := Nat × Nat × Nat
def addCov (z : Nat) (c : Cov) : Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c : Cov) (a : Nat) : takeOne (addCov a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c : Cov) (a b : Nat) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c : Cov) (a b : Nat) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws : List Decor) (a : Decor) (k : Bool) : List Decor := if k then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
def restCov (c : Cov) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws : List Decor} (a : Decor) (ha : a ∈ ws) (k : Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a) := by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb := by
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
    have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws : List Decor) (i : Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws : List Decor}
    (gp : goodPairs T pos neg) (hf : ∀ x ∈ ws, faithful pos neg x)
    (h : Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm : (fullMask pos.length).testBit i = decide (i < pos.length) := by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · have ⟨hp, hn⟩ := gp.2 i hi
    have hsep : T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0) := by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩ := live_sep h hsep
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx := hf x hx
    have hpi : pos[i]? = some (pos.getD i 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni : neg[i]? = some (neg.getD i 0) := by
      have hi' : i < neg.length := gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit : (dsep x).testBit i = true := by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12 : x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1 : x.1.testBit (pos.getD i 0) <;> cases h2 : x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc := (cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats : List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a : Nat) (l : List Nat) : (insertNat a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l : List Nat) : (sortNats l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l : List Nat) : (sortNats l).toFinset = l.toFinset := by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws : List Nat) (a b d : Nat) (ka kb : Bool) : List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap : Nat} {ws : List Nat} (nd : ws.Nodup) (out : T ∉ ws)
    (stepOK : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb : Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩ := h
    have am : a ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz : bin d a b ≠ 0 := live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
      cases c <;> simp [kept]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kf, kf, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (nd.erase _).erase _
    have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (nd.erase a).not_mem_erase
    have nk := kept_nodup kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have ndc : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have hlen : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) : (delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  have wn : ws.Nodup := nd.of_map
  have dn : (delOne ws a ka).Nodup := wn.sublist (delOne_sub ws a ka)
  have m1 (l : List Decor) (hl : l.Nodup) (x y : Decor) (c : Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true) := by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v : Nat) : v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (v : Nat) : v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l := by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v : List Nat) (nd : v.Nodup) (a b : Nat) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (y : Nat) : y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l := by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m : Nat) : List Nat :=
  (List.range 7).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    let fr := ((r &&& (127 ^^^ z)) ||| o) % 128
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 128
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 128 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (127 ^^^ z)) ||| o) < 128 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (127 ^^^ z)) < 128 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 7) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (127 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 7
    · have h7 : (127 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 128) && decide (s < 128) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL128 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL128]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 128 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^128) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^128 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^128) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^128 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps : List (Nat × Nat)) (roots1 : List Nat) (T1 : Nat) (roots2 : List Nat) (T2 : Nat) : Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok : carryOK swaps roots1 T1 roots2 T2 = true)
    (hL : Lower roots2 T2 L) : Lower roots1 T1 L := by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hT2
  have hR1' := checkRoots_sound hR1
  have heq' : renameW (permRow swaps) T1 = T2 := (permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov' : ∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)) := fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def countCheck (roots : List Nat) (T L : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    decide (essPairs.map Prod.fst).Nodup &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2) &&
    decide (L ≤ essPairs.length - 1)
lemma count_of {roots T L essPairs} (ok : countCheck roots T L essPairs = true) :
    Lower roots T L := by
  simp only [countCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨hT, hR⟩, hnd⟩, hess⟩, hle⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hl := lower_count p1 p2 p3 hR' (essPairs.map Prod.fst).toFinset (fun a ha => by
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm))
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [hcard] at hl
  exact fun p bank hr hav => hle.trans (hl p bank hr hav)
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL128))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL128]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 128 r'.val |> fun e => by simpa [this] using e⟩
def sliceCheck (z o zDrop : Nat) (raw : List Nat) (T : Nat) (freeRoots : List Nat) (qRoots : List Nat) (qGoal : Nat)
    (qL : Nat) (lEss : List (Nat × Nat × Nat)) (sliceL : Nat) : Bool :=
  let G := fixWord z o T
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    checkProper G && checkRoots freeRoots &&
    raw.all (fun a => freeIn freeRoots (fixWord z o a)) &&
    (if qGoal == 0 then
       decide (lEss.map Prod.fst).Nodup &&
       lEss.all (fun e => checkEss1 G freeRoots e.1 e.2.1 e.2.2) &&
       decide (sliceL ≤ lEss.length - 1)
     else
       liftCheck zDrop 0 freeRoots G qRoots qGoal lEss &&
       decide (sliceL ≤ qL + lEss.length))
lemma slice_of {z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL}
    (ok : sliceCheck z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL = true)
    (hPrior : qGoal ≠ 0 → Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) sliceL := by
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hz, ho⟩, hzo⟩, hGp⟩, hFR⟩, hcov⟩, htail⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  have hFR' := checkRoots_sound hFR
  refine ⟨fixRow z o, freeRoots, subcube_fixRow z o hz ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW]
  by_cases hq : qGoal = 0
  · simp only [hq, ite_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at htail
    have hl := lower_count g0 glt gb0 hFR' (lEss.map Prod.fst).toFinset (fun a ha => by
      obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact checkEss1_sound (htail.1.2 _ hm))
    have hcard : (lEss.map Prod.fst).toFinset.card = lEss.length := by
      rw [List.toFinset_card_of_nodup htail.1.1, List.length_map]
    rw [hcard] at hl
    exact fun p bank hr hav => htail.2.trans (hl p bank hr hav)
  · simp only [hq, ite_false, Bool.and_eq_true, decide_eq_true_eq] at htail
    have hl := lift_of htail.1 (hPrior hq)
    exact fun p bank hr hav => htail.2.trans (hl p bank hr hav)
def goodPairsCheck (T : Nat) (pos neg : List Nat) : Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok : goodPairsCheck T pos neg = true) : goodPairs T pos neg := by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T : Nat) (autos : List (List (Nat × Nat))) : Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok : autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T := by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg : List Nat) (base : List Decor) : Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^128)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h := ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots : List Nat) (T : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat
def evalInput (r : Row) : Fin 7 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 7 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); omega⟩
lemma evalInput_packInput (x : Fin 7 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 : Bool) (j : Fin 7),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 127 := by
  let seeds : List SWire := (varsOf 127).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 127).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^128 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi7 : i < 7 := by simpa using hi2
      have hv : (varsOf 127)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 127)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi7⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · have h := hev ⟨r, hr⟩
      simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]
    exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 127) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 7 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
    intro x
    have hx := evalInput_packInput x
    rw [← hx]
    exact (hwEvalR (packInput x)).trans (hEdgeT (packInput x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput r)).trans (hEdgeT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 127).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 127).map obs)
        (show Reach ((varsOf 127).map obs) 0 ((varsOf 127).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    refine ⟨wit, wo, hwMono, by omega, hwEval⟩
  · refine ⟨gates, o, ?_, le_rfl, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
def sliceDirectCheck (z o zDead : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    decide (zDead < 128) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 128) (hd : zDead < 128) (ho : o < 128)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 7) hz hd) ho hzo r
  unfold subcube at hsub ⊢
  rw [testBit_foldr_bits] at hsub ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsub ⊢
  refine ⟨hsub.1, ?_, hsub.2.2⟩
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun x => x.testBit i) hsub.2.1
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  cases hfa : (fixRow (z ||| zDead) o r).val.testBit i <;> cases hzb : z.testBit i <;> simp_all
lemma slice_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) qL := by
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, ho⟩, _hzo0⟩, hd⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  refine ⟨fixRow (z ||| zDead) o, qRoots, subcube_fixRow_sup z o zDead hz hd ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW (z ||| zDead) o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW, heq]
  exact hPrior
def evalInput6 (r : Row) : Fin 6 → Bool := fun i => r.val.testBit i.val
def packInput6 (x : Fin 6 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    omega⟩
lemma evalInput6_packInput6 (x : Fin 6 → Bool) : evalInput6 (packInput6 x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (j : Fin 6),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
  fin_cases i <;> simpa [evalInput6, packInput6] using hi
lemma sum_eq_packInput6 (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = (packInput6 x).val := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two, packInput6]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide
lemma testBit_rep64 (T6 : Nat) (hT6 : T6 < 2^64) (r : Row) :
    (T6 ||| (T6 <<< 64)).testBit r.val = T6.testBit (r.val % 64) := by
  have hr := r.isLt
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h64 : r.val < 64
  · have hn : ¬(64 ≤ r.val) := by omega
    rw [Nat.mod_eq_of_lt h64]
    simp [hn]
  · have hge : 64 ≤ r.val := by omega
    have hmod : r.val % 64 = r.val - 64 := by omega
    rw [hmod]
    have hhi : T6.testBit r.val = false → (T6.testBit r.val || (decide (64 ≤ r.val) && T6.testBit (r.val - 64))) = T6.testBit (r.val - 64) := by
      intro hf; simp [hf, hge]
    have hf : T6.testBit r.val = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hT6 (Nat.pow_le_pow_right (by decide : 0 < 2) hge))
    exact hhi hf
lemma sw_extract_full_6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^128 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput6 r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi6 : i < 6 := by simpa using hi2
      have hv : (varsOf 63)[i]? = some (VAR i) := by interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput6, swRead, Bool.false_bne]
      have hget : (varsOf 63)[i]'(by simpa [seeds] using hi1) = VAR i := (List.getElem?_eq_some_iff.mp hv).2
      rw [hget]
      exact var_testBit ⟨i, by omega⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · have h := hev ⟨r, hr⟩; simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]; exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma table2_of_lower (T6 : Nat) (hT6lt : T6 < 2^64)
    (hT0 : (T6 ||| (T6 <<< 64)) ≠ 0) (hTlt : (T6 ||| (T6 <<< 64)) < 2^128) (hTb0 : (T6 ||| (T6 <<< 64)).testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 63) (T6 ||| (T6 <<< 64)) L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = (T6 ||| (T6 <<< 64)).testBit r.val)
    (s : ℕ)
    (hcs : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  let T := T6 ||| (T6 <<< 64)
  obtain ⟨C, hfan, hsize, heval⟩ := hcs
  have hlegal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have ⟨hm, hl⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact ⟨hm, hl⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have hlt : C.gates.countP isBin < C.gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    have heR : ∀ r : Row, Circuit.eval ⟨C.gates, C.output⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val := by
      intro r
      have h1 := heval (evalInput6 r)
      have hsum : (∑ i : Fin 6, if evalInput6 r i then 2 ^ (i : ℕ) else 0) = r.val % 64 := by
        rw [sum_eq_packInput6]
        have h : ∀ j : Row, (packInput6 (evalInput6 j)).val = j.val % 64 := by decide +kernel
        exact h r
      dsimp only at h1
      rw [hsum] at h1
      exact h1.trans (testBit_rep64 T6 hT6lt r).symm
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full_6 T hT0 hTlt hTb0 C.gates C.output hlegal heR
    have hrun := live_to_run hlive S.toList (Finset.nodup_toList S) (by simp)
    have hsup : Supply ((varsOf 63).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 63).map obs)
        (show Reach ((varsOf 63).map obs) 0 ((varsOf 63).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    have hwEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
      intro x
      rw [← evalInput6_packInput6 x, hwEvalR (packInput6 x), testBit_rep64 T6 hT6lt (packInput6 x)]
      rw [evalInput6_packInput6 x, sum_eq_packInput6 x]
      have hlt64 : (packInput6 x).val < 64 := by
        have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
        have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
        simp only [packInput6]; omega
      rw [Nat.mod_eq_of_lt hlt64]
    have hcsz : C.size = C.gates.length := rfl
    refine ⟨⟨wit, wo⟩, hwMono, ?_, hwEval⟩
    change wit.length ≤ s
    omega
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    have ⟨hm, hl⟩ := hlegal g hg
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
inductive BT (α : Type) where
  | empty : BT α
  | leaf : α → BT α
  | node : BT α → BT α → BT α
def btGet {α : Type} (d : α) : BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α : Type} : Nat → BT α → Nat → α → BT α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, i, v =>
    if i &&& 1 == 0 then .node (btSet d .empty (i >>> 1) v) .empty
    else .node .empty (btSet d .empty (i >>> 1) v)
  | d + 1, .leaf x, i, v =>
    if i &&& 1 == 0 then .node (btSet d (.leaf x) (i >>> 1) v) .empty
    else .node .empty (btSet d (.leaf x) (i >>> 1) v)
  | d + 1, .node l r, i, v =>
    if i &&& 1 == 0 then .node (btSet d l (i >>> 1) v) r
    else .node l (btSet d r (i >>> 1) v)
def btUpdate {α : Type} (d0 : α) : Nat → BT α → Nat → (α → α) → BT α
  | 0, .leaf x, _, f => .leaf (f x)
  | 0, _, _, f => .leaf (f d0)
  | d + 1, .empty, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d .empty (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d .empty (i >>> 1) f)
  | d + 1, .leaf x, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d (.leaf x) (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d (.leaf x) (i >>> 1) f)
  | d + 1, .node l r, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d l (i >>> 1) f) r
    else .node l (btUpdate d0 d r (i >>> 1) f)
def btAll {α : Type} (P : α → Prop) : BT α → Prop
  | .empty => True
  | .leaf x => P x
  | .node l r => btAll P l ∧ btAll P r
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction t generalizing i with
  | empty => exact hd
  | leaf x => exact ht
  | node l r ihl ihr =>
    unfold btGet
    split
    · exact ihl ht.1 _
    · exact ihr ht.2 _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact hv
  | succ d ih =>
    cases t with
    | empty =>
      unfold btSet; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btSet; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btSet; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases t with
    | leaf x => exact hf x ht
    | empty => exact hf d0 hd0
    | node _ _ => exact hf d0 hd0
  | succ d ih =>
    cases t with
    | empty =>
      unfold btUpdate; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btUpdate; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btUpdate; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
def btOfList {α : Type} (depth : Nat) (l : List α) : BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α : Type} {P : α → Prop} {depth : Nat} {l : List α}
    (h : ∀ x ∈ l, P x) : btAll P (btOfList depth l) := by
  unfold btOfList
  have hgo : ∀ (xs : List α) (acc : Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2 := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h trivial
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL128 ^^^ VAR i else if o.testBit i then VAR i else ALL128
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 7) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL128.testBit r.val = true := by
    simp only [ALL128]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 128 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · have hsub : (subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)) := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and,
      fastBitMask_testBit z o 0 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 1 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 2 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 3 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 4 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 7) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 7, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 7
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 7
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 128 ≤ r := by omega
      have ha : ALL128 < 2^128 := by decide
      have hv : VAR i < 2^128 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^128; decide
      have hlt_m : fastBitMask z o i < 2^128 := by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide : 0 < 2) hle))
    have hsub : (subcube z o).testBit r = false := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
lemma slice_fast_of {z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL}
    (ok : sliceCheck z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL = true)
    (hPrior : qGoal ≠ 0 → Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) sliceL := by
  have ok2 := ok
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1 ok2.1.1.1.1.1.2 ok2.1.1.1.1.2]
  exact slice_of ok hPrior
lemma slice_fast_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  have ok2 := ok
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1.1.1 ok2.1.1.1.1.1.1.1.2 ok2.1.1.1.1.1.1.2]
  exact slice_direct ok hPrior
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem := List.contains_iff_mem.mp hhit
    have hb : ∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp := hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩ := hAutos sw hsw
    have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
        ∀ r : Row, permRow l.reverse (permRow l r) = r := by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 128
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot := rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool := BoundPool × List Nat × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else
    let consts := vals.filter (isConstM c.dom)
    some (c, miss, consts, consts.length)
def fastPoolCut (fp : FastPool) (k a b z : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let consts := fp.2.2.1
  let totC := fp.2.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && consts.contains a then 1 else 0
    let dropB := if !kb && consts.contains b then 1 else 0
    let base := c.lb + (totC - dropA - dropB)
    if k + c.paid >= base + 1 then false
    else
      let m := z &&& c.dom
      if m == 0 || m == c.dom then true
      else if k + c.paid >= base then false
      else
        let okAB := !miss.contains a && !miss.contains b
        if k + c.paid + 1 < base && okAB then true
        else
          let zIn := c.pm.contains m || c.pm.contains (c.dom ^^^ m)
          if zIn then true
          else decide (k + c.paid + 1 < base) && okAB
lemma countP_erase {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p := by
  have hp := List.perm_cons_erase hx
  have h1 := List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p : Nat → Bool) {ws : List Decor} {a b : Decor}
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0) := by
  have hne : a ≠ b := fun e => hab (congrArg Prod.fst e)
  have hmap_erase : ∀ (l : List Decor) (x : Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1 := by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne1 : y.1 ≠ x.1 := by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1 : (y == x) = false := beq_false_of_ne hyx
        have h2 : (y.1 == x.1) = false := beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1 : ((ws.erase a).map Prod.fst).Nodup := ((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1 : a.1 ∈ ws.map Prod.fst := List.mem_map_of_mem ha
    have hb1 : b.1 ∈ (ws.map Prod.fst).erase a.1 := (List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1 := countP_erase p ha1
    have c2 := countP_erase p hb1
    cases hpa : p a.1 <;> cases hpb : p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) ha)
    cases hpa : p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) hb)
    cases hpb : p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP : ValidPool raw T c) (hprep : prepPool (ws.map Prod.fst) c = some fp)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (hd : d < 4)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 (bin d a.1 b.1) ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  unfold prepPool at hprep
  dsimp only at hprep
  split at hprep
  · simp at hprep
  · simp only [Option.some.injEq] at hprep
    subst hprep
    unfold fastPoolCut at hcut
    dsimp only at hcut
    split at hcut
    · simp at hcut
    · next hmiss =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at hmiss
      have hsub := (delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail : ((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true := by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf : availM c.dom c.pm w = false := Bool.eq_false_iff.mpr hna
        have hmem_ws : w ∈ ws.map Prod.fst := hsub.subset hw
        have hm := hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            exact List.Nodup.not_mem_erase (List.Nodup.of_map Prod.fst nd) hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · exact hna' hka (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa))
        · exact hnb' hkb (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb))
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      have hlen_f : ((ws.map Prod.fst).filter (isConstM c.dom)).length = (ws.map Prod.fst).countP (isConstM c.dom) := by
        rw [List.countP_eq_length_filter]
      have hca : ((ws.map Prod.fst).filter (isConstM c.dom)).contains a.1 = isConstM c.dom a.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem ha, h⟩⟩
      have hcb : ((ws.map Prod.fst).filter (isConstM c.dom)).contains b.1 = isConstM c.dom b.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem hb, h⟩⟩
      have hma : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains a.1) = availM c.dom c.pm a.1 := by
        cases h : availM c.dom c.pm a.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem ha, h]
      have hmb : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains b.1) = availM c.dom c.pm b.1 := by
        cases h : availM c.dom c.pm b.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem hb, h]
      rw [hlen_f, hca, hcb, hma, hmb] at hcut
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut choiceOK
      simp only [choiceVal, h_all_avail, Bool.and_true, List.countP_cons, Bool.and_eq_true, decide_eq_true_eq, hd, true_and]
      rw [hcnt]
      set z := bin d a.1 b.1
      set m := z &&& c.dom
      set restC := (ws.map Prod.fst).countP (isConstM c.dom) - (if !ka && isConstM c.dom a.1 then 1 else 0) - (if !kb && isConstM c.dom b.1 then 1 else 0)
      change (k + c.paid + (!availM c.dom c.pm z).toNat < c.lb + (restC + if isConstM c.dom z then 1 else 0)) ∧
        ((!(!availM c.dom c.pm z)) || (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = true
      have hbase_le : ¬(k + c.paid ≥ c.lb + restC + 1) := by
        intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
      simp only [hbase_le, ↓reduceIte] at hcut
      by_cases hzc : (m == 0 || m == c.dom) = true
      · have hisc : isConstM c.dom z = true := hzc
        have havz : availM c.dom c.pm z = true := by
          unfold availM; dsimp only; rw [show (z &&& c.dom == 0 || z &&& c.dom == c.dom) = true from hzc]; simp
        simp only [hisc, havz, Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or, ite_true, and_true]
        omega
      · have hzc_f : (m == 0 || m == c.dom) = false := Bool.eq_false_iff.mpr hzc
        have hisc : isConstM c.dom z = false := hzc_f
        have hav_eq : availM c.dom c.pm z = (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) := by
          unfold availM; dsimp only
          have hm0 : (m == 0) = false := by cases h1 : (m == 0) <;> simp [h1] at hzc_f ⊢
          have hmd : (m == c.dom) = false := by cases h1 : (m == c.dom) <;> simp [h1] at hzc_f ⊢
          change (m == 0 || m == c.dom || c.pm.contains m || c.pm.contains (c.dom ^^^ m)) = _
          simp [hm0, hmd]
        simp only [hzc_f, Bool.false_eq_true, ↓reduceIte] at hcut
        have hlt_b : ¬(k + c.paid ≥ c.lb + restC) := by
          intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
        simp only [hlt_b, ↓reduceIte] at hcut
        rw [hav_eq, hisc]
        simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
        by_cases hfast : (k + c.paid + 1 < c.lb + restC ∧ (availM c.dom c.pm a.1 && availM c.dom c.pm b.1) = true)
        · cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) <;>
            simp only [Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false, Bool.true_or, Bool.false_or, hfast.2] <;>
            exact ⟨by omega, trivial⟩
        · have hfast_b : (decide (k + c.paid + 1 < c.lb + restC) && (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = false := by
            rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact hfast ⟨h.1, (Bool.and_eq_true _ _).mpr h.2⟩
          simp only [hfast_b, Bool.false_eq_true, ↓reduceIte] at hcut
          cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m))
          · simp only [hpm, Bool.false_eq_true, ↓reduceIte] at hcut
          · simp only [Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or]
            exact ⟨by omega, trivial⟩
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 z.1 ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  if n > cap + 1 then true else
  let z := dbin d a b
  if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
    if n > cap then go false false
    else if n == cap then go false false && go true false && go false true
    else go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^128) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    have hdl := delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, Bool.false_eq_true] at test
  dsimp only [dbin] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 _hd ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks : cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0
    intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true := by
      have hnz_b : (bin d' x.1 y.1 == 0) = false := beq_false_of_ne hnz'
      have hfr_b : (ws.any (fun v => v.1 == bin d' x.1 y.1)) = false := by
        rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
        exact hfr' ((beq_iff_eq.mp heq) ▸ List.mem_map_of_mem hv)
      by_cases hlen : 1 + (ws.length - (if k1 then 0 else 1) - (if k2 then 0 else 1)) > cap
      · unfold evalMoveBT; simp [hlen]
      · unfold testPairBT at ht
        dsimp only [dbin] at ht
        have hnot1 : ¬(ws.length > cap + 1) := by cases k1 <;> cases k2 <;> simp at hlen <;> omega
        simp only [hnot1, ↓reduceIte, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at ht
        by_cases hgt : ws.length > cap
        · simp only [hgt, ↓reduceIte] at ht
          cases k1 <;> cases k2
          · exact ht
          · simp at hlen; omega
          · simp at hlen; omega
          · simp at hlen; omega
        · simp only [hgt, ↓reduceIte] at ht
          by_cases heq : ws.length = cap
          · simp only [heq, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at ht ⊢
            cases k1 <;> cases k2
            · exact ht.1.1
            · exact ht.2
            · exact ht.1.2
            · simp at hlen; omega
          · have hneq : (ws.length == cap) = false := beq_false_of_ne heq
            simp only [hneq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at ht
            cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth : Nat) (base : List Decor) (steps : List (Nat × Nat × Nat)) : BT Decor :=
  let init := (base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a := btGet (0, 0, 0) p.2 s.2.1
    let b := btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2 := by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha := btAll_get hacc hdef s.2.1
      have hb := btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def buildPoolsBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : List PoolSpec) : BT (Option BoundPool) :=
  btOfList pdepth (pspecs.map fun (slIdx, chIdxs) =>
    match btGet none slices slIdx with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
      materialize raw cs dom lb)
lemma buildPoolsBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))} {pspecs : List PoolSpec}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsBT pdepth W raw slices pspecs) := by
  apply btAll_ofList
  intro o ho c hc
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp ho
  dsimp only at hmat
  have hsl := btAll_get (d := none) hSlices (fun _ h => by simp at h) slIdx
  cases heq : btGet none slices slIdx with
  | none => rw [heq] at hmat; exact absurd (hmat.trans hc) (by simp)
  | some sl =>
    rw [heq] at hmat
    exact materialize_sound (hsl sl heq) (hmat.trans hc)
def nodupNats : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupNats xs
lemma nodupNats_sound : ∀ {l : List Nat}, nodupNats l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupNats, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, nodupNats_sound h.2⟩
def checkNodeBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals := ws.map Prod.fst
  let fpools := ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos := ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  nodupNats vals && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^128 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    (nodupNats_sound ok.1.1)
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hfp
      cases heq : btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc := btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq : fp.1 = c := by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩ := List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W : BT Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W : BT Decor) (nodes : List NodeSpec) : BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs := nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma lower_of_forestBT {roots T cap} {topBks : BT (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot : bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def buildPoolsSubBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : BT (Option PoolSpec)) (used : List Nat) : BT (Option BoundPool) :=
  used.foldl (fun acc pIdx =>
    match btGet none pspecs pIdx with
    | none => acc
    | some (slIdx, chIdxs) =>
      match btGet none slices slIdx with
      | none => acc
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
        btSet pdepth acc pIdx (materialize raw cs dom lb)) BT.empty
lemma buildPoolsSubBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))}
    {pspecs : BT (Option PoolSpec)} {used : List Nat}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsSubBT pdepth W raw slices pspecs used) := by
  unfold buildPoolsSubBT
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := trivial
  generalize (BT.empty : BT (Option BoundPool)) = acc at hinit ⊢
  induction used generalizing acc with
  | nil => exact hinit
  | cons pIdx rest ih =>
    apply ih
    dsimp only
    cases hps : btGet none pspecs pIdx with
    | none => simp only [hps]; exact hinit
    | some spec =>
      cases hsl : btGet none slices spec.1 with
      | none => simp only [hps, hsl]; exact hinit
      | some sl =>
        simp only [hps, hsl]
        apply btAll_set hinit
        intro c hc
        exact materialize_sound (btAll_get (d := none) hSlices (fun _ h => by simp at h) spec.1 sl hsl) hc
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := by
  intro ns hns
  unfold nodeValsBT; rw [sortNats_toFinset]
  exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
lemma forall_append {α : Type} {P : α → Prop} {l1 l2 : List α}
    (h1 : ∀ x ∈ l1, P x) (h2 : ∀ x ∈ l2, P x) : ∀ x ∈ l1 ++ l2, P x := by
  intro x hx; rcases List.mem_append.mp hx with h | h; exact h1 x h; exact h2 x h
lemma buildBucketsBT_of_mem {W : BT Decor} {T k nodes}
    (hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
def checkTiersBT (W : BT Decor) (T fmask : Nat) (P : BT (Option BoundPool))
    (autos : BT (List (Nat × Nat))) : Nat → BT (List (List Nat)) → List (List NodeSpec) → Option (BT (List (List Nat)))
  | _, prev, [] => some prev
  | k, prev, t :: ts =>
    if checkNodesBT W T fmask P autos prev k t then
      checkTiersBT W T fmask P autos (k + 1) (buildBucketsBT W t) ts
    else none
def checkForestBT (W : BT Decor) (T fmask : Nat) (P : BT (Option BoundPool))
    (autos : BT (List (Nat × Nat))) (tiers : List (List NodeSpec)) (roots : List Nat) : Bool :=
  match checkTiersBT W T fmask P autos 0 BT.empty tiers with
  | none => false
  | some topBks => bucketContainsBT topBks roots
lemma checkTiersBT_sound {W : BT Decor} {raw pos neg T P autos}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hP : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) P)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autos) :
    ∀ (tiers : List (List NodeSpec)) (k : Nat) (prev res : BT (List (List Nat))),
      btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prev →
      checkTiersBT W T (fullMask pos.length) P autos k prev tiers = some res →
      btAll (fun bk => ∀ xs ∈ bk, Impossible T (k + tiers.length - 1) xs.toFinset) res
  | [], k, prev, res, hprev, h => by
    simp only [checkTiersBT, Option.some.injEq] at h
    subst h; simpa using hprev
  | t :: ts, k, prev, res, hprev, h => by
    unfold checkTiersBT at h
    split at h
    · next hchk =>
      have hnext := buildBucketsBT_sound hT gp hW hP hAutos hprev hchk
      have hres := checkTiersBT_sound hT gp hW hP hAutos ts (k + 1) (buildBucketsBT W t) res (by simpa using hnext) h
      have heq : k + 1 + ts.length - 1 = k + (t :: ts).length - 1 := by simp
      rwa [heq] at hres
    · simp at h
lemma lower_of_checkForestBT {W : BT Decor} {raw pos neg T P autos tiers} {essPairs : List (Nat × Nat × Nat)}
    (hne : tiers.length > 0)
    (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hP : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) P)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autos)
    (okRoot : forestRootCheck raw T essPairs = true)
    (okForest : checkForestBT W T (fullMask pos.length) P autos tiers raw = true) :
    Lower raw T tiers.length := by
  have hTlt : T < 2^128 := by
    simp only [forestRootCheck, Bool.and_eq_true] at okRoot
    exact (checkProper_sound okRoot.1.1).2.1
  unfold checkForestBT at okForest
  cases hres : checkTiersBT W T (fullMask pos.length) P autos 0 BT.empty tiers with
  | none => simp [hres] at okForest
  | some topBks =>
    simp only [hres] at okForest
    have htop := checkTiersBT_sound hTlt gp hW hP hAutos tiers 0 BT.empty topBks trivial hres
    have hlow := lower_of_forestBT okRoot (by simpa using htop) okForest
    have heq : tiers.length - 1 + 1 = tiers.length := by omega
    rwa [heq] at hlow
def G_0 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_0 : List Nat := varsOf 38
def pos_0 : List Nat := [6,6,34,34,36,36,6,34,36]
def neg_0 : List Nat := [4,2,32,2,32,4,32,4,2]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : BT (Option PoolSpec) := btOfList 1 []
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
def P_0_0 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 R_0 slices_0 ps_0 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound slices_0_ok) autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
def P_0_1 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 R_0 slices_0 ps_0 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0_1 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound slices_0_ok) autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
def P_0_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 R_0 slices_0 ps_0 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0_2 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound slices_0_ok) autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
def P_0_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 R_0 slices_0 ps_0 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0_3 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound slices_0_ok) autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in
def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(3,4),(0,3),(0,5),(0,2),(0,1)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0
def G_2 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def R_2 : List Nat := varsOf 19
lemma low_2_ok : carryOK [(4,5),(0,2),(0,1)] R_2 G_2 R_0 G_0 = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 4 := carry_of low_2_ok low_0
def G_3 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def R_3 : List Nat := varsOf 35
lemma low_3_ok : carryOK [(0,2),(0,1)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0
def G_4 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_4 : List Nat := varsOf 21
lemma low_4_ok : carryOK [(4,5),(0,1)] R_4 G_4 R_0 G_0 = true := by decide +kernel
lemma low_4 : Lower R_4 G_4 4 := carry_of low_4_ok low_0
def G_5 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def R_5 : List Nat := varsOf 37
lemma low_5_ok : carryOK [(0,1)] R_5 G_5 R_0 G_0 = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 4 := carry_of low_5_ok low_0
def G_6 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_6 : List Nat := varsOf 22
lemma low_6_ok : carryOK [(4,5)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0
def G_7 : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00
def R_7 : List Nat := varsOf 25
lemma low_7_ok : carryOK [(4,5),(2,3),(0,1)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0
def G_8 : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
def R_8 : List Nat := varsOf 26
lemma low_8_ok : carryOK [(4,5),(2,3)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0
def G_9 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def R_9 : List Nat := varsOf 28
lemma low_9_ok : carryOK [(4,5),(1,2),(1,3)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0
def G_10 : Nat := 0xe8e88080e8e88080e8e88080e8e88080
def R_10 : List Nat := varsOf 23
def pos_10 : List Nat := [7,7,7,19,19,19,21,21,21,22,22,22,7,7,7,19,19,19,21,21,21,22,22,22]
def neg_10 : List Nat := [6,5,3,18,17,3,20,17,5,20,18,6,17,18,20,5,6,20,3,6,18,3,5,17]
def fmask_10 : Nat := fullMask 24
def base_10 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ff1ff,0xe491b6),(0xcccccccccccccccccccccccccccccccc,0xe3fe3f,0x3d2c2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfc7fc7,0x4bcb43),(0xffff0000ffff0000ffff0000ffff0000,0xff8ff8,0x9276d8)]
def steps_10 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def W_10 : BT Decor := buildWiresBT 4 base_10 steps_10
def autosL_10 : List (List (Nat × Nat)) := [[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def autos_10 : BT (List (Nat × Nat)) := btOfList 4 autosL_10
def slicesL_10 : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,4),some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 16,4)]
def slices_10 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_10
def ps_10 : BT (Option PoolSpec) := btOfList 2 [some (0,[]),some (1,[]),some (2,[]),some (3,[])]
lemma gp_10 : goodPairs G_10 pos_10 neg_10 := goodPairs_of (by decide +kernel)
lemma base_10_ok : ∀ x ∈ base_10, faithful pos_10 neg_10 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_10_ok : btAll (fun x => faithful pos_10 neg_10 x ∧ x.1 < 2^128) W_10 := buildWiresBT_faithful base_10_ok
set_option maxRecDepth 500000 in
lemma autos_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_10 = G_10) autos_10 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_10_0_ok : sliceDirectCheck 0 4 0 R_10 G_10 R_2 G_2 = true := by decide +kernel
lemma sl_10_0 : Slice R_10 G_10 (subcubeFast 0 4) 4 := slice_fast_direct sl_10_0_ok low_2
lemma sl_10_1_ok : sliceDirectCheck 0 1 0 R_10 G_10 R_6 G_6 = true := by decide +kernel
lemma sl_10_1 : Slice R_10 G_10 (subcubeFast 0 1) 4 := slice_fast_direct sl_10_1_ok low_6
lemma sl_10_2_ok : sliceDirectCheck 0 2 0 R_10 G_10 R_4 G_4 = true := by decide +kernel
lemma sl_10_2 : Slice R_10 G_10 (subcubeFast 0 2) 4 := slice_fast_direct sl_10_2_ok low_4
lemma sl_10_3_ok : sliceDirectCheck 0 16 0 R_10 G_10 R_1 G_1 = true := by decide +kernel
lemma sl_10_3 : Slice R_10 G_10 (subcubeFast 0 16) 4 := slice_fast_direct sl_10_3_ok low_1
set_option maxRecDepth 500000 in
lemma slices_10_ok : btAll (fun o => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) slices_10 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (fun _ h => (List.not_mem_nil h).elim)))))
def bk_10_init : BT (List (List Nat)) := BT.empty
lemma bk_10_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 (0 - 1) xs.toFinset) bk_10_init := trivial
def nodes_10_0 : List NodeSpec := []
def P_10_0 : BT (Option BoundPool) := buildPoolsSubBT 2 W_10 R_10 slices_10 ps_10 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_0 : checkNodesBT W_10 G_10 fmask_10 P_10_0 autos_10 bk_10_init 0 nodes_10_0 = true := by decide +kernel
def bk_10_0 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_0
set_option maxRecDepth 500000 in
lemma bk_10_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 0 xs.toFinset) bk_10_0 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound slices_10_ok) autos_10_ok bk_10_init_ok chk_10_0
def nodes_10_1 : List NodeSpec := []
def P_10_1 : BT (Option BoundPool) := buildPoolsSubBT 2 W_10 R_10 slices_10 ps_10 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_1 : checkNodesBT W_10 G_10 fmask_10 P_10_1 autos_10 bk_10_0 1 nodes_10_1 = true := by decide +kernel
def bk_10_1 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_1
set_option maxRecDepth 500000 in
lemma bk_10_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 1 xs.toFinset) bk_10_1 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound slices_10_ok) autos_10_ok bk_10_0_ok chk_10_1
def nodes_10_2 : List NodeSpec := []
def P_10_2 : BT (Option BoundPool) := buildPoolsSubBT 2 W_10 R_10 slices_10 ps_10 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_2 : checkNodesBT W_10 G_10 fmask_10 P_10_2 autos_10 bk_10_1 2 nodes_10_2 = true := by decide +kernel
def bk_10_2 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_2
set_option maxRecDepth 500000 in
lemma bk_10_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 2 xs.toFinset) bk_10_2 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound slices_10_ok) autos_10_ok bk_10_1_ok chk_10_2
def nodes_10_3 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
def P_10_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_10 R_10 slices_10 ps_10 [0,1]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_3 : checkNodesBT W_10 G_10 fmask_10 P_10_3 autos_10 bk_10_2 3 nodes_10_3 = true := by decide +kernel
def bk_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_3
set_option maxRecDepth 500000 in
lemma bk_10_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 3 xs.toFinset) bk_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound slices_10_ok) autos_10_ok bk_10_2_ok chk_10_3
def nodes_10_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
def P_10_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_10 R_10 slices_10 ps_10 [0,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_4 : checkNodesBT W_10 G_10 fmask_10 P_10_4 autos_10 bk_10_3 4 nodes_10_4 = true := by decide +kernel
def bk_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_4
set_option maxRecDepth 500000 in
lemma bk_10_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 4 xs.toFinset) bk_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound slices_10_ok) autos_10_ok bk_10_3_ok chk_10_4
def nodes_10_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
def P_10_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_10 R_10 slices_10 ps_10 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_5 : checkNodesBT W_10 G_10 fmask_10 P_10_5 autos_10 bk_10_4 5 nodes_10_5 = true := by decide +kernel
def bk_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_5
set_option maxRecDepth 500000 in
lemma bk_10_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 5 xs.toFinset) bk_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound slices_10_ok) autos_10_ok bk_10_4_ok chk_10_5
def nodes_10_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
def P_10_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_10 R_10 slices_10 ps_10 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_6 : checkNodesBT W_10 G_10 fmask_10 P_10_6 autos_10 bk_10_5 6 nodes_10_6 = true := by decide +kernel
def bk_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_6
set_option maxRecDepth 500000 in
lemma bk_10_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 6 xs.toFinset) bk_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound slices_10_ok) autos_10_ok bk_10_5_ok chk_10_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck R_10 G_10 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,19,3)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT bk_10_6 R_10 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_10 : Lower R_10 G_10 7 := lower_of_forestBT root_10_ok bk_10_6_ok root_10_in
def G_11 : Nat := 0xfcfc0000c0c00000fcfc0000c0c00000
def R_11 : List Nat := varsOf 54
lemma low_11_ok : liftCheck 0 16 R_11 G_11 R_0 G_0 [(VAR 4,22,6)] = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 5 := lift_of low_11_ok low_0
def G_12 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def R_12 : List Nat := varsOf 39
def pos_12 : List Nat := [3,3,5,5,6,6,33,33,34,34,36,36,3,3,5,5,6,6,33,33,34,34,36,36]
def neg_12 : List Nat := [2,1,4,1,4,2,32,1,32,2,32,4,4,32,2,32,1,32,2,4,1,4,1,2]
def fmask_12 : Nat := fullMask 24
def base_12 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_12 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_12 : BT Decor := buildWiresBT 4 base_12 steps_12
def autosL_12 : List (List (Nat × Nat)) := [[],[(2,5)],[(0,1)],[(2,5),(0,1)],[(1,2)],[(1,5),(1,2)],[(0,1),(0,2)],[(1,5),(0,1),(0,2)],[(1,5),(0,2)]]
def autos_12 : BT (List (Nat × Nat)) := btOfList 4 autosL_12
def slicesL_12 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 1 0,4),some (subcubeFast 32 0,4),some (subcubeFast 4 0,4)]
def slices_12 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_12
def ps_12 : BT (Option PoolSpec) := btOfList 2 [some (0,[]),some (1,[]),some (2,[]),some (3,[])]
lemma gp_12 : goodPairs G_12 pos_12 neg_12 := goodPairs_of (by decide +kernel)
lemma base_12_ok : ∀ x ∈ base_12, faithful pos_12 neg_12 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_12_ok : btAll (fun x => faithful pos_12 neg_12 x ∧ x.1 < 2^128) W_12 := buildWiresBT_faithful base_12_ok
set_option maxRecDepth 500000 in
lemma autos_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_12 = G_12) autos_12 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_12_0_ok : sliceDirectCheck 2 0 0 R_12 G_12 R_5 G_5 = true := by decide +kernel
lemma sl_12_0 : Slice R_12 G_12 (subcubeFast 2 0) 4 := slice_fast_direct sl_12_0_ok low_5
lemma sl_12_1_ok : sliceDirectCheck 1 0 0 R_12 G_12 R_0 G_0 = true := by decide +kernel
lemma sl_12_1 : Slice R_12 G_12 (subcubeFast 1 0) 4 := slice_fast_direct sl_12_1_ok low_0
lemma sl_12_2_ok : sliceDirectCheck 32 0 0 R_12 G_12 R_1 G_1 = true := by decide +kernel
lemma sl_12_2 : Slice R_12 G_12 (subcubeFast 32 0) 4 := slice_fast_direct sl_12_2_ok low_1
lemma sl_12_3_ok : sliceDirectCheck 4 0 0 R_12 G_12 R_3 G_3 = true := by decide +kernel
lemma sl_12_3 : Slice R_12 G_12 (subcubeFast 4 0) 4 := slice_fast_direct sl_12_3_ok low_3
set_option maxRecDepth 500000 in
lemma slices_12_ok : btAll (fun o => ∀ p, o = some p → Slice R_12 G_12 p.1 p.2) slices_12 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_12 G_12 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_12_0) (forall_cons (fun _ h => by cases h; exact sl_12_1) (forall_cons (fun _ h => by cases h; exact sl_12_2) (forall_cons (fun _ h => by cases h; exact sl_12_3) (fun _ h => (List.not_mem_nil h).elim)))))
def bk_12_init : BT (List (List Nat)) := BT.empty
lemma bk_12_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 (0 - 1) xs.toFinset) bk_12_init := trivial
def nodes_12_0 : List NodeSpec := []
def P_12_0 : BT (Option BoundPool) := buildPoolsSubBT 2 W_12 R_12 slices_12 ps_12 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_0 : checkNodesBT W_12 G_12 fmask_12 P_12_0 autos_12 bk_12_init 0 nodes_12_0 = true := by decide +kernel
def bk_12_0 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_0
set_option maxRecDepth 500000 in
lemma bk_12_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 0 xs.toFinset) bk_12_0 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound slices_12_ok) autos_12_ok bk_12_init_ok chk_12_0
def nodes_12_1 : List NodeSpec := []
def P_12_1 : BT (Option BoundPool) := buildPoolsSubBT 2 W_12 R_12 slices_12 ps_12 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_1 : checkNodesBT W_12 G_12 fmask_12 P_12_1 autos_12 bk_12_0 1 nodes_12_1 = true := by decide +kernel
def bk_12_1 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_1
set_option maxRecDepth 500000 in
lemma bk_12_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 1 xs.toFinset) bk_12_1 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound slices_12_ok) autos_12_ok bk_12_0_ok chk_12_1
def nodes_12_2 : List NodeSpec := []
def P_12_2 : BT (Option BoundPool) := buildPoolsSubBT 2 W_12 R_12 slices_12 ps_12 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_2 : checkNodesBT W_12 G_12 fmask_12 P_12_2 autos_12 bk_12_1 2 nodes_12_2 = true := by decide +kernel
def bk_12_2 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_2
set_option maxRecDepth 500000 in
lemma bk_12_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 2 xs.toFinset) bk_12_2 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound slices_12_ok) autos_12_ok bk_12_1_ok chk_12_2
def nodes_12_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
def P_12_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_12 R_12 slices_12 ps_12 [0,1]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_3 : checkNodesBT W_12 G_12 fmask_12 P_12_3 autos_12 bk_12_2 3 nodes_12_3 = true := by decide +kernel
def bk_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_3
set_option maxRecDepth 500000 in
lemma bk_12_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 3 xs.toFinset) bk_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound slices_12_ok) autos_12_ok bk_12_2_ok chk_12_3
def nodes_12_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
def P_12_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_12 R_12 slices_12 ps_12 [0,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_4 : checkNodesBT W_12 G_12 fmask_12 P_12_4 autos_12 bk_12_3 4 nodes_12_4 = true := by decide +kernel
def bk_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_4
set_option maxRecDepth 500000 in
lemma bk_12_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 4 xs.toFinset) bk_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound slices_12_ok) autos_12_ok bk_12_3_ok chk_12_4
def nodes_12_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
def P_12_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_12 R_12 slices_12 ps_12 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_5 : checkNodesBT W_12 G_12 fmask_12 P_12_5 autos_12 bk_12_4 5 nodes_12_5 = true := by decide +kernel
def bk_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_5
set_option maxRecDepth 500000 in
lemma bk_12_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 5 xs.toFinset) bk_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound slices_12_ok) autos_12_ok bk_12_4_ok chk_12_5
def nodes_12_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
def P_12_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_12 R_12 slices_12 ps_12 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_6 : checkNodesBT W_12 G_12 fmask_12 P_12_6 autos_12 bk_12_5 6 nodes_12_6 = true := by decide +kernel
def bk_12_6 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_6
set_option maxRecDepth 500000 in
lemma bk_12_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 6 xs.toFinset) bk_12_6 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound slices_12_ok) autos_12_ok bk_12_5_ok chk_12_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck R_12 G_12 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT bk_12_6 R_12 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_12 : Lower R_12 G_12 7 := lower_of_forestBT root_12_ok bk_12_6_ok root_12_in
def G_13 : Nat := 0xffc0c000ffc0c000ffc0c000ffc0c000
def R_13 : List Nat := varsOf 30
lemma low_13_ok : liftCheck 0 2 R_13 G_13 R_9 G_9 [(VAR 1,14,12)] = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 5 := lift_of low_13_ok low_9
def G_14 : Nat := 0xffc0ffc0fc00fc00ffc0ffc0fc00fc00
def R_14 : List Nat := varsOf 46
def pos_14 : List Nat := [10,10,12,12,14,38,38,38,40,40,42,44,10,10,10,12,12,12,38,40,40,40]
def neg_14 : List Nat := [8,2,8,4,6,36,34,6,32,8,34,36,6,34,36,6,34,36,8,6,34,36]
def fmask_14 : Nat := fullMask 22
def base_14 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x474f3,0x19b4d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x788fc,0x2ad8b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3bff1f,0x40205),(0xffffffff00000000ffffffff00000000,0x3c0fe0,0x336d60)]
def steps_14 : List (Nat × Nat × Nat) := [(3,0,2),(2,0,2),(1,0,1),(1,0,2),(0,0,2),(2,0,1),(0,0,1),(3,1,7),(0,1,7),(3,8,1),(3,0,1),(3,9,3),(1,8,1),(1,9,3),(3,10,6)]
def W_14 : BT Decor := buildWiresBT 5 base_14 steps_14
def autosL_14 : List (List (Nat × Nat)) := [[],[(2,5)],[(1,2)],[(1,5),(1,2)],[(1,2),(1,5)],[(1,5)]]
def autos_14 : BT (List (Nat × Nat)) := btOfList 3 autosL_14
def slicesL_14 : List (Option (Nat × Nat)) := []
def slices_14 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_14
def ps_14 : BT (Option PoolSpec) := btOfList 1 []
lemma gp_14 : goodPairs G_14 pos_14 neg_14 := goodPairs_of (by decide +kernel)
lemma base_14_ok : ∀ x ∈ base_14, faithful pos_14 neg_14 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_14_ok : btAll (fun x => faithful pos_14 neg_14 x ∧ x.1 < 2^128) W_14 := buildWiresBT_faithful base_14_ok
set_option maxRecDepth 500000 in
lemma autos_14_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_14 = G_14) autos_14 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_14_ok : btAll (fun o => ∀ p, o = some p → Slice R_14 G_14 p.1 p.2) slices_14 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_14 G_14 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def bk_14_init : BT (List (List Nat)) := BT.empty
lemma bk_14_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 (0 - 1) xs.toFinset) bk_14_init := trivial
def nodes_14_0 : List NodeSpec := []
def P_14_0 : BT (Option BoundPool) := buildPoolsSubBT 1 W_14 R_14 slices_14 ps_14 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_0 : checkNodesBT W_14 G_14 fmask_14 P_14_0 autos_14 bk_14_init 0 nodes_14_0 = true := by decide +kernel
def bk_14_0 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_0
set_option maxRecDepth 500000 in
lemma bk_14_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 0 xs.toFinset) bk_14_0 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound slices_14_ok) autos_14_ok bk_14_init_ok chk_14_0
def nodes_14_1 : List NodeSpec := []
def P_14_1 : BT (Option BoundPool) := buildPoolsSubBT 1 W_14 R_14 slices_14 ps_14 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_1 : checkNodesBT W_14 G_14 fmask_14 P_14_1 autos_14 bk_14_0 1 nodes_14_1 = true := by decide +kernel
def bk_14_1 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_1
set_option maxRecDepth 500000 in
lemma bk_14_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 1 xs.toFinset) bk_14_1 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound slices_14_ok) autos_14_ok bk_14_0_ok chk_14_1
def nodes_14_2 : List NodeSpec := [([18,2,3],[],[])]
def P_14_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_14 R_14 slices_14 ps_14 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_2 : checkNodesBT W_14 G_14 fmask_14 P_14_2 autos_14 bk_14_1 2 nodes_14_2 = true := by decide +kernel
def bk_14_2 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_2
set_option maxRecDepth 500000 in
lemma bk_14_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 2 xs.toFinset) bk_14_2 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound slices_14_ok) autos_14_ok bk_14_1_ok chk_14_2
def nodes_14_3 : List NodeSpec := [([11,0,2,3],[],[]),([0,12,2,3],[],[]),([13,0,2,3],[],[]),([9,14,2,3],[],[0]),([0,1,15,2],[],[]),([0,16,2,3],[],[]),([0,1,2,17],[],[]),([5,4,1,3],[],[]),([10,6,2,3],[],[0])]
def P_14_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_14 R_14 slices_14 ps_14 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_3 : checkNodesBT W_14 G_14 fmask_14 P_14_3 autos_14 bk_14_2 3 nodes_14_3 = true := by decide +kernel
def bk_14_3 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_3
set_option maxRecDepth 500000 in
lemma bk_14_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 3 xs.toFinset) bk_14_3 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound slices_14_ok) autos_14_ok bk_14_2_ok chk_14_3
def nodes_14_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([0,1,6,2,3],[],[0]),([0,1,2,7,3],[],[0,1]),([8,0,1,2,3],[],[0,1]),([9,0,1,2,3],[],[0]),([10,0,1,2,3],[],[0])]
def P_14_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_14 R_14 slices_14 ps_14 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_4 : checkNodesBT W_14 G_14 fmask_14 P_14_4 autos_14 bk_14_3 4 nodes_14_4 = true := by decide +kernel
def bk_14_4 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_4
set_option maxRecDepth 500000 in
lemma bk_14_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 4 xs.toFinset) bk_14_4 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound slices_14_ok) autos_14_ok bk_14_3_ok chk_14_4
def nodes_14_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
def P_14_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_14 R_14 slices_14 ps_14 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_5 : checkNodesBT W_14 G_14 fmask_14 P_14_5 autos_14 bk_14_4 5 nodes_14_5 = true := by decide +kernel
def bk_14_5 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_5
set_option maxRecDepth 500000 in
lemma bk_14_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 5 xs.toFinset) bk_14_5 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound slices_14_ok) autos_14_ok bk_14_4_ok chk_14_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_ok : forestRootCheck R_14 G_14 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_in : bucketContainsBT bk_14_5 R_14 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_14 : Lower R_14 G_14 6 := lower_of_forestBT root_14_ok bk_14_5_ok root_14_in
def G_15 : Nat := 0xfff0f000ff00f000fff0f000ff00f000
def R_15 : List Nat := varsOf 60
lemma low_15_ok : liftCheck 0 32 R_15 G_15 R_9 G_9 [(VAR 5,52,20)] = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 5 := lift_of low_15_ok low_9
def G_16 : Nat := 0xffffc0c0fcfcc0c0ffffc0c0fcfcc0c0
def R_16 : List Nat := varsOf 54
lemma low_16_ok : liftCheck 32 0 R_16 G_16 R_6 G_6 [(VAR 5,48,16)] = true := by decide +kernel
lemma low_16 : Lower R_16 G_16 5 := lift_of low_16_ok low_6
def G_17 : Nat := 0xe800e800e800e800e800e800e800e800
def R_17 : List Nat := varsOf 15
lemma low_17_ok : carryOK [(0,3),(3,4),(0,5),(0,2),(0,1)] R_17 G_17 R_11 G_11 = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 5 := carry_of low_17_ok low_11
def G_18 : Nat := 0xee008800ee008800ee008800ee008800
def R_18 : List Nat := varsOf 27
lemma low_18_ok : carryOK [(3,5),(3,4),(0,2),(0,1)] R_18 G_18 R_11 G_11 = true := by decide +kernel
lemma low_18 : Lower R_18 G_18 5 := carry_of low_18_ok low_11
def G_19 : Nat := 0xee00ee0088008800ee00ee0088008800
def R_19 : List Nat := varsOf 43
lemma low_19_ok : carryOK [(3,4),(0,2),(0,1)] R_19 G_19 R_11 G_11 = true := by decide +kernel
lemma low_19 : Lower R_19 G_19 5 := carry_of low_19_ok low_11
def G_20 : Nat := 0xeeee000088880000eeee000088880000
def R_20 : List Nat := varsOf 51
lemma low_20_ok : carryOK [(0,2),(0,1)] R_20 G_20 R_11 G_11 = true := by decide +kernel
lemma low_20 : Lower R_20 G_20 5 := carry_of low_20_ok low_11
def G_21 : Nat := 0xfa00a000fa00a000fa00a000fa00a000
def R_21 : List Nat := varsOf 29
lemma low_21_ok : carryOK [(3,5),(3,4),(0,1)] R_21 G_21 R_11 G_11 = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 5 := carry_of low_21_ok low_11
def G_22 : Nat := 0xfa00fa00a000a000fa00fa00a000a000
def R_22 : List Nat := varsOf 45
lemma low_22_ok : carryOK [(3,4),(0,1)] R_22 G_22 R_11 G_11 = true := by decide +kernel
lemma low_22 : Lower R_22 G_22 5 := carry_of low_22_ok low_11
def G_23 : Nat := 0xfafa0000a0a00000fafa0000a0a00000
def R_23 : List Nat := varsOf 53
lemma low_23_ok : carryOK [(0,1)] R_23 G_23 R_11 G_11 = true := by decide +kernel
lemma low_23 : Lower R_23 G_23 5 := carry_of low_23_ok low_11
def G_24 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
def R_24 : List Nat := varsOf 30
lemma low_24_ok : carryOK [(3,5),(3,4)] R_24 G_24 R_11 G_11 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 5 := carry_of low_24_ok low_11
def G_25 : Nat := 0xfc00fc00c000c000fc00fc00c000c000
def R_25 : List Nat := varsOf 46
lemma low_25_ok : carryOK [(3,4)] R_25 G_25 R_11 G_11 = true := by decide +kernel
lemma low_25 : Lower R_25 G_25 5 := carry_of low_25_ok low_11
def G_26 : Nat := 0xfe80fe80fe80fe80fe80fe80fe80fe80
def R_26 : List Nat := varsOf 15
lemma low_26_ok : carryOK [(0,4),(0,5),(0,2),(0,1)] R_26 G_26 R_14 G_14 = true := by decide +kernel
lemma low_26 : Lower R_26 G_26 6 := carry_of low_26_ok low_14
def G_27 : Nat := 0xfefe8080fefe8080fefe8080fefe8080
def R_27 : List Nat := varsOf 23
lemma low_27_ok : carryOK [(3,4),(0,3),(0,5),(0,2),(0,1)] R_27 G_27 R_14 G_14 = true := by decide +kernel
lemma low_27 : Lower R_27 G_27 6 := carry_of low_27_ok low_14
def G_28 : Nat := 0xff888800ff888800ff888800ff888800
def R_28 : List Nat := varsOf 27
lemma low_28_ok : carryOK [(0,2),(0,1)] R_28 G_28 R_13 G_13 = true := by decide +kernel
lemma low_28 : Lower R_28 G_28 5 := carry_of low_28_ok low_13
def G_29 : Nat := 0xff88ff88ee00ee00ff88ff88ee00ee00
def R_29 : List Nat := varsOf 43
lemma low_29_ok : carryOK [(0,2),(0,1)] R_29 G_29 R_14 G_14 = true := by decide +kernel
lemma low_29 : Lower R_29 G_29 6 := carry_of low_29_ok low_14
def G_30 : Nat := 0xffa0a000ffa0a000ffa0a000ffa0a000
def R_30 : List Nat := varsOf 29
lemma low_30_ok : carryOK [(0,1)] R_30 G_30 R_13 G_13 = true := by decide +kernel
lemma low_30 : Lower R_30 G_30 5 := carry_of low_30_ok low_13
def G_31 : Nat := 0xffa0ffa0fa00fa00ffa0ffa0fa00fa00
def R_31 : List Nat := varsOf 45
lemma low_31_ok : carryOK [(0,1)] R_31 G_31 R_14 G_14 = true := by decide +kernel
lemma low_31 : Lower R_31 G_31 6 := carry_of low_31_ok low_14
def G_32 : Nat := 0xffaaaa00ff00aa00ffaaaa00ff00aa00
def R_32 : List Nat := varsOf 57
lemma low_32_ok : carryOK [(0,1),(0,2)] R_32 G_32 R_15 G_15 = true := by decide +kernel
lemma low_32 : Lower R_32 G_32 5 := carry_of low_32_ok low_15
def G_33 : Nat := 0xffcccc00ff00cc00ffcccc00ff00cc00
def R_33 : List Nat := varsOf 58
lemma low_33_ok : carryOK [(1,2)] R_33 G_33 R_15 G_15 = true := by decide +kernel
lemma low_33 : Lower R_33 G_33 5 := carry_of low_33_ok low_15
def G_34 : Nat := 0xffff8888eeee8888ffff8888eeee8888
def R_34 : List Nat := varsOf 51
lemma low_34_ok : carryOK [(0,2),(0,1)] R_34 G_34 R_16 G_16 = true := by decide +kernel
lemma low_34 : Lower R_34 G_34 5 := carry_of low_34_ok low_16
def G_35 : Nat := 0xffffa0a0fafaa0a0ffffa0a0fafaa0a0
def R_35 : List Nat := varsOf 53
lemma low_35_ok : carryOK [(0,1)] R_35 G_35 R_16 G_16 = true := by decide +kernel
lemma low_35 : Lower R_35 G_35 5 := carry_of low_35_ok low_16
def G_36 : Nat := 0xe8008000e8008000e8008000e8008000
def R_36 : List Nat := varsOf 31
lemma low_36_ok : liftCheck 0 8 R_36 G_36 R_10 G_10 [(VAR 3,15,7)] = true := by decide +kernel
lemma low_36 : Lower R_36 G_36 8 := lift_of low_36_ok low_10
def G_37 : Nat := 0xfc000000c0000000fc000000c0000000
def R_37 : List Nat := varsOf 62
lemma low_37_ok : liftCheck 0 8 R_37 G_37 R_11 G_11 [(VAR 3,30,22)] = true := by decide +kernel
lemma low_37 : Lower R_37 G_37 6 := lift_of low_37_ok low_11
def G_38 : Nat := 0xfe808000fe808000fe808000fe808000
def R_38 : List Nat := varsOf 31
def pos_38 : List Nat := [15,15,15,15,23,23,23,23,25,25,25,26,26,26,27,27,28,28,28,29,29,30,30,15,15,15,15,23,23,23,23,25,25,25,25,25,25,25,26,26,26,26,26,26,26,28,28,28,28,28,28,28]
def neg_38 : List Nat := [14,13,11,7,22,21,19,7,24,17,9,24,18,10,19,11,24,20,12,21,13,22,14,19,21,22,24,11,13,14,24,7,11,13,14,19,21,22,7,11,13,14,19,21,22,7,11,13,14,19,21,22]
def fmask_38 : Nat := fullMask 52
def base_38 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3fff98c7ff,0x6eddb9998c6ee),(0xcccccccccccccccccccccccccccccccc,0x1fc07fe0f8ff,0xb76edaae0f0dd),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfe0007fff00ff,0xdbb76b37e00bb),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffff87ffff0f,0x1c3877c55ad07),(0xffff0000ffff0000ffff0000ffff0000,0xffffff87ffff0,0xe1c3847ab5b70)]
def steps_38 : List (Nat × Nat × Nat) := [(0,3,4),(0,0,1),(3,0,3),(0,0,3),(2,0,1),(1,0,1),(3,0,5),(2,0,5),(3,7,4),(0,1,4),(1,0,5),(3,0,1),(3,8,1),(3,8,4),(3,0,4),(0,8,4),(0,1,3),(3,9,3),(0,8,1),(0,10,3),(3,9,2),(0,6,2),(0,0,4),(1,9,2),(0,2,3),(3,11,3),(1,20,1),(1,8,14),(1,19,8),(3,20,3),(3,18,1),(3,20,1),(1,9,5),(3,17,2),(3,1,15),(3,22,4),(3,12,1),(3,24,4),(0,23,4),(2,6,5),(2,10,5),(0,1,15),(3,23,2),(3,23,0),(0,22,4),(3,6,10),(0,21,4),(3,23,4),(2,0,29),(3,26,3),(0,17,4),(0,26,3),(3,21,4),(1,9,21),(0,24,4),(3,17,4),(2,6,29),(3,41,2),(3,20,2),(3,56,4),(3,12,10),(3,20,15),(3,59,2),(3,43,2),(3,43,0),(3,44,10)]
def W_38 : BT Decor := buildWiresBT 7 base_38 steps_38
def autosL_38 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(3,4)],[(0,2),(0,1)],[(3,4),(1,2)],[(3,4),(0,1)],[(0,1),(0,2)],[(3,4),(0,2),(0,1)],[(0,2)]]
def autos_38 : BT (List (Nat × Nat)) := btOfList 4 autosL_38
def slicesL_38 : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,6),some (subcubeFast 0 16,6),some (subcubeFast 0 3,4),some (subcubeFast 0 6,4),some (subcubeFast 0 5,4),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5)]
def slices_38 : BT (Option (Nat × Nat)) := btOfList 3 slicesL_38
def ps_38 : BT (Option PoolSpec) := btOfList 6 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (0,[(0,0,1),(1,0,1),(3,6,10)]),some (0,[(2,0,5),(3,0,5)]),some (0,[(0,0,5),(1,20,1)]),some (5,[]),some (6,[]),some (1,[(0,0,3),(3,8,1)]),some (0,[(0,0,1),(1,0,1)]),some (0,[(2,0,1),(3,0,1)]),some (0,[(2,0,1),(3,9,2)]),some (0,[(1,0,5),(3,1,15)]),some (0,[(2,0,1),(1,9,2)]),some (7,[]),some (0,[(1,0,5),(0,1,15)]),some (1,[(0,0,1),(1,0,1),(3,6,10)]),some (0,[(0,0,5),(3,20,1)]),some (0,[(3,0,5)]),some (0,[(2,0,5)]),some (0,[(3,7,4)]),some (0,[(1,0,5)]),some (1,[(2,0,1),(3,0,1)]),some (0,[(3,8,1)]),some (1,[(0,0,3)]),some (0,[(0,8,4)]),some (0,[(2,0,1)]),some (0,[(0,0,5)]),some (0,[(1,0,1)]),some (1,[(2,0,1),(3,9,2)]),some (0,[(0,0,1)]),some (0,[(3,8,4)]),some (0,[(0,0,4)]),some (1,[(0,0,1),(1,0,1)]),some (1,[(2,0,1),(1,9,2)]),some (1,[(2,0,5)]),some (1,[(0,0,1)]),some (1,[(2,0,1)]),some (1,[(1,0,1)])]
lemma gp_38 : goodPairs G_38 pos_38 neg_38 := goodPairs_of (by decide +kernel)
lemma base_38_ok : ∀ x ∈ base_38, faithful pos_38 neg_38 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_38_ok : btAll (fun x => faithful pos_38 neg_38 x ∧ x.1 < 2^128) W_38 := buildWiresBT_faithful base_38_ok
set_option maxRecDepth 500000 in
lemma autos_38_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_38 = G_38) autos_38 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_38_0_ok : sliceDirectCheck 0 8 0 R_38 G_38 R_27 G_27 = true := by decide +kernel
lemma sl_38_0 : Slice R_38 G_38 (subcubeFast 0 8) 6 := slice_fast_direct sl_38_0_ok low_27
lemma sl_38_1_ok : sliceDirectCheck 0 16 0 R_38 G_38 R_26 G_26 = true := by decide +kernel
lemma sl_38_1 : Slice R_38 G_38 (subcubeFast 0 16) 6 := slice_fast_direct sl_38_1_ok low_26
lemma sl_38_2_ok : sliceDirectCheck 0 3 0 R_38 G_38 R_9 G_9 = true := by decide +kernel
lemma sl_38_2 : Slice R_38 G_38 (subcubeFast 0 3) 4 := slice_fast_direct sl_38_2_ok low_9
lemma sl_38_3_ok : sliceDirectCheck 0 6 0 R_38 G_38 R_7 G_7 = true := by decide +kernel
lemma sl_38_3 : Slice R_38 G_38 (subcubeFast 0 6) 4 := slice_fast_direct sl_38_3_ok low_7
lemma sl_38_4_ok : sliceDirectCheck 0 5 0 R_38 G_38 R_8 G_8 = true := by decide +kernel
lemma sl_38_4 : Slice R_38 G_38 (subcubeFast 0 5) 4 := slice_fast_direct sl_38_4_ok low_8
lemma sl_38_5_ok : sliceDirectCheck 0 1 0 R_38 G_38 R_13 G_13 = true := by decide +kernel
lemma sl_38_5 : Slice R_38 G_38 (subcubeFast 0 1) 5 := slice_fast_direct sl_38_5_ok low_13
lemma sl_38_6_ok : sliceDirectCheck 0 2 0 R_38 G_38 R_30 G_30 = true := by decide +kernel
lemma sl_38_6 : Slice R_38 G_38 (subcubeFast 0 2) 5 := slice_fast_direct sl_38_6_ok low_30
lemma sl_38_7_ok : sliceDirectCheck 0 4 0 R_38 G_38 R_28 G_28 = true := by decide +kernel
lemma sl_38_7 : Slice R_38 G_38 (subcubeFast 0 4) 5 := slice_fast_direct sl_38_7_ok low_28
set_option maxRecDepth 500000 in
lemma slices_38_ok : btAll (fun o => ∀ p, o = some p → Slice R_38 G_38 p.1 p.2) slices_38 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_38 G_38 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_38_0) (forall_cons (fun _ h => by cases h; exact sl_38_1) (forall_cons (fun _ h => by cases h; exact sl_38_2) (forall_cons (fun _ h => by cases h; exact sl_38_3) (forall_cons (fun _ h => by cases h; exact sl_38_4) (forall_cons (fun _ h => by cases h; exact sl_38_5) (forall_cons (fun _ h => by cases h; exact sl_38_6) (forall_cons (fun _ h => by cases h; exact sl_38_7) (fun _ h => (List.not_mem_nil h).elim)))))))))
def bk_38_init : BT (List (List Nat)) := BT.empty
lemma bk_38_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_38 (0 - 1) xs.toFinset) bk_38_init := trivial
def nodes_38_0 : List NodeSpec := []
def P_38_0 : BT (Option BoundPool) := buildPoolsSubBT 6 W_38 R_38 slices_38 ps_38 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_38_0 : checkNodesBT W_38 G_38 fmask_38 P_38_0 autos_38 bk_38_init 0 nodes_38_0 = true := by decide +kernel
def bk_38_0 : BT (List (List Nat)) := buildBucketsBT W_38 nodes_38_0
set_option maxRecDepth 500000 in
lemma bk_38_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_38 0 xs.toFinset) bk_38_0 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound slices_38_ok) autos_38_ok bk_38_init_ok chk_38_0
def nodes_38_1 : List NodeSpec := []
def P_38_1 : BT (Option BoundPool) := buildPoolsSubBT 6 W_38 R_38 slices_38 ps_38 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_38_1 : checkNodesBT W_38 G_38 fmask_38 P_38_1 autos_38 bk_38_0 1 nodes_38_1 = true := by decide +kernel
def bk_38_1 : BT (List (List Nat)) := buildBucketsBT W_38 nodes_38_1
set_option maxRecDepth 500000 in
lemma bk_38_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_38 1 xs.toFinset) bk_38_1 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound slices_38_ok) autos_38_ok bk_38_0_ok chk_38_1
def nodes_38_2 : List NodeSpec := []
def P_38_2 : BT (Option BoundPool) := buildPoolsSubBT 6 W_38 R_38 slices_38 ps_38 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_38_2 : checkNodesBT W_38 G_38 fmask_38 P_38_2 autos_38 bk_38_1 2 nodes_38_2 = true := by decide +kernel
def bk_38_2 : BT (List (List Nat)) := buildBucketsBT W_38 nodes_38_2
set_option maxRecDepth 500000 in
lemma bk_38_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_38 2 xs.toFinset) bk_38_2 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound slices_38_ok) autos_38_ok bk_38_1_ok chk_38_2
def nodes_38_3 : List NodeSpec := [([6,32,2,5],[],[]),([70,2,3,4],[],[])]
def P_38_3 : BT (Option BoundPool) := buildPoolsSubBT 6 W_38 R_38 slices_38 ps_38 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_38_3 : checkNodesBT W_38 G_38 fmask_38 P_38_3 autos_38 bk_38_2 3 nodes_38_3 = true := by decide +kernel
def bk_38_3 : BT (List (List Nat)) := buildBucketsBT W_38 nodes_38_3
set_option maxRecDepth 500000 in
lemma bk_38_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_38 3 xs.toFinset) bk_38_3 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound slices_38_ok) autos_38_ok bk_38_2_ok chk_38_3
def nodes_38_4 : List NodeSpec := [([62,0,1,3,4],[],[]),([8,46,2,5,4],[],[]),([0,1,32,2,5],[0,1],[0]),([34,18,0,1,2],[],[]),([36,63,0,3,4],[],[]),([63,0,31,3,4],[],[]),([12,34,1,2,4],[],[]),([9,41,2,3,4],[],[0]),([0,21,25,5,4],[],[]),([12,1,28,3,4],[],[]),([48,17,2,3,4],[],[]),([64,0,1,2,3],[],[]),([6,59,2,3,4],[2,3],[]),([0,14,22,2,5],[],[]),([1,65,2,3,4],[],[]),([6,8,14,2,5],[],[0]),([66,1,2,3,4],[],[]),([17,27,1,2,5],[],[]),([6,24,2,5,4],[2],[]),([44,10,2,3,4],[],[0]),([42,6,2,3,4],[],[]),([12,1,22,2,4],[],[]),([57,0,25,3,4],[],[]),([6,32,2,3,4],[],[0]),([0,51,25,3,4],[2,3],[]),([20,46,2,3,4],[2,4],[]),([50,2,5,3,4],[5],[]),([67,0,1,3,4],[],[]),([12,31,2,3,4],[],[]),([23,27,1,2,5],[1],[]),([68,0,1,3,4],[],[]),([69,1,2,3,4],[],[])]
def P_38_4 : BT (Option BoundPool) := buildPoolsSubBT 6 W_38 R_38 slices_38 ps_38 [0,1,2,3,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_38_4 : checkNodesBT W_38 G_38 fmask_38 P_38_4 autos_38 bk_38_3 4 nodes_38_4 = true := by decide +kernel
def bk_38_4 : BT (List (List Nat)) := buildBucketsBT W_38 nodes_38_4
set_option maxRecDepth 500000 in
lemma bk_38_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_38 4 xs.toFinset) bk_38_4 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound slices_38_ok) autos_38_ok bk_38_3_ok chk_38_4
def nodes_38_5 : List NodeSpec := [([30,0,1,2,5,4],[0],[]),([12,11,1,2,3,4],[6],[0]),([20,1,2,3,15,4],[2,4],[0,1]),([0,31,2,5,3,4],[2,7],[0]),([12,8,1,2,5,4],[0],[]),([8,0,14,1,2,5],[],[0,2,3]),([0,1,32,2,3,4],[0,1],[0]),([8,1,2,3,33,4],[8],[]),([8,27,0,1,2,5],[8,0],[]),([34,0,1,2,5,4],[0],[0]),([18,8,27,1,2,3],[8],[]),([35,0,1,2,3,4],[],[]),([36,8,0,2,3,4],[],[]),([34,8,0,1,2,4],[0],[0]),([36,0,1,2,3,4],[],[]),([36,20,0,2,3,4],[9],[1]),([20,0,31,2,3,4],[3],[0,2]),([0,1,2,3,37,4],[8],[]),([17,0,1,2,5,4],[10],[0]),([17,6,8,2,3,4],[9],[]),([0,38,1,2,3,4],[8],[]),([6,10,2,5,3,4],[2,11],[0,3]),([9,16,2,5,3,4],[12],[0]),([9,0,21,2,5,4],[],[0,3]),([0,14,22,2,3,4],[],[0]),([0,1,22,2,5,4],[1],[0]),([0,21,25,3,4],[2,3,13],[0]),([39,0,2,5,3,4],[14],[]),([0,1,28,5,3,4],[2,15],[0]),([12,0,1,2,3,4],[],[]),([12,1,10,2,3,4],[],[0]),([40,0,1,2,3,4],[],[]),([0,1,24,2,5,4],[1],[0]),([0,41,1,2,3,4],[16],[0]),([42,0,1,2,3,4],[],[0]),([43,0,1,2,3,4],[16],[0,2]),([44,0,1,2,3,4],[],[0]),([6,8,1,2,5,4],[],[3,0]),([34,20,0,1,2,4],[0],[0]),([45,0,1,2,3,4],[],[]),([20,0,1,2,3,4],[9,16],[2,4]),([6,8,14,2,3,4],[],[0]),([12,9,1,2,3,4],[],[0,3]),([12,8,1,2,3,4],[0],[3]),([18,6,1,2,3,4],[9],[]),([0,46,2,5,3,4],[8,17],[0,3]),([47,0,1,2,3,4],[],[]),([12,20,1,2,3,4],[0],[0,1,3]),([48,8,1,2,3,4],[0],[0]),([6,24,2,3,4],[3,2,11],[0]),([0,1,49,2,3,4],[],[0]),([50,2,3,4],[2,3,5,18],[0]),([23,27,1,2,3,4],[1],[0]),([9,0,51,2,3,4],[8,3],[2,0]),([8,1,2,5,15,4],[0],[0,1]),([52,0,1,2,3,4],[],[]),([53,6,1,2,3,4],[9],[]),([23,0,1,2,5,4],[1],[0,2]),([0,1,25,5,3,4],[9,13],[0,3]),([36,0,2,5,3,4],[19],[]),([54,0,1,2,3,4],[],[]),([55,0,1,2,3,4],[],[]),([48,23,1,2,3,4],[2],[0]),([56,0,1,2,3,4],[1],[0]),([9,57,0,2,3,4],[],[0]),([0,21,58,2,3,4],[9],[]),([6,20,1,2,3,4],[3],[]),([8,27,1,2,5],[0,1,8],[0,1,3,5]),([36,0,2,3,4],[],[]),([26,8,1,2,3,4],[3,0,2],[]),([18,8,0,1,2,5],[1,0],[]),([17,27,1,2,3,4],[],[0]),([0,1,59,2,3,4],[8,9,16],[0]),([0,60,1,2,3,4],[10],[2]),([61,0,1,2,3,4],[],[])]
def P_38_5 : BT (Option BoundPool) := buildPoolsSubBT 6 W_38 R_38 slices_38 ps_38 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_38_5 : checkNodesBT W_38 G_38 fmask_38 P_38_5 autos_38 bk_38_4 5 nodes_38_5 = true := by decide +kernel
def bk_38_5 : BT (List (List Nat)) := buildBucketsBT W_38 nodes_38_5
set_option maxRecDepth 500000 in
lemma bk_38_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_38 5 xs.toFinset) bk_38_5 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound slices_38_ok) autos_38_ok bk_38_4_ok chk_38_5
def nodes_38_6 : List NodeSpec := [([11,0,1,2,5,3,4],[8,20],[0,3]),([12,0,1,2,5,3,4],[21,1,8],[0,3]),([0,13,1,2,3,4],[2,22,4],[]),([8,0,14,1,2,3,4],[9,8],[0,6,2,3]),([0,1,2,5,3,15,4],[23,1,8],[0,3,1]),([9,16,2,3,4],[3,8,12,24],[0]),([17,0,1,2,3,4],[2,10,25,16],[2,7,0]),([17,8,0,1,2,3,4],[2,0],[2,0]),([18,8,0,1,2,3,4],[26,0,8],[3,0]),([19,8,1,2,3,4],[2,26,4,0],[0]),([20,0,1,2,3,4],[9,16,27,26],[0,1,3,2,4]),([9,0,1,2,5,3,4],[9,28,1,8],[0,3]),([20,8,0,1,2,3,4],[26,2,4],[0,1,3]),([9,0,21,2,3,4],[3,2,28],[0,3]),([0,1,22,2,3,4],[2,3,1,28],[0]),([20,0,1,2,5,3,4],[8,29],[0,1,3]),([23,8,0,1,2,3,4],[2],[0,2]),([0,1,24,2,3,4],[3,8,1,30],[0]),([0,1,25,3,4],[2,3,13,31],[0,3]),([26,0,1,2,3,4],[3,4,0,1,2],[0,3,2,6,4,8]),([6,8,1,2,3,4],[2,32,4],[0,3]),([8,0,1,2,5,4],[26,8,0],[0,1,2,4]),([18,0,1,2,3,4],[26,33,9,16],[0,1,3,2,4]),([0,1,10,2,5,3,4],[8,30,9,1],[0,2,3]),([8,27,0,1,2,3,4],[34,8,1],[3,0]),([6,10,2,3,4],[3,2,11,35],[0,3]),([8,27,1,2,3,4],[26,34,8],[0,1,3,5]),([0,1,28,3,4],[2,16,15,36],[0]),([6,0,1,2,5,3,4],[2,32,1],[0,3,2,6]),([6,0,1,29,2,3,4],[2,3,4],[0,4,2]),([12,0,1,2,3,4],[21,37,9,16],[0,1,3]),([23,0,1,2,3,4],[2,16,1,32],[0,2])]
def P_38_6 : BT (Option BoundPool) := buildPoolsSubBT 6 W_38 R_38 slices_38 ps_38 [0,1,2,3,4,8,9,10,11,12,13,15,16,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_38_6 : checkNodesBT W_38 G_38 fmask_38 P_38_6 autos_38 bk_38_5 6 nodes_38_6 = true := by decide +kernel
def bk_38_6 : BT (List (List Nat)) := buildBucketsBT W_38 nodes_38_6
set_option maxRecDepth 500000 in
lemma bk_38_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_38 6 xs.toFinset) bk_38_6 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound slices_38_ok) autos_38_ok bk_38_5_ok chk_38_6
def nodes_38_7 : List NodeSpec := [([0,1,2,5,3,4],[0,1,8,9,16],[0,2,1,4,3,7,9,6,8]),([6,0,1,2,3,4],[2,3,32,38,4],[0,3,2,6]),([7,0,1,2,3,4],[2,4,0,1],[0,3]),([8,0,1,2,3,4],[2,0,4,26],[0,1,2,4,7]),([9,0,1,2,3,4],[3,2,28,39],[0,3]),([0,1,10,2,3,4],[3,8,30,40],[0,3])]
def P_38_7 : BT (Option BoundPool) := buildPoolsSubBT 6 W_38 R_38 slices_38 ps_38 [0,1,2,3,4,8,9,16,26,28,30,32,38,39,40]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_38_7 : checkNodesBT W_38 G_38 fmask_38 P_38_7 autos_38 bk_38_6 7 nodes_38_7 = true := by decide +kernel
def bk_38_7 : BT (List (List Nat)) := buildBucketsBT W_38 nodes_38_7
set_option maxRecDepth 500000 in
lemma bk_38_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_38 7 xs.toFinset) bk_38_7 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound slices_38_ok) autos_38_ok bk_38_6_ok chk_38_7
def nodes_38_8 : List NodeSpec := [([0,1,2,3,4],[0,1],[0,2,1,4,3,7,9,6,8])]
def P_38_8 : BT (Option BoundPool) := buildPoolsSubBT 6 W_38 R_38 slices_38 ps_38 [0,1]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_38_8 : checkNodesBT W_38 G_38 fmask_38 P_38_8 autos_38 bk_38_7 8 nodes_38_8 = true := by decide +kernel
def bk_38_8 : BT (List (List Nat)) := buildBucketsBT W_38 nodes_38_8
set_option maxRecDepth 500000 in
lemma bk_38_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_38 8 xs.toFinset) bk_38_8 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound slices_38_ok) autos_38_ok bk_38_7_ok chk_38_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_38_ok : forestRootCheck R_38 G_38 [(VAR 0,15,14),(VAR 1,15,13),(VAR 2,15,11),(VAR 3,15,7),(VAR 4,23,7)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_38_in : bucketContainsBT bk_38_8 R_38 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_38 : Lower R_38 G_38 9 := lower_of_forestBT root_38_ok bk_38_8_ok root_38_in
def G_39 : Nat := 0xfe80fe80e800e800fe80fe80e800e800
def R_39 : List Nat := varsOf 47
def pos_39 : List Nat := [11,11,11,13,13,13,14,14,14,15,39,39,39,39,41,41,41,42,42,42,43,44,44,44,45,46,11,11,11,11,11,11,13,13,13,13,13,13,14,14,14,14,14,14,39,39,39,39,41,41,41,41,41,41,42,42,42,42,42,42,44,44,44,44,44,44]
def neg_39 : List Nat := [10,9,3,12,9,5,12,10,6,7,38,37,35,7,40,33,9,40,34,10,35,40,36,12,37,38,7,12,35,37,38,40,7,10,35,37,38,40,7,9,35,37,38,40,9,10,12,40,7,10,12,35,37,38,7,9,12,35,37,38,7,9,10,35,37,38]
def fmask_39 : Nat := fullMask 66
def base_39 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3ff03ffd11fe3f,0x1b6d913cd3511ba36),(0xcccccccccccccccccccccccccccccccc,0xfc0ffc0fe1e3fc7,0x2da6b2557561c3785),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3f000ffff03e03ff8,0x31d7546596fc02f68),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffff0fffffffc3ff,0x6186f8a288ab40db),(0xffffffff00000000ffffffff00000000,0x3fffff00003fffc00,0x38e388f3cf376dc00)]
def steps_39 : List (Nat × Nat × Nat) := [(0,0,1),(0,2,4),(1,5,6)]
def W_39 : BT Decor := buildWiresBT 3 base_39 steps_39
def autosL_39 : List (List (Nat × Nat)) := [[],[(1,2)],[(1,5),(1,2)],[(0,1),(0,2)],[(1,5),(0,1),(0,2)],[(1,5),(0,2)]]
def autos_39 : BT (List (Nat × Nat)) := btOfList 3 autosL_39
def slicesL_39 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,5),some (subcubeFast 32 0,5),some (subcubeFast 0 4,6),some (subcubeFast 4 0,5),some (subcubeFast 0 32,6),some (subcubeFast 0 1,6),some (subcubeFast 1 0,5),some (subcubeFast 0 2,6),some (subcubeFast 0 8,7),some (subcubeFast 2 8,4)]
def slices_39 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_39
def ps_39 : BT (Option PoolSpec) := btOfList 4 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[(0,2,4)]),some (6,[]),some (7,[]),some (2,[(0,0,1)]),some (5,[]),some (8,[]),some (9,[]),some (4,[(0,0,1)])]
lemma gp_39 : goodPairs G_39 pos_39 neg_39 := goodPairs_of (by decide +kernel)
lemma base_39_ok : ∀ x ∈ base_39, faithful pos_39 neg_39 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_39_ok : btAll (fun x => faithful pos_39 neg_39 x ∧ x.1 < 2^128) W_39 := buildWiresBT_faithful base_39_ok
set_option maxRecDepth 500000 in
lemma autos_39_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_39 = G_39) autos_39 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_39_0_ok : sliceDirectCheck 2 0 0 R_39 G_39 R_22 G_22 = true := by decide +kernel
lemma sl_39_0 : Slice R_39 G_39 (subcubeFast 2 0) 5 := slice_fast_direct sl_39_0_ok low_22
lemma sl_39_1_ok : sliceDirectCheck 32 0 0 R_39 G_39 R_17 G_17 = true := by decide +kernel
lemma sl_39_1 : Slice R_39 G_39 (subcubeFast 32 0) 5 := slice_fast_direct sl_39_1_ok low_17
lemma sl_39_2_ok : sliceDirectCheck 0 4 0 R_39 G_39 R_29 G_29 = true := by decide +kernel
lemma sl_39_2 : Slice R_39 G_39 (subcubeFast 0 4) 6 := slice_fast_direct sl_39_2_ok low_29
lemma sl_39_3_ok : sliceDirectCheck 4 0 0 R_39 G_39 R_19 G_19 = true := by decide +kernel
lemma sl_39_3 : Slice R_39 G_39 (subcubeFast 4 0) 5 := slice_fast_direct sl_39_3_ok low_19
lemma sl_39_4_ok : sliceDirectCheck 0 32 0 R_39 G_39 R_26 G_26 = true := by decide +kernel
lemma sl_39_4 : Slice R_39 G_39 (subcubeFast 0 32) 6 := slice_fast_direct sl_39_4_ok low_26
lemma sl_39_5_ok : sliceDirectCheck 0 1 0 R_39 G_39 R_14 G_14 = true := by decide +kernel
lemma sl_39_5 : Slice R_39 G_39 (subcubeFast 0 1) 6 := slice_fast_direct sl_39_5_ok low_14
lemma sl_39_6_ok : sliceDirectCheck 1 0 0 R_39 G_39 R_25 G_25 = true := by decide +kernel
lemma sl_39_6 : Slice R_39 G_39 (subcubeFast 1 0) 5 := slice_fast_direct sl_39_6_ok low_25
lemma sl_39_7_ok : sliceDirectCheck 0 2 0 R_39 G_39 R_31 G_31 = true := by decide +kernel
lemma sl_39_7 : Slice R_39 G_39 (subcubeFast 0 2) 6 := slice_fast_direct sl_39_7_ok low_31
lemma sl_39_8_ok : sliceDirectCheck 0 8 0 R_39 G_39 R_12 G_12 = true := by decide +kernel
lemma sl_39_8 : Slice R_39 G_39 (subcubeFast 0 8) 7 := slice_fast_direct sl_39_8_ok low_12
lemma sl_39_9_ok : sliceDirectCheck 2 8 0 R_39 G_39 R_5 G_5 = true := by decide +kernel
lemma sl_39_9 : Slice R_39 G_39 (subcubeFast 2 8) 4 := slice_fast_direct sl_39_9_ok low_5
set_option maxRecDepth 500000 in
lemma slices_39_ok : btAll (fun o => ∀ p, o = some p → Slice R_39 G_39 p.1 p.2) slices_39 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_39 G_39 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_39_0) (forall_cons (fun _ h => by cases h; exact sl_39_1) (forall_cons (fun _ h => by cases h; exact sl_39_2) (forall_cons (fun _ h => by cases h; exact sl_39_3) (forall_cons (fun _ h => by cases h; exact sl_39_4) (forall_cons (fun _ h => by cases h; exact sl_39_5) (forall_cons (fun _ h => by cases h; exact sl_39_6) (forall_cons (fun _ h => by cases h; exact sl_39_7) (forall_cons (fun _ h => by cases h; exact sl_39_8) (forall_cons (fun _ h => by cases h; exact sl_39_9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
def bk_39_init : BT (List (List Nat)) := BT.empty
lemma bk_39_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 (0 - 1) xs.toFinset) bk_39_init := trivial
def nodes_39_0 : List NodeSpec := []
def P_39_0 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 R_39 slices_39 ps_39 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_39_0 : checkNodesBT W_39 G_39 fmask_39 P_39_0 autos_39 bk_39_init 0 nodes_39_0 = true := by decide +kernel
def bk_39_0 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_0
set_option maxRecDepth 500000 in
lemma bk_39_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 0 xs.toFinset) bk_39_0 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound slices_39_ok) autos_39_ok bk_39_init_ok chk_39_0
def nodes_39_1 : List NodeSpec := []
def P_39_1 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 R_39 slices_39 ps_39 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_39_1 : checkNodesBT W_39 G_39 fmask_39 P_39_1 autos_39 bk_39_0 1 nodes_39_1 = true := by decide +kernel
def bk_39_1 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_1
set_option maxRecDepth 500000 in
lemma bk_39_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 1 xs.toFinset) bk_39_1 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound slices_39_ok) autos_39_ok bk_39_0_ok chk_39_1
def nodes_39_2 : List NodeSpec := []
def P_39_2 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 R_39 slices_39 ps_39 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_39_2 : checkNodesBT W_39 G_39 fmask_39 P_39_2 autos_39 bk_39_1 2 nodes_39_2 = true := by decide +kernel
def bk_39_2 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_2
set_option maxRecDepth 500000 in
lemma bk_39_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 2 xs.toFinset) bk_39_2 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound slices_39_ok) autos_39_ok bk_39_1_ok chk_39_2
def nodes_39_3 : List NodeSpec := []
def P_39_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 R_39 slices_39 ps_39 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_39_3 : checkNodesBT W_39 G_39 fmask_39 P_39_3 autos_39 bk_39_2 3 nodes_39_3 = true := by decide +kernel
def bk_39_3 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_3
set_option maxRecDepth 500000 in
lemma bk_39_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 3 xs.toFinset) bk_39_3 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound slices_39_ok) autos_39_ok bk_39_2_ok chk_39_3
def nodes_39_4 : List NodeSpec := []
def P_39_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 R_39 slices_39 ps_39 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_39_4 : checkNodesBT W_39 G_39 fmask_39 P_39_4 autos_39 bk_39_3 4 nodes_39_4 = true := by decide +kernel
def bk_39_4 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_4
set_option maxRecDepth 500000 in
lemma bk_39_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 4 xs.toFinset) bk_39_4 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound slices_39_ok) autos_39_ok bk_39_3_ok chk_39_4
def nodes_39_5 : List NodeSpec := [([0,1,2,7,3,4],[],[])]
def P_39_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 R_39 slices_39 ps_39 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_39_5 : checkNodesBT W_39 G_39 fmask_39 P_39_5 autos_39 bk_39_4 5 nodes_39_5 = true := by decide +kernel
def bk_39_5 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_5
set_option maxRecDepth 500000 in
lemma bk_39_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 5 xs.toFinset) bk_39_5 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound slices_39_ok) autos_39_ok bk_39_4_ok chk_39_5
def nodes_39_6 : List NodeSpec := [([5,0,1,6,2,3,4],[0,1,5,8,3,6,4,7],[0])]
def P_39_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 R_39 slices_39 ps_39 [0,1,3,4,5,6,7,8]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_39_6 : checkNodesBT W_39 G_39 fmask_39 P_39_6 autos_39 bk_39_5 6 nodes_39_6 = true := by decide +kernel
def bk_39_6 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_6
set_option maxRecDepth 500000 in
lemma bk_39_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 6 xs.toFinset) bk_39_6 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound slices_39_ok) autos_39_ok bk_39_5_ok chk_39_6
def nodes_39_7 : List NodeSpec := [([5,0,1,2,3,4],[11,9,8,12,3,1],[0])]
def P_39_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 R_39 slices_39 ps_39 [1,3,8,9,11,12]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_39_7 : checkNodesBT W_39 G_39 fmask_39 P_39_7 autos_39 bk_39_6 7 nodes_39_7 = true := by decide +kernel
def bk_39_7 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_7
set_option maxRecDepth 500000 in
lemma bk_39_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 7 xs.toFinset) bk_39_7 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound slices_39_ok) autos_39_ok bk_39_6_ok chk_39_7
def nodes_39_8 : List NodeSpec := [([0,1,2,3,4],[10,9,7,2,4],[0,1,2,3,4,5])]
def P_39_8 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 R_39 slices_39 ps_39 [2,4,7,9,10]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_39_8 : checkNodesBT W_39 G_39 fmask_39 P_39_8 autos_39 bk_39_7 8 nodes_39_8 = true := by decide +kernel
def bk_39_8 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_8
set_option maxRecDepth 500000 in
lemma bk_39_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 8 xs.toFinset) bk_39_8 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound slices_39_ok) autos_39_ok bk_39_7_ok chk_39_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_39_ok : forestRootCheck R_39 G_39 [(VAR 0,11,10),(VAR 1,11,9),(VAR 2,13,9),(VAR 3,11,3),(VAR 5,39,7)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_39_in : bucketContainsBT bk_39_8 R_39 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_39 : Lower R_39 G_39 9 := lower_of_forestBT root_39_ok bk_39_8_ok root_39_in
def G_40 : Nat := 0xfefe8080e8e88080fefe8080e8e88080
def R_40 : List Nat := varsOf 55
def pos_40 : List Nat := [7,7,7,19,19,19,21,21,21,22,22,22,39,39,39,49,49,49,50,50,50,51,52,52,52,53,54,7,7,7,7,7,7,7,19,19,19,19,19,21,21,21,21,21,22,22,22,22,22,49,49,49,49,49,50,50,50,50,50,52,52,52,52,52]
def neg_40 : List Nat := [6,5,3,18,17,3,20,17,5,20,18,6,38,37,35,48,33,17,48,34,18,35,48,36,20,37,38,17,18,20,35,37,38,48,20,35,37,38,48,18,35,37,38,48,17,35,37,38,48,18,20,35,37,38,17,20,35,37,38,17,18,35,37,38]
def fmask_40 : Nat := fullMask 64
def base_40 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3e0ffffa23f1ff,0x6b587318ca2361b6),(0xcccccccccccccccccccccccccccccccc,0x7c1f07ffc3c7e3f,0xb52aa5a954385c2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf801ff83ffc07fc7,0xc6b4c635a7803b43),(0xffff0000ffff0000ffff0000ffff0000,0xfffffffc07ff8ff8,0x18c718c6395686d8),(0xffffffff00000000ffffffff00000000,0xfffe000007fff000,0xe739ef7bc6edf000)]
def steps_40 : List (Nat × Nat × Nat) := [(2,0,1),(1,0,1),(0,0,1),(3,0,1),(3,7,6),(2,9,2),(1,9,2),(3,9,2),(0,9,2),(3,13,11)]
def W_40 : BT Decor := buildWiresBT 4 base_40 steps_40
def autosL_40 : List (List (Nat × Nat)) := [[],[(0,1)],[(1,2)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_40 : BT (List (Nat × Nat)) := btOfList 3 autosL_40
def slicesL_40 : List (Option (Nat × Nat)) := [some (subcubeFast 0 32,6),some (subcubeFast 32 2,4),some (subcubeFast 2 16,4),some (subcubeFast 0 2,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 4,5),some (subcubeFast 4 0,5),some (subcubeFast 0 16,7),some (subcubeFast 1 16,4),some (subcubeFast 32 0,7),some (subcubeFast 1 0,5)]
def slices_40 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_40
def ps_40 : BT (Option PoolSpec) := btOfList 4 [some (0,[(0,0,1),(1,0,1),(3,7,6)]),some (1,[]),some (2,[]),some (4,[]),some (6,[]),some (7,[]),some (8,[]),some (9,[]),some (0,[]),some (10,[]),some (8,[(1,0,1)]),some (11,[]),some (10,[(0,0,1)])]
lemma gp_40 : goodPairs G_40 pos_40 neg_40 := goodPairs_of (by decide +kernel)
lemma base_40_ok : ∀ x ∈ base_40, faithful pos_40 neg_40 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_40_ok : btAll (fun x => faithful pos_40 neg_40 x ∧ x.1 < 2^128) W_40 := buildWiresBT_faithful base_40_ok
set_option maxRecDepth 500000 in
lemma autos_40_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_40 = G_40) autos_40 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_40_0_ok : sliceDirectCheck 0 32 0 R_40 G_40 R_27 G_27 = true := by decide +kernel
lemma sl_40_0 : Slice R_40 G_40 (subcubeFast 0 32) 6 := slice_fast_direct sl_40_0_ok low_27
lemma sl_40_1_ok : sliceDirectCheck 32 2 0 R_40 G_40 R_4 G_4 = true := by decide +kernel
lemma sl_40_1 : Slice R_40 G_40 (subcubeFast 32 2) 4 := slice_fast_direct sl_40_1_ok low_4
lemma sl_40_2_ok : sliceDirectCheck 2 16 0 R_40 G_40 R_5 G_5 = true := by decide +kernel
lemma sl_40_2 : Slice R_40 G_40 (subcubeFast 2 16) 4 := slice_fast_direct sl_40_2_ok low_5
lemma sl_40_3_ok : sliceDirectCheck 0 2 0 R_40 G_40 R_35 G_35 = true := by decide +kernel
lemma sl_40_3 : Slice R_40 G_40 (subcubeFast 0 2) 5 := slice_fast_direct sl_40_3_ok low_35
lemma sl_40_4_ok : sliceDirectCheck 0 1 0 R_40 G_40 R_16 G_16 = true := by decide +kernel
lemma sl_40_4 : Slice R_40 G_40 (subcubeFast 0 1) 5 := slice_fast_direct sl_40_4_ok low_16
lemma sl_40_5_ok : sliceDirectCheck 2 0 0 R_40 G_40 R_23 G_23 = true := by decide +kernel
lemma sl_40_5 : Slice R_40 G_40 (subcubeFast 2 0) 5 := slice_fast_direct sl_40_5_ok low_23
lemma sl_40_6_ok : sliceDirectCheck 0 4 0 R_40 G_40 R_34 G_34 = true := by decide +kernel
lemma sl_40_6 : Slice R_40 G_40 (subcubeFast 0 4) 5 := slice_fast_direct sl_40_6_ok low_34
lemma sl_40_7_ok : sliceDirectCheck 4 0 0 R_40 G_40 R_20 G_20 = true := by decide +kernel
lemma sl_40_7 : Slice R_40 G_40 (subcubeFast 4 0) 5 := slice_fast_direct sl_40_7_ok low_20
lemma sl_40_8_ok : sliceDirectCheck 0 16 0 R_40 G_40 R_12 G_12 = true := by decide +kernel
lemma sl_40_8 : Slice R_40 G_40 (subcubeFast 0 16) 7 := slice_fast_direct sl_40_8_ok low_12
lemma sl_40_9_ok : sliceDirectCheck 1 16 0 R_40 G_40 R_0 G_0 = true := by decide +kernel
lemma sl_40_9 : Slice R_40 G_40 (subcubeFast 1 16) 4 := slice_fast_direct sl_40_9_ok low_0
lemma sl_40_10_ok : sliceDirectCheck 32 0 0 R_40 G_40 R_10 G_10 = true := by decide +kernel
lemma sl_40_10 : Slice R_40 G_40 (subcubeFast 32 0) 7 := slice_fast_direct sl_40_10_ok low_10
lemma sl_40_11_ok : sliceDirectCheck 1 0 0 R_40 G_40 R_11 G_11 = true := by decide +kernel
lemma sl_40_11 : Slice R_40 G_40 (subcubeFast 1 0) 5 := slice_fast_direct sl_40_11_ok low_11
set_option maxRecDepth 500000 in
lemma slices_40_ok : btAll (fun o => ∀ p, o = some p → Slice R_40 G_40 p.1 p.2) slices_40 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_40 G_40 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_40_0) (forall_cons (fun _ h => by cases h; exact sl_40_1) (forall_cons (fun _ h => by cases h; exact sl_40_2) (forall_cons (fun _ h => by cases h; exact sl_40_3) (forall_cons (fun _ h => by cases h; exact sl_40_4) (forall_cons (fun _ h => by cases h; exact sl_40_5) (forall_cons (fun _ h => by cases h; exact sl_40_6) (forall_cons (fun _ h => by cases h; exact sl_40_7) (forall_cons (fun _ h => by cases h; exact sl_40_8) (forall_cons (fun _ h => by cases h; exact sl_40_9) (forall_cons (fun _ h => by cases h; exact sl_40_10) (forall_cons (fun _ h => by cases h; exact sl_40_11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
def bk_40_init : BT (List (List Nat)) := BT.empty
lemma bk_40_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_40 (0 - 1) xs.toFinset) bk_40_init := trivial
def nodes_40_0 : List NodeSpec := []
def P_40_0 : BT (Option BoundPool) := buildPoolsSubBT 4 W_40 R_40 slices_40 ps_40 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_40_0 : checkNodesBT W_40 G_40 fmask_40 P_40_0 autos_40 bk_40_init 0 nodes_40_0 = true := by decide +kernel
def bk_40_0 : BT (List (List Nat)) := buildBucketsBT W_40 nodes_40_0
set_option maxRecDepth 500000 in
lemma bk_40_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_40 0 xs.toFinset) bk_40_0 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound slices_40_ok) autos_40_ok bk_40_init_ok chk_40_0
def nodes_40_1 : List NodeSpec := []
def P_40_1 : BT (Option BoundPool) := buildPoolsSubBT 4 W_40 R_40 slices_40 ps_40 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_40_1 : checkNodesBT W_40 G_40 fmask_40 P_40_1 autos_40 bk_40_0 1 nodes_40_1 = true := by decide +kernel
def bk_40_1 : BT (List (List Nat)) := buildBucketsBT W_40 nodes_40_1
set_option maxRecDepth 500000 in
lemma bk_40_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_40 1 xs.toFinset) bk_40_1 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound slices_40_ok) autos_40_ok bk_40_0_ok chk_40_1
def nodes_40_2 : List NodeSpec := [([14,3,4],[],[])]
def P_40_2 : BT (Option BoundPool) := buildPoolsSubBT 4 W_40 R_40 slices_40 ps_40 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_40_2 : checkNodesBT W_40 G_40 fmask_40 P_40_2 autos_40 bk_40_1 2 nodes_40_2 = true := by decide +kernel
def bk_40_2 : BT (List (List Nat)) := buildBucketsBT W_40 nodes_40_2
set_option maxRecDepth 500000 in
lemma bk_40_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_40 2 xs.toFinset) bk_40_2 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound slices_40_ok) autos_40_ok bk_40_1_ok chk_40_2
def nodes_40_3 : List NodeSpec := [([10,12,3,4],[],[0]),([13,11,3,4],[],[0])]
def P_40_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_40 R_40 slices_40 ps_40 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_40_3 : checkNodesBT W_40 G_40 fmask_40 P_40_3 autos_40 bk_40_2 3 nodes_40_3 = true := by decide +kernel
def bk_40_3 : BT (List (List Nat)) := buildBucketsBT W_40 nodes_40_3
set_option maxRecDepth 500000 in
lemma bk_40_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_40 3 xs.toFinset) bk_40_3 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound slices_40_ok) autos_40_ok bk_40_2_ok chk_40_3
def nodes_40_4 : List NodeSpec := [([10,9,2,3,4],[],[0]),([9,2,11,3,4],[],[0]),([9,12,2,3,4],[],[0]),([13,9,2,3,4],[0,1],[0])]
def P_40_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_40 R_40 slices_40 ps_40 [0,1]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_40_4 : checkNodesBT W_40 G_40 fmask_40 P_40_4 autos_40 bk_40_3 4 nodes_40_4 = true := by decide +kernel
def bk_40_4 : BT (List (List Nat)) := buildBucketsBT W_40 nodes_40_4
set_option maxRecDepth 500000 in
lemma bk_40_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_40 4 xs.toFinset) bk_40_4 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound slices_40_ok) autos_40_ok bk_40_3_ok chk_40_4
def nodes_40_5 : List NodeSpec := [([9,2,3,4],[2,1],[0])]
def P_40_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_40 R_40 slices_40 ps_40 [1,2]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_40_5 : checkNodesBT W_40 G_40 fmask_40 P_40_5 autos_40 bk_40_4 5 nodes_40_5 = true := by decide +kernel
def bk_40_5 : BT (List (List Nat)) := buildBucketsBT W_40 nodes_40_5
set_option maxRecDepth 500000 in
lemma bk_40_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_40 5 xs.toFinset) bk_40_5 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound slices_40_ok) autos_40_ok bk_40_4_ok chk_40_5
def nodes_40_6 : List NodeSpec := [([5,8,2,3,4],[2,1],[0]),([7,6,2,3,4],[2,1],[0])]
def P_40_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_40 R_40 slices_40 ps_40 [1,2]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_40_6 : checkNodesBT W_40 G_40 fmask_40 P_40_6 autos_40 bk_40_5 6 nodes_40_6 = true := by decide +kernel
def bk_40_6 : BT (List (List Nat)) := buildBucketsBT W_40 nodes_40_6
set_option maxRecDepth 500000 in
lemma bk_40_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_40 6 xs.toFinset) bk_40_6 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound slices_40_ok) autos_40_ok bk_40_5_ok chk_40_6
def nodes_40_7 : List NodeSpec := [([5,0,1,2,3,4],[7,1,4,5],[0]),([0,1,6,2,3,4],[1,10,3,5,4],[0]),([7,0,1,2,3,4],[2,12,11,8,4,5],[0])]
def P_40_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_40 R_40 slices_40 ps_40 [1,2,3,4,5,7,8,10,11,12]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_40_7 : checkNodesBT W_40 G_40 fmask_40 P_40_7 autos_40 bk_40_6 7 nodes_40_7 = true := by decide +kernel
def bk_40_7 : BT (List (List Nat)) := buildBucketsBT W_40 nodes_40_7
set_option maxRecDepth 500000 in
lemma bk_40_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_40 7 xs.toFinset) bk_40_7 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound slices_40_ok) autos_40_ok bk_40_6_ok chk_40_7
def nodes_40_8 : List NodeSpec := [([0,1,2,3,4],[6,9],[0,1,2,3,4,5])]
def P_40_8 : BT (Option BoundPool) := buildPoolsSubBT 4 W_40 R_40 slices_40 ps_40 [6,9]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_40_8 : checkNodesBT W_40 G_40 fmask_40 P_40_8 autos_40 bk_40_7 8 nodes_40_8 = true := by decide +kernel
def bk_40_8 : BT (List (List Nat)) := buildBucketsBT W_40 nodes_40_8
set_option maxRecDepth 500000 in
lemma bk_40_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_40 8 xs.toFinset) bk_40_8 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound slices_40_ok) autos_40_ok bk_40_7_ok chk_40_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_40_ok : forestRootCheck R_40 G_40 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,19,3),(VAR 5,49,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_40_in : bucketContainsBT bk_40_8 R_40 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_40 : Lower R_40 G_40 9 := lower_of_forestBT root_40_ok bk_40_8_ok root_40_in
def G_41 : Nat := 0xffc0c000fc00c000ffc0c000fc00c000
def R_41 : List Nat := varsOf 62
def pos_41 : List Nat := [14,14,14,26,26,26,28,28,28,30,46,46,46,54,54,54,54,56,56,56,58,58,60,60,14,14,14,14,14,14,14,26,26,26,26,26,26,28,28,28,28,28,28,54,54,54,56,56,56,56,56,56]
def neg_41 : List Nat := [12,10,6,24,18,10,24,20,12,22,44,42,38,52,50,38,22,48,40,24,50,42,52,44,22,24,38,42,44,50,52,22,38,42,44,50,52,22,38,42,44,50,52,24,42,44,22,38,42,44,50,52]
def fmask_41 : Nat := fullMask 52
def base_41 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x381fff31fe3f,0x5d2ebad31da36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3fe07fc1ffc7,0xae575d5c1b785),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc7fffffe1fff,0x339861aac0d6b),(0xffff0000ffff0000ffff0000ffff0000,0xfffff80ffe3f8,0xc4e38e35b62d8),(0xffffffff00000000ffffffff00000000,0xff80000fffc00,0xfb7df7cf6fc00)]
def steps_41 : List (Nat × Nat × Nat) := [(0,0,2),(0,0,1),(3,5,1),(3,6,2),(0,6,2),(3,9,3)]
def W_41 : BT Decor := buildWiresBT 4 base_41 steps_41
def autosL_41 : List (List (Nat × Nat)) := [[],[(1,2)]]
def autos_41 : BT (List (Nat × Nat)) := btOfList 1 autosL_41
def slicesL_41 : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 0 34,4),some (subcubeFast 0 16,6),some (subcubeFast 0 32,5),some (subcubeFast 32 0,5),some (subcubeFast 0 8,5),some (subcubeFast 0 2,5),some (subcubeFast 32 8,4)]
def slices_41 : BT (Option (Nat × Nat)) := btOfList 3 slicesL_41
def ps_41 : BT (Option PoolSpec) := btOfList 4 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[]),some (6,[]),some (2,[(0,0,2)]),some (7,[]),some (2,[(0,0,1)])]
lemma gp_41 : goodPairs G_41 pos_41 neg_41 := goodPairs_of (by decide +kernel)
lemma base_41_ok : ∀ x ∈ base_41, faithful pos_41 neg_41 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_41_ok : btAll (fun x => faithful pos_41 neg_41 x ∧ x.1 < 2^128) W_41 := buildWiresBT_faithful base_41_ok
set_option maxRecDepth 500000 in
lemma autos_41_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_41 = G_41) autos_41 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_41_0_ok : sliceDirectCheck 0 4 0 R_41 G_41 R_33 G_33 = true := by decide +kernel
lemma sl_41_0 : Slice R_41 G_41 (subcubeFast 0 4) 5 := slice_fast_direct sl_41_0_ok low_33
lemma sl_41_1_ok : sliceDirectCheck 0 34 0 R_41 G_41 R_9 G_9 = true := by decide +kernel
lemma sl_41_1 : Slice R_41 G_41 (subcubeFast 0 34) 4 := slice_fast_direct sl_41_1_ok low_9
lemma sl_41_2_ok : sliceDirectCheck 0 16 0 R_41 G_41 R_14 G_14 = true := by decide +kernel
lemma sl_41_2 : Slice R_41 G_41 (subcubeFast 0 16) 6 := slice_fast_direct sl_41_2_ok low_14
lemma sl_41_3_ok : sliceDirectCheck 0 32 0 R_41 G_41 R_13 G_13 = true := by decide +kernel
lemma sl_41_3 : Slice R_41 G_41 (subcubeFast 0 32) 5 := slice_fast_direct sl_41_3_ok low_13
lemma sl_41_4_ok : sliceDirectCheck 32 0 0 R_41 G_41 R_24 G_24 = true := by decide +kernel
lemma sl_41_4 : Slice R_41 G_41 (subcubeFast 32 0) 5 := slice_fast_direct sl_41_4_ok low_24
lemma sl_41_5_ok : sliceDirectCheck 0 8 0 R_41 G_41 R_16 G_16 = true := by decide +kernel
lemma sl_41_5 : Slice R_41 G_41 (subcubeFast 0 8) 5 := slice_fast_direct sl_41_5_ok low_16
lemma sl_41_6_ok : sliceDirectCheck 0 2 0 R_41 G_41 R_15 G_15 = true := by decide +kernel
lemma sl_41_6 : Slice R_41 G_41 (subcubeFast 0 2) 5 := slice_fast_direct sl_41_6_ok low_15
lemma sl_41_7_ok : sliceDirectCheck 32 8 0 R_41 G_41 R_6 G_6 = true := by decide +kernel
lemma sl_41_7 : Slice R_41 G_41 (subcubeFast 32 8) 4 := slice_fast_direct sl_41_7_ok low_6
set_option maxRecDepth 500000 in
lemma slices_41_ok : btAll (fun o => ∀ p, o = some p → Slice R_41 G_41 p.1 p.2) slices_41 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_41 G_41 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_41_0) (forall_cons (fun _ h => by cases h; exact sl_41_1) (forall_cons (fun _ h => by cases h; exact sl_41_2) (forall_cons (fun _ h => by cases h; exact sl_41_3) (forall_cons (fun _ h => by cases h; exact sl_41_4) (forall_cons (fun _ h => by cases h; exact sl_41_5) (forall_cons (fun _ h => by cases h; exact sl_41_6) (forall_cons (fun _ h => by cases h; exact sl_41_7) (fun _ h => (List.not_mem_nil h).elim)))))))))
def bk_41_init : BT (List (List Nat)) := BT.empty
lemma bk_41_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 (0 - 1) xs.toFinset) bk_41_init := trivial
def nodes_41_0 : List NodeSpec := []
def P_41_0 : BT (Option BoundPool) := buildPoolsSubBT 4 W_41 R_41 slices_41 ps_41 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_0 : checkNodesBT W_41 G_41 fmask_41 P_41_0 autos_41 bk_41_init 0 nodes_41_0 = true := by decide +kernel
def bk_41_0 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_0
set_option maxRecDepth 500000 in
lemma bk_41_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 0 xs.toFinset) bk_41_0 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok (buildPoolsSubBT_sound slices_41_ok) autos_41_ok bk_41_init_ok chk_41_0
def nodes_41_1 : List NodeSpec := []
def P_41_1 : BT (Option BoundPool) := buildPoolsSubBT 4 W_41 R_41 slices_41 ps_41 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_1 : checkNodesBT W_41 G_41 fmask_41 P_41_1 autos_41 bk_41_0 1 nodes_41_1 = true := by decide +kernel
def bk_41_1 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_1
set_option maxRecDepth 500000 in
lemma bk_41_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 1 xs.toFinset) bk_41_1 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok (buildPoolsSubBT_sound slices_41_ok) autos_41_ok bk_41_0_ok chk_41_1
def nodes_41_2 : List NodeSpec := []
def P_41_2 : BT (Option BoundPool) := buildPoolsSubBT 4 W_41 R_41 slices_41 ps_41 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_2 : checkNodesBT W_41 G_41 fmask_41 P_41_2 autos_41 bk_41_1 2 nodes_41_2 = true := by decide +kernel
def bk_41_2 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_2
set_option maxRecDepth 500000 in
lemma bk_41_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 2 xs.toFinset) bk_41_2 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok (buildPoolsSubBT_sound slices_41_ok) autos_41_ok bk_41_1_ok chk_41_2
def nodes_41_3 : List NodeSpec := []
def P_41_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_41 R_41 slices_41 ps_41 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_3 : checkNodesBT W_41 G_41 fmask_41 P_41_3 autos_41 bk_41_2 3 nodes_41_3 = true := by decide +kernel
def bk_41_3 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_3
set_option maxRecDepth 500000 in
lemma bk_41_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 3 xs.toFinset) bk_41_3 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok (buildPoolsSubBT_sound slices_41_ok) autos_41_ok bk_41_2_ok chk_41_3
def nodes_41_4 : List NodeSpec := [([10,0,1,2,4],[],[])]
def P_41_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_41 R_41 slices_41 ps_41 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_4 : checkNodesBT W_41 G_41 fmask_41 P_41_4 autos_41 bk_41_3 4 nodes_41_4 = true := by decide +kernel
def bk_41_4 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_4
set_option maxRecDepth 500000 in
lemma bk_41_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 4 xs.toFinset) bk_41_4 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok (buildPoolsSubBT_sound slices_41_ok) autos_41_ok bk_41_3_ok chk_41_4
def nodes_41_5 : List NodeSpec := [([7,0,1,2,3,4],[],[]),([6,5,1,2,3,4],[0,1],[]),([8,0,1,2,3,4],[],[]),([9,0,1,2,3,4],[2,3,4],[0])]
def P_41_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_41 R_41 slices_41 ps_41 [0,1,2,3,4]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_5 : checkNodesBT W_41 G_41 fmask_41 P_41_5 autos_41 bk_41_4 5 nodes_41_5 = true := by decide +kernel
def bk_41_5 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_5
set_option maxRecDepth 500000 in
lemma bk_41_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 5 xs.toFinset) bk_41_5 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok (buildPoolsSubBT_sound slices_41_ok) autos_41_ok bk_41_4_ok chk_41_5
def nodes_41_6 : List NodeSpec := [([5,0,1,2,3,4],[1,7,8,0],[0]),([6,0,1,2,3,4],[1,9,0,5],[0,1])]
def P_41_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_41 R_41 slices_41 ps_41 [0,1,5,7,8,9]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_6 : checkNodesBT W_41 G_41 fmask_41 P_41_6 autos_41 bk_41_5 6 nodes_41_6 = true := by decide +kernel
def bk_41_6 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_6
set_option maxRecDepth 500000 in
lemma bk_41_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 6 xs.toFinset) bk_41_6 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok (buildPoolsSubBT_sound slices_41_ok) autos_41_ok bk_41_5_ok chk_41_6
def nodes_41_7 : List NodeSpec := [([0,1,2,3,4],[2,6,0,5,4,3],[0,1])]
def P_41_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_41 R_41 slices_41 ps_41 [0,2,3,4,5,6]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_7 : checkNodesBT W_41 G_41 fmask_41 P_41_7 autos_41 bk_41_6 7 nodes_41_7 = true := by decide +kernel
def bk_41_7 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_7
set_option maxRecDepth 500000 in
lemma bk_41_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 7 xs.toFinset) bk_41_7 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok (buildPoolsSubBT_sound slices_41_ok) autos_41_ok bk_41_6_ok chk_41_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_41_ok : forestRootCheck R_41 G_41 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,26,10),(VAR 5,54,22)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_41_in : bucketContainsBT bk_41_7 R_41 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_41 : Lower R_41 G_41 8 := lower_of_forestBT root_41_ok bk_41_7_ok root_41_in
def G_42 : Nat := 0xee00000088000000ee00000088000000
def R_42 : List Nat := varsOf 59
lemma low_42_ok : carryOK [(0,2),(0,1)] R_42 G_42 R_37 G_37 = true := by decide +kernel
lemma low_42 : Lower R_42 G_42 6 := carry_of low_42_ok low_37
def G_43 : Nat := 0xfa000000a0000000fa000000a0000000
def R_43 : List Nat := varsOf 61
lemma low_43_ok : carryOK [(0,1)] R_43 G_43 R_37 G_37 = true := by decide +kernel
lemma low_43 : Lower R_43 G_43 6 := carry_of low_43_ok low_37
def G_44 : Nat := 0xff888800ee008800ff888800ee008800
def R_44 : List Nat := varsOf 59
lemma low_44_ok : carryOK [(0,2),(0,1)] R_44 G_44 R_41 G_41 = true := by decide +kernel
lemma low_44 : Lower R_44 G_44 8 := carry_of low_44_ok low_41
def G_45 : Nat := 0xffa0a000fa00a000ffa0a000fa00a000
def R_45 : List Nat := varsOf 61
lemma low_45_ok : carryOK [(0,1)] R_45 G_45 R_41 G_41 = true := by decide +kernel
lemma low_45 : Lower R_45 G_45 8 := carry_of low_45_ok low_41
def G_46 : Nat := 0xfe808000e8008000fe808000e8008000
def R_46 : List Nat := varsOf 63
def pos_46 : List Nat := [15,15,15,15,27,27,27,27,29,29,29,29,30,30,30,30,31,47,47,47,47,55,55,55,55,55,57,57,57,57,58,58,58,58,59,59,60,60,60,60,61,61,62,62,15,15,15,15,15,15,15,15,15,15,15,15,27,27,27,27,27,27,27,27,27,27,29,29,29,29,29,29,29,29,29,29,30,30,30,30,30,30,30,30,30,30,55,55,55,55,55,55,55,57,57,57,57,57,57,57,57,57,57,58,58,58,58,58,58,58,58,58,58,60,60,60,60,60,60,60,60,60,60]
def neg_46 : List Nat := [14,13,11,7,26,25,19,11,28,25,21,13,28,26,22,14,23,46,45,43,39,54,53,51,39,23,56,49,41,25,56,50,42,26,51,43,56,52,44,28,53,45,54,46,23,25,26,28,39,43,45,46,51,53,54,56,23,28,39,43,45,46,51,53,54,56,23,26,39,43,45,46,51,53,54,56,23,25,39,43,45,46,51,53,54,56,25,26,28,43,45,46,56,23,26,28,39,43,45,46,51,53,54,23,25,28,39,43,45,46,51,53,54,23,25,26,39,43,45,46,51,53,54]
def fmask_46 : Nat := fullMask 123
def base_46 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7fffc00ffffffff30c3fff0fff,0x376ddb7264df374dd37330c3bdd0eee),(0xcccccccccccccccccccccccccccccccc,0x1ff801ffff003fffffc0fc3fff0ff,0x5bb6cdb6a96d5bd6d5b5c0f83bbe0dd),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7fe00001ffffffc00fffff003ffff0f,0x6d3b6edad1b56d5b76d9fe00377dd0b),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x7ffffffe03ffffffffffffffc1fffff,0xec3b0edfe3a8ea3a8eeadb740ebbb7),(0xffff0000ffff0000ffff0000ffff0000,0x7ffffffffffffffff000fffffe1fff0,0x70fc3f0f1fc3f0fc3f0f5b6eee17770),(0xffffffff00000000ffffffff00000000,0x7ffffffffc0000000000ffffffe0000,0x7f1fc7f1e3fcff3fcff0f7dddfe0000)]
def steps_46 : List (Nat × Nat × Nat) := [(2,4,5),(0,4,5),(0,0,3),(0,3,4),(0,0,5),(0,0,4),(3,0,5),(3,0,4),(1,0,1),(3,0,3),(2,0,1),(0,3,5),(0,0,1),(2,0,7),(3,17,4),(2,0,17),(3,12,1),(3,10,1),(0,1,5),(3,13,3),(3,11,1),(2,11,1),(3,12,4),(3,10,4),(3,11,3),(0,18,4),(0,0,2),(3,1,4),(3,8,1),(2,8,1),(3,2,3),(1,8,1),(3,16,3),(0,8,1),(0,18,5),(3,8,4),(0,1,4),(3,1,5),(0,18,2),(3,18,2),(3,0,1),(3,18,4),(3,2,4),(1,0,7),(3,16,4),(3,16,2),(0,2,5),(3,2,5),(0,14,4),(0,11,3),(0,2,4),(2,0,2),(1,18,2),(0,14,2),(3,15,1),(0,2,3),(0,14,3),(3,18,3),(3,13,1),(3,18,5),(0,1,3),(0,11,5),(2,18,2),(3,15,4),(3,19,1),(0,1,49),(3,20,0),(3,29,1),(3,23,2),(2,1,17),(3,43,2),(3,64,2),(3,43,11),(3,24,2),(3,67,1),(3,30,1),(3,26,2),(3,27,2),(3,27,0),(3,26,3),(3,33,2),(1,33,15),(3,60,4),(0,60,4),(3,60,2),(3,43,0),(3,55,1),(1,55,1),(0,34,4),(1,34,2),(3,35,0),(0,37,4),(0,37,2),(3,8,2),(1,8,2),(3,39,0),(2,2,7),(1,2,7),(3,53,4),(3,53,0),(1,53,16),(2,11,24),(2,1,52),(1,48,16),(3,56,3),(0,62,4),(1,16,61),(0,61,4),(3,21,1),(3,47,2),(0,66,4),(2,66,2),(1,16,66),(3,44,4),(3,21,4),(3,31,2),(3,38,4),(0,38,2),(3,42,2),(1,16,52),(3,65,4),(3,61,4),(0,51,4),(3,33,8),(3,39,2),(3,68,5),(1,36,16),(0,56,5),(2,38,2),(3,53,14),(3,48,14),(3,48,3),(3,36,4),(3,36,14),(3,51,3),(3,44,3),(0,44,3),(2,14,61),(0,45,4),(3,62,4),(3,62,2),(1,13,24),(3,59,4),(3,59,3),(0,59,3),(3,53,18),(1,18,7),(1,53,18),(3,52,4),(2,0,52),(1,18,52),(3,48,18),(1,48,18),(0,38,4),(1,36,18),(2,18,61),(1,18,61),(3,34,2),(0,63,4),(1,39,2),(0,1,2),(3,63,4),(3,25,1),(3,22,4),(3,18,14),(3,65,2),(3,22,2),(3,31,5),(1,33,8),(3,41,1),(3,31,3),(2,2,17),(3,44,0),(1,43,13),(1,31,2),(0,58,4),(1,39,5),(2,18,52),(3,39,5),(3,45,3),(3,63,2),(3,51,4),(3,35,2),(3,39,4),(0,39,4),(3,38,2),(3,40,0),(0,59,4),(3,36,18),(3,45,4),(3,23,4),(3,34,4),(0,45,3),(0,44,4),(0,66,2),(1,15,18),(0,58,3),(3,68,0),(2,62,2),(3,64,3),(2,14,52),(3,47,3),(3,44,5),(3,66,4),(1,53,26),(3,55,2),(3,11,2),(2,1,56),(3,39,100),(3,39,37),(0,1,103),(2,1,133),(2,14,113),(1,16,133),(1,16,113),(1,0,113),(0,112,4),(3,116,2),(1,18,133),(3,20,2),(2,0,113),(1,116,2),(0,118,4),(1,53,31),(1,16,200),(3,170,2),(3,170,4),(3,53,50),(0,2,152),(3,143,4),(1,18,113),(3,18,103),(3,150,4),(1,16,116),(3,170,5),(1,16,99),(1,111,2),(3,117,3),(3,44,1),(3,48,62),(2,62,56),(3,111,2),(2,111,2),(2,170,2),(3,204,4),(3,204,3),(1,150,5),(0,170,4),(3,53,54),(3,40,14),(0,156,4),(0,162,4),(0,111,2),(0,153,4),(3,18,100),(3,170,3),(0,171,4),(3,177,4),(0,14,103),(3,16,103),(3,44,14),(0,170,5),(1,170,2),(1,48,65),(3,171,4),(3,134,3),(1,117,16),(2,14,133),(3,31,14),(1,31,52),(0,170,3),(3,173,2),(3,44,58),(0,170,2),(3,142,4),(3,39,14),(1,6,39),(3,190,2),(3,105,1),(3,126,2),(3,68,14),(1,53,27),(1,92,211),(1,34,211),(3,215,2),(2,215,2),(1,215,2),(1,16,225),(2,14,225),(2,1,113),(3,258,3),(3,248,3),(3,251,4),(1,170,7),(3,232,2),(0,231,4),(3,253,3),(3,246,3),(2,281,2),(1,6,150),(3,253,2),(1,48,170),(3,276,2),(3,232,5),(0,232,5),(1,232,2),(2,261,2),(0,261,2),(3,231,4),(3,231,3),(1,261,2),(2,232,2),(0,268,5),(1,274,2),(0,251,4),(1,53,170),(0,266,5),(1,170,56),(1,36,170),(0,62,58),(3,279,3),(3,274,5),(2,170,61),(1,170,61),(3,232,3),(0,170,61),(3,267,2),(2,170,7),(1,267,2),(0,268,4),(1,281,2),(3,261,4),(0,261,4),(3,261,2),(3,266,5),(0,268,3),(3,231,5),(0,170,56),(1,121,65),(3,151,14),(0,231,5),(3,249,4),(2,274,2),(3,276,4),(3,274,2),(1,170,17),(3,279,5),(3,279,4),(3,45,62),(0,274,2),(3,281,2),(3,267,4),(3,249,3),(0,215,2),(0,281,2),(0,274,5),(2,14,234),(3,18,242),(3,300,5),(2,268,7),(1,102,170),(3,170,103),(1,20,170),(1,177,170),(0,351,4),(0,2,351),(0,321,4),(1,110,170),(0,323,3),(3,343,5),(1,170,113),(0,329,4),(3,357,2),(0,332,4),(3,53,232),(1,53,232),(3,36,232),(1,36,232),(2,232,61),(1,232,61),(3,330,2),(3,300,3),(0,300,3),(1,253,61),(3,302,2),(0,339,4),(3,48,261),(0,307,3),(2,242,7),(0,308,4),(1,48,231),(3,341,4),(1,18,258),(1,36,231),(0,2,299),(1,300,5),(0,315,4),(0,313,4),(3,332,4),(3,314,3),(3,301,3),(3,339,4),(3,313,4),(3,308,4),(3,349,2),(1,276,231),(3,333,2),(3,358,4),(3,315,4),(3,285,14),(1,249,231),(0,358,4),(3,258,242),(1,170,137),(1,48,276),(0,353,5),(3,61,268),(1,279,261),(1,127,170),(0,341,4),(3,355,5),(3,353,3),(3,317,5),(3,306,3),(0,319,5),(1,36,253),(1,279,7),(3,326,4),(3,338,2),(0,324,4),(1,48,261),(0,306,3),(3,337,2),(0,326,4),(2,281,45),(1,45,261),(3,301,311),(3,313,316),(1,249,301),(3,231,358),(3,231,347),(1,249,313),(3,360,336),(0,416,4),(3,331,329),(0,416,3),(3,355,319)]
def W_46 : BT Decor := buildWiresBT 9 base_46 steps_46
def autosL_46 : List (List (Nat × Nat)) := [[],[(0,1),(0,2)],[(1,2)],[(0,1)],[(0,2)],[(0,2),(0,1)]]
def autos_46 : BT (List (Nat × Nat)) := btOfList 3 autosL_46
def slicesL_46 : List (Option (Nat × Nat)) := [some (subcubeFast 32 9,4),some (subcubeFast 0 38,4),some (subcubeFast 0 17,6),some (subcubeFast 0 5,5),some (subcubeFast 0 16,9),some (subcubeFast 0 20,6),some (subcubeFast 1 24,4),some (subcubeFast 0 36,5),some (subcubeFast 0 10,5),some (subcubeFast 0 3,5),some (subcubeFast 0 1,8),some (subcubeFast 32 1,5),some (subcubeFast 0 33,5),some (subcubeFast 0 35,4),some (subcubeFast 0 32,9),some (subcubeFast 0 48,6),some (subcubeFast 0 8,9),some (subcubeFast 2 0,6),some (subcubeFast 0 12,5),some (subcubeFast 1 16,5),some (subcubeFast 2 16,5),some (subcubeFast 1 0,6),some (subcubeFast 1 8,5),some (subcubeFast 0 18,6),some (subcubeFast 4 24,4),some (subcubeFast 4 16,5),some (subcubeFast 4 0,6),some (subcubeFast 0 40,6),some (subcubeFast 32 10,4),some (subcubeFast 0 4,8),some (subcubeFast 2 24,4),some (subcubeFast 0 24,7),some (subcubeFast 4 8,5),some (subcubeFast 32 0,8),some (subcubeFast 32 8,7),some (subcubeFast 32 2,5),some (subcubeFast 0 9,5),some (subcubeFast 2 8,5),some (subcubeFast 0 2,8),some (subcubeFast 32 12,4),some (subcubeFast 32 4,5),some (subcubeFast 32 24,4),some (subcubeFast 0 6,5),some (subcubeFast 0 37,4),some (subcubeFast 32 16,5),some (subcubeFast 0 34,5)]
def slices_46 : BT (Option (Nat × Nat)) := btOfList 6 slicesL_46
def ps_46 : BT (Option PoolSpec) := btOfList 9 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[(0,0,1),(1,0,1),(3,18,14),(2,170,2),(3,170,2),(1,249,301)]),some (5,[(0,0,1),(1,0,1),(3,18,14)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(2,170,2),(3,170,2),(1,249,231)]),some (6,[]),some (4,[(0,0,1),(1,0,1),(3,18,14),(0,170,2),(1,170,2),(3,279,268)]),some (7,[]),some (8,[]),some (9,[]),some (10,[]),some (11,[]),some (12,[]),some (13,[]),some (4,[(0,0,1),(1,0,1),(3,18,14),(0,170,5),(3,267,2)]),some (14,[(0,0,1),(1,0,1),(0,14,3),(0,62,4)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(2,170,2),(3,170,2)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(0,170,2),(1,170,2)]),some (15,[(0,0,1),(1,0,1),(3,18,14)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(2,170,2),(3,170,2),(1,249,231)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(2,170,2),(3,170,2)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(0,170,2),(1,170,2),(3,279,268)]),some (17,[]),some (4,[(0,0,1),(1,0,1),(3,18,14),(0,170,2),(1,279,7)]),some (18,[]),some (19,[]),some (20,[]),some (21,[]),some (22,[]),some (23,[]),some (24,[]),some (25,[]),some (26,[]),some (27,[(0,0,1),(1,0,1),(3,18,14)]),some (28,[]),some (16,[]),some (29,[]),some (30,[]),some (4,[(0,0,1),(1,0,1),(3,18,14),(3,170,2)]),some (31,[]),some (14,[(1,0,1),(0,14,3),(0,62,4)]),some (10,[(0,2,3),(0,2,4),(0,3,4)]),some (5,[(0,0,1),(1,0,1)]),some (14,[(0,0,1),(1,0,1),(0,14,3),(0,3,4)]),some (2,[(1,2,7)]),some (15,[(0,0,1),(1,0,1)]),some (2,[(0,2,3)]),some (2,[(2,2,7)]),some (32,[]),some (29,[(0,0,3),(0,0,4),(0,3,4)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(3,253,2)]),some (14,[(0,0,1),(1,0,1),(3,18,14),(0,3,4)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(3,232,2)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(0,232,2)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(0,261,2)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(0,170,2)]),some (4,[]),some (27,[(0,0,1),(1,0,1)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(0,170,2)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(1,170,2)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(1,170,61)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(2,170,7)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(1,170,2)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(3,170,2)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(2,170,2)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(3,261,2)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(3,276,2)]),some (33,[(0,0,1),(0,18,4),(3,31,2)]),some (4,[(0,0,1),(1,0,1),(3,31,14),(3,274,2)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(0,170,2),(1,170,2)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(0,170,2),(3,279,5)]),some (5,[(0,0,1),(1,0,1),(3,31,14)]),some (2,[(1,18,7)]),some (4,[(0,0,1),(1,0,1),(1,2,7),(0,14,103)]),some (4,[(0,0,1),(1,0,1),(3,31,14),(0,274,2)]),some (16,[(0,0,1),(1,0,1),(3,39,14),(3,281,2)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(2,170,2)]),some (2,[(3,18,2)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(1,48,170)]),some (16,[(0,0,1),(1,0,1),(3,18,14),(1,36,170)]),some (16,[(0,0,1),(1,0,1),(3,39,14),(0,281,2)]),some (2,[(1,18,2)]),some (2,[(3,2,3)]),some (33,[]),some (14,[]),some (34,[(0,0,4),(3,11,1)]),some (4,[(3,11,1),(3,2,5),(1,53,26)]),some (35,[]),some (36,[]),some (34,[]),some (37,[]),some (34,[(0,1,4),(3,42,2)]),some (38,[]),some (29,[(0,0,3),(0,8,4)]),some (38,[(0,0,3),(0,8,4)]),some (38,[(0,0,3),(0,8,4),(3,55,2)]),some (29,[(0,0,3),(0,3,4)]),some (15,[]),some (2,[(3,8,1)]),some (5,[(0,0,3)]),some (14,[(0,0,3),(0,0,4),(3,11,1),(0,3,4)]),some (39,[]),some (5,[]),some (34,[(0,0,1),(0,0,4)]),some (14,[(0,2,3),(0,2,4),(0,3,4)]),some (5,[(2,0,1)]),some (38,[(0,2,3),(0,112,4)]),some (40,[]),some (27,[]),some (10,[(0,2,3),(0,61,4)]),some (14,[(0,2,3),(0,61,4),(2,0,113)]),some (10,[(0,1,3),(0,66,4)]),some (41,[]),some (14,[(0,0,1),(1,0,1),(0,14,4)]),some (2,[(3,2,5),(1,53,31)]),some (2,[(3,2,5),(1,53,16)]),some (4,[(2,0,1),(3,0,1),(2,2,7)]),some (4,[(1,0,1),(0,14,3),(0,2,3)]),some (4,[(2,0,1),(3,0,1),(1,2,7)]),some (27,[(2,0,1),(3,0,1)]),some (42,[]),some (5,[(2,0,1),(3,0,1)]),some (5,[(0,0,3),(3,8,1)]),some (15,[(2,0,1),(3,0,1)]),some (43,[]),some (14,[(2,0,1),(3,16,4),(0,1,3),(0,3,4)]),some (4,[(0,0,1),(1,0,1),(3,2,5)]),some (4,[(0,0,1),(1,0,1),(2,2,7)]),some (14,[(2,0,1),(3,16,3),(0,1,4),(0,3,4)]),some (14,[(0,0,1),(1,0,1),(0,14,3)]),some (31,[(1,0,1)]),some (38,[(0,2,3),(0,61,4),(2,0,113)]),some (4,[(1,0,1),(0,2,3),(2,14,61)]),some (34,[(0,0,1),(3,18,103)]),some (4,[(0,0,1),(1,2,7),(3,18,103)]),some (29,[(0,0,1),(0,4,5)]),some (14,[(2,0,1),(0,1,3),(0,66,4),(1,16,116)]),some (34,[(0,0,1)]),some (5,[(1,0,1)]),some (16,[(1,0,1),(0,14,4),(0,2,4)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(3,170,5)]),some (5,[(0,0,1)]),some (14,[(0,0,3),(3,8,1),(0,0,4),(0,3,4)]),some (29,[(0,0,3),(0,0,4)]),some (27,[(1,0,1)]),some (10,[(0,2,3)]),some (16,[(1,0,1),(0,2,4)]),some (14,[(0,0,1),(1,0,1),(3,18,14)]),some (38,[(0,2,3),(0,61,4)]),some (38,[(0,2,3),(0,3,4)]),some (16,[(1,0,1),(0,62,4),(0,2,4)]),some (34,[(0,0,1),(0,18,4)]),some (14,[(0,0,1),(0,18,4),(1,53,31)]),some (15,[(1,0,1)]),some (10,[(0,2,3),(0,3,4)]),some (10,[(0,18,2)]),some (34,[(0,0,1),(0,156,4)]),some (44,[]),some (34,[(0,0,1),(0,153,4)]),some (29,[(0,0,1),(0,153,4)]),some (34,[(0,0,1),(0,1,4)]),some (14,[(0,0,1),(0,0,3),(0,1,4),(0,3,4)]),some (16,[(0,0,1),(1,0,1),(3,18,14)]),some (10,[(0,2,3),(0,2,4)]),some (33,[(0,0,1),(3,18,2)]),some (4,[(0,0,1),(1,0,1),(1,2,7)]),some (29,[(0,0,1),(0,18,4)]),some (4,[(1,0,1),(1,2,7),(0,14,103)]),some (2,[(0,3,5)]),some (14,[(1,0,1),(0,14,3),(0,3,4)]),some (14,[(0,0,1),(1,0,1),(0,14,4),(0,3,4)]),some (4,[(2,0,1),(1,2,7),(3,16,103)]),some (14,[(0,0,1),(0,18,3),(3,39,2)]),some (10,[(0,62,2)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(3,2,5)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(0,2,5)]),some (16,[(1,0,1),(0,14,4),(3,36,4)]),some (10,[(3,170,2)]),some (4,[(0,0,1),(1,0,1),(3,18,14),(0,170,5)]),some (2,[(3,2,5)]),some (10,[(0,18,4),(3,31,2)]),some (2,[(3,2,5),(1,53,18)]),some (4,[(0,0,1),(3,2,5),(1,53,18)]),some (23,[(3,2,5),(1,53,31)]),some (4,[(1,0,1),(0,14,3),(3,48,3)]),some (14,[(0,0,1),(0,18,4),(3,31,2)]),some (14,[(0,0,1),(0,18,4),(0,0,3),(0,3,4)]),some (2,[(3,18,5)]),some (10,[(0,18,3),(3,39,2)]),some (10,[(0,2,3),(3,61,4)]),some (16,[(0,0,1),(1,0,1),(3,39,14)]),some (4,[(1,0,1),(0,2,3),(2,14,113)]),some (14,[(0,0,1),(0,18,3),(0,0,4),(0,3,4)]),some (4,[(0,0,1),(1,0,1),(0,2,5),(2,14,52)]),some (2,[(3,2,5),(1,53,27)]),some (34,[(0,0,1),(3,39,2)]),some (10,[(0,2,4),(3,56,3)]),some (2,[(3,1,5),(3,43,2)]),some (45,[]),some (2,[(3,67,1)]),some (34,[(0,0,4),(3,30,1)]),some (14,[(0,0,4),(3,11,3),(3,30,1)]),some (14,[(0,0,4),(3,11,1),(3,26,2)]),some (38,[(0,0,4),(3,26,2)]),some (23,[(3,2,5)]),some (14,[(0,0,4),(0,11,1)]),some (23,[(0,2,5)]),some (2,[(0,2,5)]),some (14,[(0,0,4),(3,11,1),(3,26,3)]),some (34,[(3,15,1)]),some (34,[(3,15,1),(0,1,4)]),some (34,[(3,15,1),(0,0,4)]),some (34,[(3,15,1),(0,60,4)]),some (14,[(0,0,3),(0,0,4),(0,3,4)]),some (34,[(0,0,4)]),some (14,[(0,0,3),(0,0,4),(3,11,1)]),some (14,[(0,0,3),(0,8,4),(3,55,1)]),some (34,[(0,8,4),(3,55,1)]),some (10,[(0,8,4),(3,55,1)]),some (14,[(0,0,3),(0,8,4),(1,55,1)]),some (38,[(0,0,3)]),some (29,[(0,0,3),(3,8,1)]),some (38,[(0,0,3),(0,3,4)]),some (14,[(0,0,3),(3,8,2)]),some (4,[(2,0,1),(2,2,7)]),some (4,[(2,0,1),(1,2,7)]),some (27,[(2,0,1)]),some (4,[(2,0,1),(3,2,5),(1,53,16)]),some (5,[(0,3,5)]),some (27,[(0,2,4)]),some (14,[(0,2,4),(3,56,3)]),some (14,[(2,0,1),(3,0,1)]),some (10,[(0,2,3),(1,16,61)]),some (38,[(0,2,3)]),some (14,[(2,0,1),(3,16,4)]),some (4,[(1,0,1),(2,2,7)]),some (14,[(2,0,1),(0,1,4)]),some (4,[(2,0,1),(3,2,5)]),some (14,[(0,2,3),(0,61,4)]),some (14,[(2,0,1),(3,0,1),(0,3,4)]),some (23,[(0,0,3)]),some (14,[(0,0,3),(0,1,4),(0,3,4)]),some (34,[(0,1,4)]),some (4,[(3,13,1),(3,2,5)]),some (4,[(1,0,1),(0,2,3)]),some (14,[(0,2,3),(0,2,4)]),some (14,[(0,0,1),(0,18,4)]),some (33,[(0,0,1),(0,18,4)]),some (14,[(2,0,1),(3,16,4),(0,3,4)]),some (14,[(0,0,1),(0,0,3),(3,8,4)]),some (14,[(2,0,1),(3,16,4),(0,1,3)]),some (2,[(3,55,1)]),some (14,[(0,0,4),(0,11,3),(3,55,1)]),some (2,[(3,31,2)]),some (14,[(2,0,1),(3,16,3),(0,3,4)]),some (14,[(2,0,1),(3,16,3),(0,1,4)]),some (10,[(0,1,4),(3,42,2)]),some (10,[(3,16,3)]),some (10,[(3,16,2),(0,4,5)]),some (14,[(1,0,1),(0,14,4)]),some (4,[(0,0,1),(2,2,7)]),some (15,[(0,0,1)]),some (10,[(3,16,2),(0,2,4)]),some (33,[(0,0,1)]),some (10,[(3,16,2),(0,51,4)]),some (10,[(3,16,2),(0,1,4)]),some (14,[(2,0,1),(3,16,2),(0,1,4)]),some (10,[(3,16,2),(0,51,3)]),some (38,[(0,0,3),(3,39,2)]),some (14,[(0,0,3),(0,8,1),(3,39,2)]),some (34,[(0,8,1),(3,39,2)]),some (29,[(0,0,1)]),some (14,[(0,0,1),(1,0,1)]),some (4,[(1,0,1),(1,2,7)]),some (33,[(0,0,1),(0,0,4)]),some (4,[(0,0,1),(3,2,5)]),some (14,[(0,0,1),(0,0,4)]),some (4,[(1,0,1),(0,3,5)]),some (14,[(2,0,1),(0,1,3),(0,3,4)]),some (14,[(0,0,1),(0,2,4)]),some (14,[(0,0,4),(3,11,1)]),some (4,[(1,0,1),(3,2,3)]),some (16,[(1,0,1),(3,36,4)]),some (14,[(0,0,4),(3,11,1),(0,3,4)]),some (16,[(1,0,1),(2,4,5)]),some (16,[(1,0,1),(3,2,4)]),some (16,[(1,0,1),(3,61,4)]),some (14,[(0,2,3),(3,61,4)]),some (16,[(1,0,1),(0,14,4)]),some (33,[(0,0,1),(0,18,2)]),some (14,[(0,0,3),(3,8,1),(0,3,4)]),some (34,[(0,0,1),(3,18,4)]),some (4,[(0,0,1),(0,2,5)]),some (10,[(0,59,3)]),some (14,[(0,0,1),(2,2,7)]),some (4,[(1,0,1),(3,48,3)]),some (4,[(0,0,1),(1,2,7)]),some (38,[(0,18,3),(3,39,2)]),some (4,[(2,0,1),(0,2,5)]),some (14,[(2,0,1),(3,16,3),(0,38,4)]),some (29,[(0,0,1),(0,18,3)]),some (33,[(0,0,1),(3,18,4)]),some (29,[(0,0,1),(3,18,4)]),some (29,[(0,0,1),(0,0,3)]),some (38,[(0,0,3),(3,34,2)]),some (29,[(0,0,1),(0,0,4)]),some (14,[(0,0,1),(0,0,4),(0,3,4)]),some (10,[(3,16,2),(0,2,3)]),some (14,[(0,0,1),(0,0,3)]),some (14,[(0,0,1),(0,0,3),(0,3,4)]),some (4,[(0,0,1),(1,0,1),(0,2,5)]),some (34,[(0,0,1),(3,63,4)]),some (34,[(0,0,1),(3,15,4)]),some (14,[(0,0,1),(0,0,3),(0,1,4)]),some (16,[(0,0,1),(1,0,1)]),some (16,[(2,0,1),(3,0,1)]),some (14,[(1,0,1),(0,14,4),(0,3,4)]),some (34,[(0,0,1),(0,8,4)]),some (14,[(0,0,1),(0,0,3),(0,8,4)]),some (14,[(0,0,3),(3,8,1)]),some (27,[(0,0,1)]),some (38,[(0,18,4),(3,31,2)]),some (4,[(1,0,1),(0,14,3),(0,3,5)]),some (14,[(1,0,1),(0,14,3)]),some (14,[(0,0,3),(3,8,4),(3,41,1)]),some (27,[(3,2,4)]),some (14,[(0,0,1),(0,18,4),(3,31,3)]),some (14,[(0,0,1),(0,18,4),(0,3,4)]),some (14,[(0,0,1),(0,2,3)]),some (14,[(0,0,1),(0,18,4),(0,0,3)]),some (14,[(0,0,3),(0,8,4)]),some (29,[(0,0,1),(3,18,3)]),some (14,[(0,0,1),(0,18,3)]),some (33,[(0,2,4)]),some (14,[(0,0,1),(0,18,2)]),some (14,[(0,0,1),(0,18,3),(0,0,4)]),some (34,[(0,0,1),(3,39,4)]),some (14,[(0,0,1),(0,18,3),(3,39,4)]),some (2,[(0,3,5),(2,1,17)]),some (34,[(0,0,1),(0,39,4)]),some (14,[(0,0,1),(0,18,3),(0,39,4)]),some (14,[(2,0,1),(0,1,3),(0,66,4)]),some (14,[(0,0,1),(1,0,1),(0,3,4)]),some (14,[(0,0,3),(3,8,1),(0,0,4)]),some (16,[(1,0,1),(0,62,4)]),some (16,[(1,0,1),(0,61,4)]),some (10,[(0,18,3)]),some (33,[(0,0,4),(3,11,1)]),some (14,[(0,0,3),(3,8,1),(3,34,4)]),some (29,[(0,0,4),(3,11,1)]),some (14,[(2,0,1),(0,1,3)]),some (14,[(2,0,1),(0,1,4),(0,3,4)]),some (34,[(0,0,1),(3,18,2)]),some (14,[(0,0,1),(0,18,3),(0,3,4)]),some (15,[(2,0,1)]),some (10,[(3,16,2),(0,1,3)]),some (14,[(2,0,1),(3,16,2),(0,1,3)]),some (14,[(2,0,1),(3,16,2)]),some (14,[(0,0,1),(0,0,4),(3,11,3)]),some (14,[(3,12,1)]),some (14,[(3,10,1)]),some (4,[(0,1,5)]),some (14,[(3,0,4),(3,13,3)]),some (2,[(0,1,5)]),some (33,[(0,0,4)]),some (4,[(0,0,5)]),some (14,[(3,0,3)]),some (14,[(0,0,4),(3,11,3)]),some (4,[(0,0,1)]),some (33,[(0,0,2)]),some (14,[(1,0,1)]),some (14,[(0,0,3),(0,3,4)]),some (14,[(3,0,3),(0,0,4)]),some (29,[(0,0,3)]),some (14,[(0,0,3),(3,0,4)]),some (14,[(0,0,4)]),some (14,[(0,0,3)]),some (14,[(0,0,3),(0,0,4)]),some (16,[(3,8,1)]),some (16,[(2,0,1)]),some (14,[(2,0,1),(3,16,3)]),some (14,[(0,0,3),(0,8,1)]),some (34,[(0,8,1)]),some (14,[(0,0,1)]),some (16,[(1,0,1)]),some (14,[(2,0,1)]),some (14,[(0,0,3),(3,8,4)]),some (14,[(2,0,1),(0,3,4)]),some (14,[(3,0,4)]),some (38,[(0,18,2)]),some (16,[(0,0,1)]),some (2,[(3,1,5)]),some (10,[(3,16,2)]),some (38,[(0,18,3)]),some (14,[(0,0,4),(0,11,3)]),some (23,[(3,0,3)]),some (14,[(0,0,1),(0,3,4)]),some (16,[(3,15,1)]),some (34,[(0,8,4)]),some (14,[(0,0,4),(0,3,4)]),some (14,[(0,0,3),(0,1,4)]),some (4,[(3,13,1)]),some (10,[(0,1,3)]),some (14,[(1,0,1),(0,3,4)]),some (34,[(3,15,4)]),some (14,[(3,0,3),(3,15,4)]),some (14,[(0,3,4)])]
lemma gp_46 : goodPairs G_46 pos_46 neg_46 := goodPairs_of (by decide +kernel)
lemma base_46_ok : ∀ x ∈ base_46, faithful pos_46 neg_46 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_46_ok : btAll (fun x => faithful pos_46 neg_46 x ∧ x.1 < 2^128) W_46 := buildWiresBT_faithful base_46_ok
set_option maxRecDepth 500000 in
lemma autos_46_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_46 = G_46) autos_46 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_46_0_ok : sliceDirectCheck 32 9 0 R_46 G_46 R_6 G_6 = true := by decide +kernel
lemma sl_46_0 : Slice R_46 G_46 (subcubeFast 32 9) 4 := slice_fast_direct sl_46_0_ok low_6
lemma sl_46_1_ok : sliceDirectCheck 0 38 0 R_46 G_46 R_7 G_7 = true := by decide +kernel
lemma sl_46_1 : Slice R_46 G_46 (subcubeFast 0 38) 4 := slice_fast_direct sl_46_1_ok low_7
lemma sl_46_2_ok : sliceDirectCheck 0 17 0 R_46 G_46 R_14 G_14 = true := by decide +kernel
lemma sl_46_2 : Slice R_46 G_46 (subcubeFast 0 17) 6 := slice_fast_direct sl_46_2_ok low_14
lemma sl_46_3_ok : sliceDirectCheck 0 5 0 R_46 G_46 R_33 G_33 = true := by decide +kernel
lemma sl_46_3 : Slice R_46 G_46 (subcubeFast 0 5) 5 := slice_fast_direct sl_46_3_ok low_33
lemma sl_46_4_ok : sliceDirectCheck 0 16 0 R_46 G_46 R_39 G_39 = true := by decide +kernel
lemma sl_46_4 : Slice R_46 G_46 (subcubeFast 0 16) 9 := slice_fast_direct sl_46_4_ok low_39
lemma sl_46_5_ok : sliceDirectCheck 0 20 0 R_46 G_46 R_29 G_29 = true := by decide +kernel
lemma sl_46_5 : Slice R_46 G_46 (subcubeFast 0 20) 6 := slice_fast_direct sl_46_5_ok low_29
lemma sl_46_6_ok : sliceDirectCheck 1 24 0 R_46 G_46 R_0 G_0 = true := by decide +kernel
lemma sl_46_6 : Slice R_46 G_46 (subcubeFast 1 24) 4 := slice_fast_direct sl_46_6_ok low_0
lemma sl_46_7_ok : sliceDirectCheck 0 36 0 R_46 G_46 R_28 G_28 = true := by decide +kernel
lemma sl_46_7 : Slice R_46 G_46 (subcubeFast 0 36) 5 := slice_fast_direct sl_46_7_ok low_28
lemma sl_46_8_ok : sliceDirectCheck 0 10 0 R_46 G_46 R_35 G_35 = true := by decide +kernel
lemma sl_46_8 : Slice R_46 G_46 (subcubeFast 0 10) 5 := slice_fast_direct sl_46_8_ok low_35
lemma sl_46_9_ok : sliceDirectCheck 0 3 0 R_46 G_46 R_15 G_15 = true := by decide +kernel
lemma sl_46_9 : Slice R_46 G_46 (subcubeFast 0 3) 5 := slice_fast_direct sl_46_9_ok low_15
lemma sl_46_10_ok : sliceDirectCheck 0 1 0 R_46 G_46 R_41 G_41 = true := by decide +kernel
lemma sl_46_10 : Slice R_46 G_46 (subcubeFast 0 1) 8 := slice_fast_direct sl_46_10_ok low_41
lemma sl_46_11_ok : sliceDirectCheck 32 1 0 R_46 G_46 R_24 G_24 = true := by decide +kernel
lemma sl_46_11 : Slice R_46 G_46 (subcubeFast 32 1) 5 := slice_fast_direct sl_46_11_ok low_24
lemma sl_46_12_ok : sliceDirectCheck 0 33 0 R_46 G_46 R_13 G_13 = true := by decide +kernel
lemma sl_46_12 : Slice R_46 G_46 (subcubeFast 0 33) 5 := slice_fast_direct sl_46_12_ok low_13
lemma sl_46_13_ok : sliceDirectCheck 0 35 0 R_46 G_46 R_9 G_9 = true := by decide +kernel
lemma sl_46_13 : Slice R_46 G_46 (subcubeFast 0 35) 4 := slice_fast_direct sl_46_13_ok low_9
lemma sl_46_14_ok : sliceDirectCheck 0 32 0 R_46 G_46 R_38 G_38 = true := by decide +kernel
lemma sl_46_14 : Slice R_46 G_46 (subcubeFast 0 32) 9 := slice_fast_direct sl_46_14_ok low_38
lemma sl_46_15_ok : sliceDirectCheck 0 48 0 R_46 G_46 R_26 G_26 = true := by decide +kernel
lemma sl_46_15 : Slice R_46 G_46 (subcubeFast 0 48) 6 := slice_fast_direct sl_46_15_ok low_26
lemma sl_46_16_ok : sliceDirectCheck 0 8 0 R_46 G_46 R_40 G_40 = true := by decide +kernel
lemma sl_46_16 : Slice R_46 G_46 (subcubeFast 0 8) 9 := slice_fast_direct sl_46_16_ok low_40
lemma sl_46_17_ok : sliceDirectCheck 2 0 0 R_46 G_46 R_43 G_43 = true := by decide +kernel
lemma sl_46_17 : Slice R_46 G_46 (subcubeFast 2 0) 6 := slice_fast_direct sl_46_17_ok low_43
lemma sl_46_18_ok : sliceDirectCheck 0 12 0 R_46 G_46 R_34 G_34 = true := by decide +kernel
lemma sl_46_18 : Slice R_46 G_46 (subcubeFast 0 12) 5 := slice_fast_direct sl_46_18_ok low_34
lemma sl_46_19_ok : sliceDirectCheck 1 16 0 R_46 G_46 R_25 G_25 = true := by decide +kernel
lemma sl_46_19 : Slice R_46 G_46 (subcubeFast 1 16) 5 := slice_fast_direct sl_46_19_ok low_25
lemma sl_46_20_ok : sliceDirectCheck 2 16 0 R_46 G_46 R_22 G_22 = true := by decide +kernel
lemma sl_46_20 : Slice R_46 G_46 (subcubeFast 2 16) 5 := slice_fast_direct sl_46_20_ok low_22
lemma sl_46_21_ok : sliceDirectCheck 1 0 0 R_46 G_46 R_37 G_37 = true := by decide +kernel
lemma sl_46_21 : Slice R_46 G_46 (subcubeFast 1 0) 6 := slice_fast_direct sl_46_21_ok low_37
lemma sl_46_22_ok : sliceDirectCheck 1 8 0 R_46 G_46 R_11 G_11 = true := by decide +kernel
lemma sl_46_22 : Slice R_46 G_46 (subcubeFast 1 8) 5 := slice_fast_direct sl_46_22_ok low_11
lemma sl_46_23_ok : sliceDirectCheck 0 18 0 R_46 G_46 R_31 G_31 = true := by decide +kernel
lemma sl_46_23 : Slice R_46 G_46 (subcubeFast 0 18) 6 := slice_fast_direct sl_46_23_ok low_31
lemma sl_46_24_ok : sliceDirectCheck 4 24 0 R_46 G_46 R_3 G_3 = true := by decide +kernel
lemma sl_46_24 : Slice R_46 G_46 (subcubeFast 4 24) 4 := slice_fast_direct sl_46_24_ok low_3
lemma sl_46_25_ok : sliceDirectCheck 4 16 0 R_46 G_46 R_19 G_19 = true := by decide +kernel
lemma sl_46_25 : Slice R_46 G_46 (subcubeFast 4 16) 5 := slice_fast_direct sl_46_25_ok low_19
lemma sl_46_26_ok : sliceDirectCheck 4 0 0 R_46 G_46 R_42 G_42 = true := by decide +kernel
lemma sl_46_26 : Slice R_46 G_46 (subcubeFast 4 0) 6 := slice_fast_direct sl_46_26_ok low_42
lemma sl_46_27_ok : sliceDirectCheck 0 40 0 R_46 G_46 R_27 G_27 = true := by decide +kernel
lemma sl_46_27 : Slice R_46 G_46 (subcubeFast 0 40) 6 := slice_fast_direct sl_46_27_ok low_27
lemma sl_46_28_ok : sliceDirectCheck 32 10 0 R_46 G_46 R_4 G_4 = true := by decide +kernel
lemma sl_46_28 : Slice R_46 G_46 (subcubeFast 32 10) 4 := slice_fast_direct sl_46_28_ok low_4
lemma sl_46_29_ok : sliceDirectCheck 0 4 0 R_46 G_46 R_44 G_44 = true := by decide +kernel
lemma sl_46_29 : Slice R_46 G_46 (subcubeFast 0 4) 8 := slice_fast_direct sl_46_29_ok low_44
lemma sl_46_30_ok : sliceDirectCheck 2 24 0 R_46 G_46 R_5 G_5 = true := by decide +kernel
lemma sl_46_30 : Slice R_46 G_46 (subcubeFast 2 24) 4 := slice_fast_direct sl_46_30_ok low_5
lemma sl_46_31_ok : sliceDirectCheck 0 24 0 R_46 G_46 R_12 G_12 = true := by decide +kernel
lemma sl_46_31 : Slice R_46 G_46 (subcubeFast 0 24) 7 := slice_fast_direct sl_46_31_ok low_12
lemma sl_46_32_ok : sliceDirectCheck 4 8 0 R_46 G_46 R_20 G_20 = true := by decide +kernel
lemma sl_46_32 : Slice R_46 G_46 (subcubeFast 4 8) 5 := slice_fast_direct sl_46_32_ok low_20
lemma sl_46_33_ok : sliceDirectCheck 32 0 0 R_46 G_46 R_36 G_36 = true := by decide +kernel
lemma sl_46_33 : Slice R_46 G_46 (subcubeFast 32 0) 8 := slice_fast_direct sl_46_33_ok low_36
lemma sl_46_34_ok : sliceDirectCheck 32 8 0 R_46 G_46 R_10 G_10 = true := by decide +kernel
lemma sl_46_34 : Slice R_46 G_46 (subcubeFast 32 8) 7 := slice_fast_direct sl_46_34_ok low_10
lemma sl_46_35_ok : sliceDirectCheck 32 2 0 R_46 G_46 R_21 G_21 = true := by decide +kernel
lemma sl_46_35 : Slice R_46 G_46 (subcubeFast 32 2) 5 := slice_fast_direct sl_46_35_ok low_21
lemma sl_46_36_ok : sliceDirectCheck 0 9 0 R_46 G_46 R_16 G_16 = true := by decide +kernel
lemma sl_46_36 : Slice R_46 G_46 (subcubeFast 0 9) 5 := slice_fast_direct sl_46_36_ok low_16
lemma sl_46_37_ok : sliceDirectCheck 2 8 0 R_46 G_46 R_23 G_23 = true := by decide +kernel
lemma sl_46_37 : Slice R_46 G_46 (subcubeFast 2 8) 5 := slice_fast_direct sl_46_37_ok low_23
lemma sl_46_38_ok : sliceDirectCheck 0 2 0 R_46 G_46 R_45 G_45 = true := by decide +kernel
lemma sl_46_38 : Slice R_46 G_46 (subcubeFast 0 2) 8 := slice_fast_direct sl_46_38_ok low_45
lemma sl_46_39_ok : sliceDirectCheck 32 12 0 R_46 G_46 R_2 G_2 = true := by decide +kernel
lemma sl_46_39 : Slice R_46 G_46 (subcubeFast 32 12) 4 := slice_fast_direct sl_46_39_ok low_2
lemma sl_46_40_ok : sliceDirectCheck 32 4 0 R_46 G_46 R_18 G_18 = true := by decide +kernel
lemma sl_46_40 : Slice R_46 G_46 (subcubeFast 32 4) 5 := slice_fast_direct sl_46_40_ok low_18
lemma sl_46_41_ok : sliceDirectCheck 32 24 0 R_46 G_46 R_1 G_1 = true := by decide +kernel
lemma sl_46_41 : Slice R_46 G_46 (subcubeFast 32 24) 4 := slice_fast_direct sl_46_41_ok low_1
lemma sl_46_42_ok : sliceDirectCheck 0 6 0 R_46 G_46 R_32 G_32 = true := by decide +kernel
lemma sl_46_42 : Slice R_46 G_46 (subcubeFast 0 6) 5 := slice_fast_direct sl_46_42_ok low_32
lemma sl_46_43_ok : sliceDirectCheck 0 37 0 R_46 G_46 R_8 G_8 = true := by decide +kernel
lemma sl_46_43 : Slice R_46 G_46 (subcubeFast 0 37) 4 := slice_fast_direct sl_46_43_ok low_8
lemma sl_46_44_ok : sliceDirectCheck 32 16 0 R_46 G_46 R_17 G_17 = true := by decide +kernel
lemma sl_46_44 : Slice R_46 G_46 (subcubeFast 32 16) 5 := slice_fast_direct sl_46_44_ok low_17
lemma sl_46_45_ok : sliceDirectCheck 0 34 0 R_46 G_46 R_30 G_30 = true := by decide +kernel
lemma sl_46_45 : Slice R_46 G_46 (subcubeFast 0 34) 5 := slice_fast_direct sl_46_45_ok low_30
set_option maxRecDepth 500000 in
lemma slices_46_ok : btAll (fun o => ∀ p, o = some p → Slice R_46 G_46 p.1 p.2) slices_46 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_46 G_46 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_46_0) (forall_cons (fun _ h => by cases h; exact sl_46_1) (forall_cons (fun _ h => by cases h; exact sl_46_2) (forall_cons (fun _ h => by cases h; exact sl_46_3) (forall_cons (fun _ h => by cases h; exact sl_46_4) (forall_cons (fun _ h => by cases h; exact sl_46_5) (forall_cons (fun _ h => by cases h; exact sl_46_6) (forall_cons (fun _ h => by cases h; exact sl_46_7) (forall_cons (fun _ h => by cases h; exact sl_46_8) (forall_cons (fun _ h => by cases h; exact sl_46_9) (forall_cons (fun _ h => by cases h; exact sl_46_10) (forall_cons (fun _ h => by cases h; exact sl_46_11) (forall_cons (fun _ h => by cases h; exact sl_46_12) (forall_cons (fun _ h => by cases h; exact sl_46_13) (forall_cons (fun _ h => by cases h; exact sl_46_14) (forall_cons (fun _ h => by cases h; exact sl_46_15) (forall_cons (fun _ h => by cases h; exact sl_46_16) (forall_cons (fun _ h => by cases h; exact sl_46_17) (forall_cons (fun _ h => by cases h; exact sl_46_18) (forall_cons (fun _ h => by cases h; exact sl_46_19) (forall_cons (fun _ h => by cases h; exact sl_46_20) (forall_cons (fun _ h => by cases h; exact sl_46_21) (forall_cons (fun _ h => by cases h; exact sl_46_22) (forall_cons (fun _ h => by cases h; exact sl_46_23) (forall_cons (fun _ h => by cases h; exact sl_46_24) (forall_cons (fun _ h => by cases h; exact sl_46_25) (forall_cons (fun _ h => by cases h; exact sl_46_26) (forall_cons (fun _ h => by cases h; exact sl_46_27) (forall_cons (fun _ h => by cases h; exact sl_46_28) (forall_cons (fun _ h => by cases h; exact sl_46_29) (forall_cons (fun _ h => by cases h; exact sl_46_30) (forall_cons (fun _ h => by cases h; exact sl_46_31) (forall_cons (fun _ h => by cases h; exact sl_46_32) (forall_cons (fun _ h => by cases h; exact sl_46_33) (forall_cons (fun _ h => by cases h; exact sl_46_34) (forall_cons (fun _ h => by cases h; exact sl_46_35) (forall_cons (fun _ h => by cases h; exact sl_46_36) (forall_cons (fun _ h => by cases h; exact sl_46_37) (forall_cons (fun _ h => by cases h; exact sl_46_38) (forall_cons (fun _ h => by cases h; exact sl_46_39) (forall_cons (fun _ h => by cases h; exact sl_46_40) (forall_cons (fun _ h => by cases h; exact sl_46_41) (forall_cons (fun _ h => by cases h; exact sl_46_42) (forall_cons (fun _ h => by cases h; exact sl_46_43) (forall_cons (fun _ h => by cases h; exact sl_46_44) (forall_cons (fun _ h => by cases h; exact sl_46_45) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))))
def bk_46_init : BT (List (List Nat)) := BT.empty
lemma bk_46_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 (0 - 1) xs.toFinset) bk_46_init := trivial
def nodes_46_0 : List NodeSpec := []
def P_46_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_0 : checkNodesBT W_46 G_46 fmask_46 P_46_0 autos_46 bk_46_init 0 nodes_46_0 = true := by decide +kernel
def bk_46_0 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_0
set_option maxRecDepth 500000 in
lemma bk_46_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 0 xs.toFinset) bk_46_0 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_init_ok chk_46_0
def nodes_46_1 : List NodeSpec := []
def P_46_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_1 : checkNodesBT W_46 G_46 fmask_46 P_46_1 autos_46 bk_46_0 1 nodes_46_1 = true := by decide +kernel
def bk_46_1 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_1
set_option maxRecDepth 500000 in
lemma bk_46_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 1 xs.toFinset) bk_46_1 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_0_ok chk_46_1
def nodes_46_2 : List NodeSpec := []
def P_46_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_2 : checkNodesBT W_46 G_46 fmask_46 P_46_2 autos_46 bk_46_1 2 nodes_46_2 = true := by decide +kernel
def bk_46_2 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_2
set_option maxRecDepth 500000 in
lemma bk_46_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 2 xs.toFinset) bk_46_2 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_1_ok chk_46_2
def nodes_46_3 : List NodeSpec := [([418,18,3,7],[],[]),([398,242,3,7],[],[]),([231,417,3,7],[],[]),([231,358,9,7],[],[]),([416,9,3,7],[],[])]
def P_46_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_3 : checkNodesBT W_46 G_46 fmask_46 P_46_3 autos_46 bk_46_2 3 nodes_46_3 = true := by decide +kernel
def bk_46_3 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_3
set_option maxRecDepth 500000 in
lemma bk_46_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 3 xs.toFinset) bk_46_3 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_2_ok chk_46_3
def nodes_46_4 : List NodeSpec := [([394,18,111,2,3],[],[]),([300,18,428,3,4],[],[]),([442,18,3,4,5],[],[]),([443,18,3,4,5],[],[]),([170,2,329,9,7],[],[]),([170,56,329,9,5],[],[]),([170,442,3,4,5],[],[]),([339,170,2,9,7],[],[]),([170,443,3,4,5],[],[]),([300,261,2,9,5],[0],[]),([339,232,2,9,5],[],[]),([170,61,323,9,5],[],[]),([170,231,61,9,7],[],[]),([300,18,318,3,4],[1],[]),([170,313,56,9,5],[2],[]),([339,329,3,4,5],[],[]),([261,353,2,9,5],[0],[]),([231,232,61,9,5],[],[]),([247,18,111,61,7],[],[]),([231,385,3,4,5],[],[]),([313,416,3,4,5],[],[]),([314,231,347,3,5],[],[]),([313,232,2,9,5],[2],[]),([231,444,3,4,5],[4],[]),([170,2,341,9,7],[],[]),([231,261,2,9,7],[],[]),([315,231,358,4,5],[],[]),([231,416,3,7,4],[],[]),([418,18,3,4,5],[],[0]),([170,313,2,9,7],[],[]),([314,416,3,4,5],[],[]),([445,231,3,4,5],[],[]),([446,231,3,4,5],[],[]),([231,417,3,4,5],[],[0]),([170,2,358,9,7],[],[0]),([231,358,3,7,4],[],[0]),([18,111,56,251,5],[],[]),([231,358,9,4,5],[],[0]),([315,416,3,4,5],[],[]),([18,258,242,3,7],[1],[0]),([232,326,2,9,5],[],[]),([301,416,3,4,5],[],[]),([170,326,2,9,7],[],[]),([231,447,3,4,5],[3],[]),([279,261,2,9,7],[0],[]),([170,56,341,9,5],[],[]),([231,347,3,7],[5],[0]),([231,261,56,9,5],[],[]),([18,448,3,4,5],[],[]),([296,18,111,2,7],[],[]),([170,61,268,9,7],[],[]),([418,0,1,3,7],[],[0]),([231,449,3,4,5],[6],[]),([18,111,2,297,7],[],[]),([450,2,3,4,5],[],[]),([231,451,3,4,5],[3],[]),([18,111,61,242,7],[7,0],[]),([413,231,3,4,5],[],[]),([170,301,61,9,5],[],[]),([231,347,9,3,5],[],[]),([170,61,335,9,5],[],[]),([279,268,9,3,7],[],[0]),([363,111,2,3,7],[],[]),([416,9,3,4,5],[],[0]),([398,111,2,3,7],[],[0]),([446,416,3,4,5],[],[]),([248,247,18,3,7],[],[0]),([170,2,417,3,7],[],[0]),([398,242,3,4,5],[],[0]),([451,416,3,4,5],[],[]),([449,416,3,4,5],[8],[]),([170,2,9,3,432],[],[]),([249,231,9,3,7],[],[0]),([355,18,430,3,4],[],[]),([416,3,7,4],[8,1],[0]),([445,416,3,4,5],[],[]),([301,261,2,9,5],[],[]),([18,452,3,4,5],[],[])]
def P_46_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [0,1,2,3,4,5,6,7,8]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_4 : checkNodesBT W_46 G_46 fmask_46 P_46_4 autos_46 bk_46_3 4 nodes_46_4 = true := by decide +kernel
def bk_46_4 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_4
set_option maxRecDepth 500000 in
lemma bk_46_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 4 xs.toFinset) bk_46_4 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_3_ok chk_46_4
def nd_46_5_0 : List NodeSpec := [([359,0,292,3,4,5],[],[1]),([0,1,258,242,3,7],[9],[0]),([296,0,1,111,2,7],[],[0]),([362,18,2,3,7,4],[1],[]),([294,18,2,3,4,5],[],[]),([18,54,2,3,263,5],[],[]),([18,62,225,2,4,5],[],[]),([62,113,2,236,4,5],[],[]),([18,111,62,61,56,5],[10],[]),([247,18,62,61,4,5],[],[]),([18,111,61,56,2,5],[],[]),([248,247,18,3,4,5],[],[0]),([18,111,2,297,4,5],[],[0]),([247,18,111,2,3,7],[2,7],[0]),([18,111,2,242,3,7],[7,0,2],[0]),([127,18,62,56,2,5],[],[]),([18,111,61,242,4,5],[0,7],[0]),([363,111,2,3,4,5],[],[0]),([62,61,2,236,4,5],[7],[]),([18,258,242,3,4,5],[1],[0]),([296,18,111,2,4,5],[],[0]),([204,18,111,56,3,5],[],[0]),([18,111,2,250,3,5],[],[]),([298,18,62,2,4,5],[],[]),([238,18,62,2,9,5],[0],[]),([339,18,62,2,4,5],[],[]),([18,308,62,61,4,5],[11],[]),([18,313,62,2,4,5],[12],[]),([18,232,364,2,3,4],[13],[]),([312,339,18,3,4,5],[],[0]),([170,314,18,2,3,7],[],[]),([365,170,18,2,3,4],[],[]),([18,111,61,56,5],[0,2],[]),([300,18,268,3,4,5],[1],[0]),([339,18,268,3,4,5],[3],[]),([170,366,2,3,4,5],[],[]),([18,111,61,2,7],[7,0,2],[0]),([170,367,2,3,7,4],[],[]),([170,368,2,3,4,5],[2],[]),([0,1,111,56,251,5],[],[0]),([170,369,2,3,4,5],[],[]),([170,2,3,370,4,5],[],[]),([170,371,2,3,4,5],[14],[]),([170,372,2,3,4,5],[],[]),([314,18,232,2,3,5],[],[]),([170,373,2,3,4,5],[],[]),([170,2,374,3,4,5],[],[]),([170,375,56,2,3,4],[],[]),([18,367,2,3,7,4],[15],[]),([170,61,323,3,4,5],[],[0]),([170,324,56,3,4,5],[2],[]),([127,170,61,56,3,5],[3],[]),([127,170,113,2,3,5],[12],[]),([170,2,376,3,4,5],[],[]),([328,313,2,3,4,5],[],[0]),([6,170,2,329,3,4],[],[]),([170,2,329,3,7,4],[],[0]),([170,2,377,3,4,5],[],[]),([204,18,62,56,9,5],[],[]),([170,56,329,3,4,5],[],[0]),([170,308,61,3,4,5],[11],[]),([378,170,2,3,4,5],[2,13],[]),([170,379,2,3,4,5],[],[]),([170,379,332,3,4,5],[16],[]),([170,2,323,9,3,5],[],[0]),([170,380,2,3,4,5],[],[]),([170,381,2,3,4,5],[13],[]),([170,307,61,3,4,5],[],[]),([170,382,2,3,4,5],[],[]),([170,366,2,3,7,4],[],[]),([170,383,2,3,4,5],[10,13,14],[]),([324,232,2,3,4,5],[2],[]),([384,170,2,3,4,5],[],[]),([170,2,385,3,4,5],[2,10],[0]),([170,386,2,3,4,5],[],[]),([170,232,364,2,3,4],[],[]),([170,387,2,3,4,5],[],[]),([388,170,2,3,4,5],[14,13],[]),([307,232,2,3,4,5],[3],[]),([170,301,311,3,4,5],[],[0]),([253,324,2,3,4,5],[],[]),([170,61,56,2,9,5],[3],[]),([170,2,389,3,4,5],[2],[]),([390,170,2,3,4,5],[],[]),([0,1,111,2,297,7],[],[0]),([36,170,306,3,4,5],[],[]),([170,306,61,3,4,5],[10],[]),([18,301,311,3,4,5],[],[0]),([331,2,329,3,4,5],[],[0]),([170,261,2,9,7],[7,0],[0]),([170,337,261,2,9,5],[10],[]),([6,339,170,2,3,4],[],[]),([339,170,2,3,7,4],[],[0]),([339,170,2,9,4,5],[],[0]),([391,170,2,3,4,5],[],[]),([324,261,2,3,4,5],[3],[]),([170,392,2,3,4,5],[],[]),([170,313,316,3,4,5],[],[0]),([261,2,329,3,4,5],[12],[0]),([170,261,232,2,9,5],[11],[]),([317,300,18,3,4,5],[],[0]),([170,393,2,3,4,5],[],[]),([170,337,232,2,3,5],[12],[]),([300,261,2,3,4,5],[0],[0]),([337,261,232,2,3,5],[11],[]),([339,253,2,3,4,5],[],[]),([394,0,1,111,2,3],[],[0]),([306,261,2,3,4,5],[],[]),([276,307,2,3,4,5],[],[]),([18,62,2,263,4,5],[],[]),([300,276,2,3,4,5],[0],[]),([170,270,2,3,4,5],[],[]),([170,308,2,3,7,4],[],[]),([48,170,308,3,4,5],[],[]),([170,395,2,3,4,5],[],[]),([18,111,2,251,4,5],[0],[0]),([102,170,231,3,4,5],[11,13],[]),([127,14,2,236,3,5],[],[]),([102,170,231,3,7,4],[15,13],[]),([170,231,396,3,4,5],[1],[]),([170,231,2,9,3,7],[7],[0]),([238,18,111,2,3,5],[0],[]),([339,232,2,3,4,5],[],[0]),([397,170,2,3,4,5],[],[]),([170,231,56,9,3,5],[7],[0]),([398,111,2,3,4,5],[],[0]),([170,231,399,3,4,5],[1],[]),([170,231,61,3,7,4],[15],[0]),([48,170,329,3,4,5],[],[]),([170,231,61,9,4,5],[],[0]),([127,170,231,3,4,5],[11],[]),([231,61,329,3,4,5],[11],[]),([355,18,319,3,4,5],[],[0]),([170,314,56,2,3,5],[12],[]),([170,400,2,3,4,5],[14],[]),([339,231,261,3,4,5],[3],[]),([36,170,314,3,4,5],[],[]),([170,301,61,3,4,5],[10],[0]),([18,258,111,2,3,7],[7,17,0],[0]),([170,314,301,2,3,5],[12],[]),([0,1,111,61,242,7],[7,0],[0]),([300,170,2,3,4,401],[13],[]),([6,170,315,2,3,4],[],[]),([170,232,61,2,9,5],[],[0]),([170,121,268,3,4,5],[3],[]),([170,315,56,3,4,5],[2],[]),([170,56,341,3,4,5],[],[0]),([249,315,231,3,4,5],[3],[0]),([170,315,61,2,4,5],[12],[]),([170,402,2,3,4,5],[],[]),([18,313,316,3,4,5],[],[0]),([231,2,329,3,4,5],[3],[]),([170,403,2,3,4,5],[],[]),([170,130,231,3,4,5],[3],[]),([339,170,313,3,4,5],[12],[0]),([247,0,1,111,61,7],[],[0]),([170,404,332,3,4,5],[],[]),([313,2,329,3,4,5],[12],[0]),([18,62,2,320,4,5],[11],[]),([170,2,329,3,4,5],[],[]),([291,290,0,3,4,5],[],[1]),([170,405,2,3,4,5],[],[]),([300,170,364,2,3,4],[14],[]),([300,170,231,3,4,5],[1],[]),([231,232,311,3,4,5],[],[]),([315,232,2,3,4,5],[2],[]),([300,231,232,3,4,5],[3,15],[]),([170,406,2,3,4,5],[],[]),([36,253,231,3,4,5],[3],[]),([253,231,61,3,4,5],[11],[]),([6,231,261,2,3,4],[1],[]),([231,261,2,9,4,5],[],[0]),([6,170,231,61,3,4],[15],[]),([170,407,2,3,4,5],[],[]),([170,2,347,3,7],[1,15,5],[0]),([170,408,2,3,4,5],[],[]),([170,61,2,9,7],[7,0],[0]),([48,231,261,3,4,5],[3],[]),([170,2,329,9,4,5],[],[0]),([274,18,2,335,3,5],[],[]),([170,308,56,3,4,5],[2],[]),([231,261,56,3,4,5],[5],[0]),([18,232,2,335,3,5],[],[]),([339,170,231,3,4,5],[3],[]),([314,261,2,3,4,5],[],[]),([330,170,232,2,9,5],[2],[]),([170,409,2,3,4,5],[],[]),([48,276,231,3,4,5],[3],[]),([276,231,56,3,4,5],[11],[]),([308,232,2,3,4,5],[2],[]),([170,404,2,3,4,5],[13],[]),([276,314,2,3,4,5],[],[]),([300,170,268,3,4,5],[1],[]),([170,231,137,3,4,5],[11],[]),([170,261,56,2,9,5],[],[0]),([276,301,2,3,4,5],[],[]),([317,300,170,3,4,5],[],[0]),([249,170,2,9,3,7],[7],[0]),([249,231,3,7,4],[1,18],[0]),([170,315,2,3,7,4],[],[]),([170,2,3,263,4,5],[],[]),([249,314,231,3,4,5],[3],[0]),([249,301,231,3,4,5],[18],[0]),([18,150,111,56,3,5],[10],[]),([276,231,2,3,7,4],[1],[]),([249,313,231,3,4,5],[],[0]),([204,247,18,3,4,5],[],[]),([410,170,2,3,4,5],[14,13],[]),([231,302,2,3,4,5],[3],[]),([18,150,62,56,9,5],[2],[]),([315,18,261,2,4,5],[],[]),([177,170,231,3,4,5],[11],[]),([279,268,3,7,4],[15,1,19],[0]),([170,337,338,2,3,5],[12],[]),([170,184,231,2,3,4],[15],[]),([170,2,347,9,3,5],[10],[0]),([170,61,268,9,4,5],[],[0]),([170,231,138,3,4,5],[11],[]),([300,170,2,3,4,5],[14,13],[]),([53,170,121,3,4,5],[],[]),([127,170,56,2,3,5],[12],[]),([170,2,358,9,4,5],[2],[0]),([330,170,338,2,4,5],[12],[]),([36,231,232,3,4,5],[3],[]),([231,2,411,3,4,5],[11],[]),([170,412,2,3,7,4],[],[]),([170,2,181,3,7],[15,7],[]),([413,170,2,3,4,5],[],[0]),([54,56,2,236,3,5],[],[]),([312,339,170,3,4,5],[],[0]),([170,414,2,3,4,5],[],[]),([18,415,2,3,4,5],[],[]),([170,400,2,3,7,4],[20],[]),([231,232,2,9,3,5],[7],[0]),([231,416,3,4,5],[1,21,6],[0]),([248,247,0,1,3,7],[],[0]),([314,231,232,2,3,5],[2],[]),([170,2,417,3,4,5],[],[0]),([247,18,111,56,3,5],[2],[]),([231,358,3,4,5],[22,1],[0]),([300,170,301,3,4,5],[5],[]),([102,170,268,3,7,4],[],[]),([279,261,2,3,7,4],[0],[0]),([170,2,335,9,3,5],[10],[0]),([418,0,1,3,4,5],[],[0]),([330,231,2,3,4,5],[3],[]),([170,326,61,2,4,5],[12],[]),([253,313,2,3,4,5],[],[]),([170,2,419,3,4,5],[],[]),([170,420,2,3,4,5],[],[])]
def P_46_5_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [0,1,2,3,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_5_0 : checkNodesBT W_46 G_46 fmask_46 P_46_5_0 autos_46 bk_46_4 5 nd_46_5_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_46_5_0 : ∀ ns ∈ nd_46_5_0, Impossible G_46 5 (nodeValsBT W_46 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_4_ok chk_46_5_0
def nd_46_5_1 : List NodeSpec := [([170,61,268,3,7,4],[],[0]),([300,170,2,9,3,5],[0],[0]),([339,170,268,3,4,5],[3],[]),([170,113,268,3,4,5],[],[]),([18,62,2,303,4,5],[11],[]),([6,170,313,2,3,4],[],[]),([18,62,2,250,9,5],[],[]),([279,232,2,9,3,5],[],[0]),([170,315,2,3,4,5],[],[]),([170,421,353,2,3,4],[15],[]),([422,170,61,3,4,5],[],[]),([307,261,2,3,4,5],[10],[]),([170,301,2,9,3,5],[10],[0]),([170,315,231,61,4,5],[],[]),([170,232,2,335,3,5],[3],[]),([231,261,316,3,4,5],[],[]),([170,39,2,341,4,5],[12],[]),([231,232,2,3,4,5],[2,3],[]),([170,56,268,9,3,5],[],[0]),([48,170,315,3,4,5],[],[]),([279,330,2,3,4,5],[],[]),([248,18,111,2,3,7],[],[0]),([279,261,2,9,4,5],[0],[0]),([261,2,423,3,4,5],[],[]),([330,261,232,2,4,5],[11],[]),([279,268,9,3,4,5],[],[0]),([170,424,2,3,4,5],[],[]),([170,2,425,3,4,5],[],[]),([416,3,4,5],[1,23,8],[0]),([170,314,61,3,4,5],[],[]),([171,18,54,56,3,5],[2],[]),([170,121,231,3,4,5],[3],[]),([279,337,2,3,4,5],[],[]),([274,18,426,2,3,4],[13],[]),([170,352,56,2,3,4],[1],[]),([170,313,56,3,4,5],[2],[0]),([170,353,2,9,3,5],[0],[0]),([170,353,56,2,3,5],[11],[]),([427,170,2,3,4,5],[14,13],[]),([170,306,56,3,4,5],[11],[]),([339,170,2,3,4,5],[],[]),([18,54,234,2,3,7],[2,1],[]),([261,353,2,3,4,5],[0],[0]),([170,231,3,7,4,103],[13],[]),([247,18,111,61,4,5],[10],[0]),([170,324,2,3,7,4],[],[]),([110,170,231,3,4,5],[11],[]),([360,18,336,3,4,5],[],[0]),([18,232,2,428,3,4],[],[0]),([170,429,2,3,4,5],[],[]),([170,121,52,3,4,5],[24],[]),([170,326,2,3,7,4],[],[0]),([170,2,358,3,7,4],[2],[0]),([270,18,54,2,3,5],[],[]),([170,326,2,9,4,5],[2],[0]),([231,261,2,3,7,4],[1],[0]),([231,261,2,3,4,5],[3],[]),([274,18,2,430,3,4],[],[0]),([170,431,2,3,4,5],[],[]),([170,2,3,4,432],[15,25],[0]),([433,170,2,3,4,5],[],[]),([170,231,61,3,4,5],[11],[]),([170,61,335,3,4,5],[],[0]),([170,313,2,3,4,5],[],[]),([170,314,2,3,4,5],[],[]),([249,231,9,3,4,5],[3],[0]),([313,232,2,3,4,5],[2],[0]),([337,231,2,3,4,5],[3],[]),([434,170,2,3,4,5],[],[]),([279,2,329,3,4,5],[3],[]),([170,231,56,3,4,5],[11,2],[]),([170,231,113,3,4,5],[11],[]),([170,315,261,2,4,5],[12],[]),([170,313,2,3,7,4],[],[0]),([348,18,350,3,4,5],[],[0]),([231,232,61,3,4,5],[],[0]),([170,435,2,3,4,5],[],[]),([231,338,2,3,4,5],[3],[]),([170,436,2,3,4,5],[2],[]),([315,231,261,2,4,5],[],[]),([170,261,2,341,4,5],[12],[]),([127,18,62,61,56,5],[],[]),([321,232,2,3,4,5],[2],[]),([36,170,231,3,7,4],[1],[]),([170,185,61,2,4,5],[12],[]),([170,195,56,2,3,5],[12],[]),([261,232,2,9,5],[0,2,11],[0]),([232,326,2,3,4,5],[],[0]),([170,437,2,3,4,5],[],[]),([330,170,261,2,4,5],[12],[]),([170,171,56,3,4,5],[2],[]),([170,332,56,3,4,5],[2],[]),([170,231,2,3,7,4],[1],[]),([170,2,268,9,3,7],[7],[0]),([170,225,2,3,4,5],[2],[]),([170,314,232,2,3,5],[12],[]),([170,262,2,3,4,5],[],[]),([18,62,56,251,4,5],[],[0]),([36,170,301,3,4,5],[],[]),([253,315,2,3,4,5],[],[]),([170,229,2,3,4,5],[],[]),([18,305,62,2,3,4],[],[]),([328,231,61,3,4,5],[],[]),([18,111,56,242,3,5],[7,2],[]),([204,18,308,3,4,5],[],[]),([18,232,2,318,3,4],[],[0]),([281,18,2,341,4,5],[],[]),([170,31,2,318,3,4],[],[]),([296,18,62,2,4,5],[],[]),([170,313,2,9,4,5],[2],[0]),([215,0,2,341,4,5],[],[]),([170,2,341,3,7,4],[],[0]),([231,349,2,3,4,5],[3],[]),([54,113,2,236,3,5],[],[]),([170,285,2,3,4,5],[2],[]),([170,438,2,3,4,5],[],[]),([170,439,2,3,4,5],[],[]),([48,170,313,3,4,5],[],[]),([279,338,2,3,4,5],[],[]),([170,2,341,9,4,5],[2],[0]),([170,130,268,3,4,5],[3],[]),([300,170,56,3,4,5],[5],[]),([170,315,313,2,4,5],[12],[]),([339,170,61,3,4,5],[12],[0]),([170,184,2,268,3,4],[15],[]),([301,261,2,3,4,5],[10],[0]),([170,314,231,56,3,5],[2],[]),([170,234,2,3,7,4],[1],[]),([18,261,2,341,4,5],[],[]),([440,281,2,3,4,5],[],[]),([62,56,2,236,4,5],[],[]),([170,31,2,335,3,5],[3],[]),([231,347,3,4,5],[5,1],[0]),([170,61,56,9,5],[0,2,3],[0]),([127,170,268,3,4,5],[],[]),([279,170,2,9,3,7],[0],[0]),([206,121,18,3,4,5],[],[]),([127,170,61,2,9,5],[10],[]),([170,301,2,3,4,5],[],[]),([127,18,62,113,2,5],[7],[]),([261,2,441,3,4,5],[],[]),([304,18,356,3,4,5],[],[0])]
def P_46_5_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [0,1,2,3,5,7,8,10,11,12,13,14,15,23,24,25]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_5_1 : checkNodesBT W_46 G_46 fmask_46 P_46_5_1 autos_46 bk_46_4 5 nd_46_5_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_46_5_1 : ∀ ns ∈ nd_46_5_1, Impossible G_46 5 (nodeValsBT W_46 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_4_ok chk_46_5_1
def nodes_46_5 : List NodeSpec := nd_46_5_0 ++ nd_46_5_1
def bk_46_5 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_5
set_option maxRecDepth 500000 in
lemma bk_46_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 5 xs.toFinset) bk_46_5 :=
  buildBucketsBT_of_mem (forall_append (mem_46_5_0) mem_46_5_1)
def nd_46_6_0 : List NodeSpec := [([288,0,1,2,3,4,5],[],[]),([34,212,8,1,2,9,5],[2,26,27],[]),([289,0,1,2,3,4,5],[],[]),([213,8,0,37,2,9,5],[27,28],[]),([215,290,0,2,3,4,5],[10,29],[0]),([291,215,0,2,3,4,5],[11,29],[0]),([215,0,2,292,3,4,5],[0,15,29],[0]),([0,1,2,293,3,4,5],[],[]),([0,1,56,112,9,5],[28,31,30],[]),([0,239,2,227,3,4,5],[7,32],[]),([0,66,228,56,2,3,5],[],[]),([127,16,46,61,56,3,5],[3],[0]),([170,121,2,3,4,5],[30,28,3,2,13,14],[0]),([18,245,62,2,3,4,5],[3,14,13],[]),([127,16,46,56,2,3,5],[12],[0]),([127,16,46,113,2,3,5],[12],[0]),([267,170,56,2,3,4,5],[5,13,1],[0]),([294,0,1,2,3,4,5],[],[0]),([204,18,111,2,3,4,5],[2,0],[0]),([226,295,14,2,3,4,5],[24],[]),([143,0,1,56,9,5],[33,2,0],[]),([14,61,2,236,3,4,5],[7],[0]),([248,247,0,1,3,4,5],[],[0]),([0,1,54,2,3,263,5],[34],[0]),([226,1,54,113,2,3,5],[7],[]),([226,1,62,61,2,4,5],[30],[]),([170,198,61,2,3,4,5],[30],[0]),([170,232,2,17,3,4,5],[13,35],[]),([247,0,1,62,61,4,5],[],[0]),([0,1,150,62,56,9,5],[10],[0]),([0,1,111,61,2,7],[36,7,2],[0]),([296,0,1,111,2,4,5],[34],[0]),([0,1,111,61,56,2,5],[38],[0]),([0,1,111,61,56,5],[38,0,7,39,2],[0]),([63,18,150,62,2,4,5],[15,30,0],[]),([0,1,111,2,297,4,5],[37],[0]),([6,170,231,2,3,4],[1,40,15,7],[0]),([0,1,111,2,242,3,7],[7,0,31],[0]),([204,0,1,111,56,3,5],[38],[0]),([204,247,0,1,3,4,5],[],[0]),([270,18,14,2,3,4,5],[],[0]),([53,18,232,2,3,4,5],[15,28],[]),([298,0,1,62,2,4,5],[],[0]),([16,46,2,3,263,4,5],[],[0]),([0,1,62,56,251,4,5],[],[0]),([238,0,1,111,2,3,5],[0,34],[0]),([170,45,61,2,3,4,5],[30],[0]),([127,0,1,2,236,3,5],[41],[0]),([127,18,14,61,56,3,5],[3],[0]),([18,14,225,2,3,4,5],[2],[0]),([170,18,2,3,7,4,299],[13,15],[]),([273,18,56,2,3,4,5],[1],[]),([253,261,2,3,4,5],[7,11,0],[0]),([0,1,258,111,2,3,7],[7,39,0,42],[0]),([14,56,2,236,3,4,5],[],[0]),([18,14,61,56,2,9,5],[3],[0]),([48,18,62,61,4,5],[7,0,3],[]),([18,14,61,56,9,5],[7,43,0,3],[0]),([127,18,14,61,2,9,5],[10],[0]),([247,18,62,2,3,4,5],[2,10],[0]),([127,18,14,56,2,3,5],[44],[0]),([0,1,62,2,263,4,5],[],[0]),([300,170,18,2,3,4,5],[2,3,14,13],[0]),([0,1,111,2,250,3,5],[37],[0]),([18,150,62,2,9,4,5],[0,2,3,45],[0]),([18,54,2,3,7,103],[0,1,46,15,28],[]),([18,258,111,2,3,4,5],[7,17,0],[0]),([18,54,133,56,2,3,5],[1,47,13],[]),([110,18,54,2,3,5],[44,7,2,13],[]),([144,18,54,56,2,3,5],[28,11],[]),([0,1,258,242,3,4,5],[9],[0]),([18,54,2,138,3,5],[7,13,3],[]),([170,56,268,3,4,5],[5,1,11],[0]),([18,54,61,2,3,7],[7,48,0,1],[0]),([170,231,261,2,3,4,5],[11,10,3],[0]),([18,54,61,56,3,5],[7,48,44,0],[0]),([16,46,61,56,9,5],[7,39,0,3],[0]),([18,54,113,61,2,3,5],[7,44],[]),([18,62,2,9,7],[7,0],[]),([0,1,62,2,250,9,5],[],[0]),([18,62,137,2,4,5],[7,13,3],[]),([18,62,56,2,9,5],[7,0],[0]),([102,18,54,2,3,7],[0,47,49,15,28],[]),([170,301,231,2,3,4,5],[5,40],[0]),([18,62,113,56,2,4,5],[7],[0]),([16,46,61,2,9,7],[7,0],[0]),([170,302,2,3,4,5],[7,11,3,13,14],[0]),([18,62,61,2,7,4],[7,0],[0]),([127,18,62,2,4,5],[7,10,13],[0]),([18,62,113,2,4,5],[7,13,11],[0]),([127,16,46,61,2,9,5],[10],[0]),([0,1,111,62,61,56,5],[10],[0]),([18,62,61,2,162,4,5],[30,11],[]),([18,111,62,61,2,4,5],[0,2,3],[0]),([170,231,2,3,7,4],[40,1,15,7,20,13],[0]),([0,1,62,2,303,4,5],[37],[0]),([304,281,18,2,3,4,5],[11,24,3],[0]),([0,1,305,62,2,3,4],[],[0]),([247,18,111,2,3,4,5],[2,10],[0]),([248,18,111,2,3,4,5],[],[0]),([6,18,150,62,2,3,4],[1],[0]),([18,150,111,2,3,4,5],[0,3,17],[0]),([204,0,1,62,56,9,5],[33],[0]),([238,18,62,2,3,4,5],[2,3,13,14],[0]),([18,14,61,2,9,7],[7,0],[0]),([212,8,1,37,2,9,5],[39,50,27,51],[]),([6,18,62,61,2,4],[7,1,0],[]),([18,261,62,2,4,5],[7,11,13],[0]),([0,1,62,225,2,4,5],[],[0]),([102,170,18,2,3,7,4],[28,15,13],[]),([170,18,2,3,7,4,103],[15,28,13],[0]),([170,306,2,3,4,5],[15,52,10],[0]),([170,2,3,7,4,152],[15,7,1],[0]),([249,231,3,4,5],[1,22,18],[0]),([177,170,18,2,3,4,5],[24,11],[]),([170,18,104,2,3,4,5],[24,11,2,13],[]),([170,307,18,2,3,4,5],[24,12],[]),([36,170,232,2,3,4,5],[3,11],[0]),([170,144,56,2,3,4,5],[28],[0]),([18,308,62,2,3,4,5],[30],[0]),([309,18,232,2,3,4,5],[15],[]),([279,170,2,9,3,4,5],[7,11,0,53],[0]),([18,310,232,2,3,4,5],[15,28],[]),([261,232,2,3,4,5],[7,0,11],[0]),([300,18,232,2,3,4,5],[54,15],[0]),([18,232,2,311,3,4,5],[3,2,11],[0]),([18,111,2,242,3,4,5],[7,0,2,17],[0]),([18,301,232,2,3,4,5],[2,28,55],[0]),([18,14,2,3,263,4,5],[],[0]),([312,18,261,2,3,4,5],[15,0,30,3],[0]),([18,111,2,3,7],[7,0,2],[0]),([18,313,261,2,3,4,5],[10,30,56],[0]),([177,18,54,2,3,4,5],[2,13],[0]),([170,18,231,2,3,7,4],[15,28],[0]),([48,170,18,231,3,4,5],[3,11],[]),([170,18,231,61,3,4,5],[11,30],[]),([14,113,2,236,3,4,5],[7],[0]),([170,314,18,2,3,4,5],[2,24],[0]),([170,18,301,2,3,4,5],[24,12],[]),([170,315,18,2,3,4,5],[10,24],[0]),([170,18,313,2,3,4,5],[24,12],[]),([127,0,1,62,61,56,5],[38],[0]),([170,261,2,316,3,4,5],[11,10,3],[0]),([18,62,2,250,3,4,5],[2],[0]),([204,276,18,2,3,4,5],[30,11],[0]),([18,231,232,2,3,4,5],[11,28,3],[0]),([170,314,231,2,3,4,5],[40,11,3],[0]),([317,170,232,2,3,4,5],[3],[0]),([18,62,2,251,4,5],[0,1,11],[0]),([170,18,2,268,3,7,4],[15,28,13],[0]),([170,56,2,9,3,5],[7,5,0],[0]),([18,62,61,56,4,5],[7,0,3],[0]),([170,18,2,318,3,4],[0,1,15],[0]),([170,130,2,3,4,5],[28,30,3,10,13,14],[0]),([170,18,56,268,3,4,5],[11,28],[]),([170,261,56,2,3,4,5],[5,11],[0]),([170,18,61,268,3,4,5],[11,30,0],[]),([102,170,2,3,4,5],[20,0,1,11],[0]),([36,170,18,231,3,4,5],[3,11],[]),([279,232,2,3,4,5],[11,5,57],[0]),([102,170,2,3,7,4],[20,0,15],[0]),([274,18,2,319,3,4,5],[15,3,24],[0]),([170,2,3,7,4,299],[20,0,1],[0]),([170,2,9,3,7],[0,7],[0]),([0,1,62,2,320,4,5],[58],[0]),([53,170,232,2,3,4,5],[13,15],[0]),([170,104,2,3,4,5],[5,0,1,11],[0]),([170,232,2,9,3,5],[7,0,11],[0]),([170,321,2,3,4,5],[0,15,2,3],[0]),([285,18,14,2,3,4,5],[2],[0]),([204,18,62,56,3,4,5],[10],[0]),([170,137,2,3,4,5],[7,3,11,13,14],[0]),([20,18,62,2,4,5],[59,13,11,2],[0]),([253,231,2,3,4,5],[15,40,5],[0]),([110,170,2,3,4,5],[5,7,11,14,13],[0]),([322,266,18,2,3,4,5],[1,11],[]),([18,111,61,2,4,5],[7,0,2],[0]),([170,301,56,2,3,4,5],[5,11],[0]),([170,2,323,3,4,5],[5,10,13,14],[0]),([170,324,18,2,3,4,5],[24,12],[]),([18,325,62,2,3,4,5],[3,14,13],[]),([36,170,2,3,7,4],[1,7,0,15],[0]),([278,14,3,4,5],[1,28,30],[]),([317,18,232,2,3,4,5],[15,28,3],[0]),([170,326,2,3,4,5],[15,60,2],[0]),([65,18,54,56,2,3,5],[13,3,28],[0]),([170,2,138,3,4,5],[5,7,11,13,14],[0]),([170,61,2,9,4,5],[7,0,3],[0]),([198,18,62,61,2,4,5],[30,11],[]),([48,170,61,3,4,5],[7,3,0],[0]),([121,18,14,52,3,4,5],[24],[0]),([170,61,56,3,4,5],[7,5,0,3],[0]),([127,170,61,2,3,4,5],[7,3],[0]),([170,61,268,3,4,5],[1,61,11],[0]),([18,54,56,2,17,3,5],[13],[]),([170,133,56,2,3,4,5],[1,20,13],[]),([274,18,327,2,3,4,5],[15,24],[]),([127,170,2,3,4,5],[7,11,13,14],[0]),([170,113,61,2,3,4,5],[7,5],[0]),([18,14,234,2,3,7,4],[2,1],[0]),([170,2,3,4,299,5],[20,0,3],[0]),([170,313,61,2,3,4,5],[11],[0]),([18,232,52,2,3,4,5],[1],[]),([300,170,2,3,4,5],[54,13,14,10,3],[0]),([328,170,61,2,3,4,5],[3,10,11],[0]),([170,2,329,3,4,5],[62,2,13,14,3],[0]),([330,170,232,2,3,4,5],[7,11],[0]),([331,170,61,2,3,4,5],[1,0,11],[0]),([170,240,56,2,3,4,5],[13,15],[]),([276,170,2,3,7,4],[15,7,0,1],[0]),([170,126,2,3,4,5],[7,15,13,3],[0]),([170,171,2,3,4,5],[0,1,2,11],[0]),([170,332,3,4,5],[0,15,16],[0]),([333,170,2,3,7,4],[15,0,63,1],[0]),([170,261,2,268,3,4,5],[3,10,11],[0]),([170,231,2,3,4,5],[1,11,10,2],[0]),([170,334,3,4,5],[0,1,11],[]),([18,261,2,268,3,4,5],[0,15,30],[0]),([170,113,2,3,4,5],[7,11,13,14,5],[0]),([279,261,2,3,4,5],[15,0,3,60],[0]),([170,332,2,3,4,5],[0,1,16,11],[0]),([170,2,335,3,4,5],[5,64,10,13,14],[0]),([330,170,2,3,4,5],[7,3,13,14],[0]),([16,46,225,2,3,4,5],[2],[0]),([300,170,232,2,3,4,5],[15,2,3],[0]),([170,39,2,268,3,4,5],[0,3,15,24],[0]),([170,301,232,2,3,4,5],[5],[0]),([247,0,1,111,61,4,5],[10],[0]),([18,54,61,56,2,3,5],[44,7],[0]),([145,18,61,2,4,5],[7,0],[]),([276,231,2,3,4,5],[15,65,3],[0]),([170,261,2,9,4,5],[7,0,11],[0]),([281,18,2,336,3,4,5],[0,15,3,24],[0]),([170,337,261,2,3,4,5],[7,11],[0]),([170,338,261,2,3,4,5],[7],[0]),([170,338,2,3,4,5],[7,3,13,14],[0]),([339,170,261,2,3,4,5],[11,10,3],[0]),([249,170,2,3,7,4],[1,66,15,7,20,13],[0]),([339,170,2,3,4,5],[67,2,13,14,3],[0]),([53,274,18,2,3,4,5],[15,24],[]),([170,61,56,2,3,4,5],[7,5,3],[0]),([170,232,2,311,3,4,5],[11,2,3],[0]),([127,18,62,61,2,4,5],[7],[0]),([170,56,2,17,3,4,5],[13,35],[]),([312,170,261,2,3,4,5],[3],[0]),([177,18,62,2,4,5],[59,13,10,11],[0]),([170,313,261,2,3,4,5],[3],[0]),([170,61,2,329,3,4,5],[11,3,10],[0]),([170,261,232,2,3,4,5],[7,11],[0]),([153,54,2,3,4,5],[0,1,11],[])]
def P_46_6_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [0,1,2,3,5,7,9,10,11,12,13,14,15,16,17,18,20,22,24,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_6_0 : checkNodesBT W_46 G_46 fmask_46 P_46_6_0 autos_46 bk_46_5 6 nd_46_6_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_46_6_0 : ∀ ns ∈ nd_46_6_0, Impossible G_46 6 (nodeValsBT W_46 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_5_ok chk_46_6_0
def nd_46_6_1 : List NodeSpec := [([339,170,18,2,3,4,5],[10,3],[0]),([170,338,232,2,3,4,5],[7],[0]),([102,170,18,2,3,4,5],[13,24,11],[]),([170,308,2,3,4,5],[15,68,2],[0]),([170,231,2,3,7,4,5],[15,13,20,1],[0]),([48,276,170,2,3,4,5],[3,11],[0]),([170,231,2,9,3,4,5],[7,11,3],[0]),([266,18,340,2,3,4,5],[1],[]),([48,170,231,3,4,5],[1,40,11],[0]),([170,39,231,2,3,4,5],[3,24,10,11],[0]),([127,0,1,62,56,2,5],[],[0]),([276,170,56,2,3,4,5],[11,5],[0]),([170,231,56,2,3,4,5],[5,11,3],[0]),([170,61,2,162,3,4,5],[24,10,3],[]),([170,2,181,3,4,5],[7,1,11],[0]),([170,232,61,2,3,4,5],[11,3],[0]),([170,2,131,3,4],[30,28,3,13],[]),([36,253,170,2,3,4,5],[3,11],[0]),([170,232,52,2,3,4,5],[13,1],[]),([36,170,231,3,4,5],[1,65,11],[0]),([36,18,54,56,3,5],[7,3,0,2],[]),([170,231,61,3,4,5],[65,1,11,0],[0]),([170,18,2,341,3,4,5],[10,24,61],[0]),([170,61,2,3,7,4],[7,0,1,15],[0]),([170,65,56,2,3,4,5],[13,5,14],[0]),([170,342,231,2,3,4,5],[15,13],[]),([0,66,118,56,2,9,5],[10,50],[]),([276,18,62,61,2,4,5],[3,10,11,30],[0]),([343,170,56,2,3,4,5],[5,1],[0]),([170,184,2,3,4],[28,13,30,15],[0]),([344,0,1,2,3,4,5],[69],[]),([345,2,3,4,5],[30,28,3,13],[]),([170,309,232,2,3,4,5],[15,13],[]),([170,346,231,2,3,4,5],[15,1,13],[]),([170,231,56,3,4,5],[40,1,11,5],[0]),([18,54,113,2,3,5],[7,13,44],[0]),([170,301,2,3,4,5],[40,5,10,13,14],[0]),([276,232,2,3,4,5],[7,11,0],[0]),([229,0,1,2,3,4,5],[],[]),([170,113,56,2,3,4,5],[7,5],[0]),([170,315,2,3,4,5],[65,2,13,14,3,11],[0]),([170,314,2,3,4,5],[40,10,13,14,3,11],[0]),([127,18,14,113,2,3,5],[7,44],[0]),([18,261,2,316,3,4,5],[3,10,11],[0]),([238,0,1,62,2,9,5],[0],[0]),([170,313,2,3,4,5],[2,13,14,65],[0]),([170,261,2,3,7,4],[7,0,15,1],[0]),([249,170,2,9,3,4,5],[7,3],[0]),([170,313,231,2,3,4,5],[65],[0]),([170,2,347,3,4,5],[5,11,1,10],[0]),([348,274,18,2,3,4,5],[11,24,3],[0]),([339,18,261,2,3,4,5],[67],[0]),([170,2,341,3,4,5],[1,61,2],[0]),([279,170,2,3,7,4],[15,57,13,1,7,20],[0]),([170,349,2,3,4,5],[7,11,3,13,14],[0]),([0,1,111,2,251,4,5],[58,0],[0]),([248,0,1,111,2,3,7],[],[0]),([276,18,150,2,3,4,5],[3,15,30,0],[]),([36,170,56,3,4,5],[5,7,0],[0]),([170,18,2,323,3,4,5],[13,24,14],[]),([274,18,350,2,3,4,5],[70,2,24],[0]),([170,185,2,3,4,5],[7,11,13,14],[0]),([48,18,150,62,3,4,5],[3],[]),([170,2,3,351,4,5],[35,0,3,2],[0]),([170,231,232,2,3,4,5],[11,2,3],[0]),([18,54,113,56,2,3,5],[7,44],[0]),([231,261,2,3,4,5],[65,15,3,0],[0]),([45,18,54,56,2,3,5],[28,11],[]),([18,258,62,2,3,4,5],[11,30,14,13],[0]),([171,18,54,2,3,4,5],[2,13],[0]),([18,54,2,181,3,5],[7,13,3],[]),([45,261,2,3,4,5],[7,11,0],[0]),([170,315,231,2,3,4,5],[65,11,3],[0]),([279,268,3,4,5],[1,11,71,19],[0]),([170,352,2,3,4],[0,15,1,72],[0]),([18,231,261,2,3,4,5],[11,30,3],[0]),([246,18,62,2,3,4,5],[],[0]),([170,353,2,3,4,5],[15,57,10,13],[0]),([170,337,2,3,4,5],[7,3,13,14],[0]),([247,0,1,111,2,3,7],[2,7],[0]),([274,45,2,3,4,5],[28,30,11,73],[]),([18,62,61,56,2,4,5],[7,3],[0]),([170,31,52,2,3,4,5],[13,1],[0]),([6,170,261,2,3,4],[15,7,1],[0]),([18,354,62,2,3,4,5],[11],[]),([53,170,31,2,3,4,5],[24,3,15],[0]),([204,18,62,2,9,4,5],[2,0],[0]),([177,170,2,3,4,5],[35,1,13,11,2],[0]),([171,18,14,56,3,4,5],[2,11],[0]),([206,31,18,2,3,4,5],[1,13],[0]),([170,232,2,268,3,4,5],[3,2,11],[0]),([226,1,54,56,2,3,5],[28],[]),([170,266,2,3,4,5],[1,28,30],[]),([18,14,2,181,3,7],[1,7],[0]),([279,170,56,2,3,4,5],[5,1,11],[0]),([18,54,2,3,7,152],[7,15,74,47,13,1],[0]),([262,18,14,2,3,4,5],[14],[0]),([170,31,231,2,3,4,5],[3,24,2,11],[0]),([18,264,2,3,7,4],[1,0,75,15],[]),([48,170,261,2,3,4,5],[3,11],[0]),([281,45,2,3,4,5],[28,11,0],[0]),([18,185,14,61,2,4,5],[12],[0]),([266,58,3,4,5],[1,28,30],[]),([0,1,150,111,56,3,5],[10],[0]),([170,31,2,268,3,4,5],[3,2,15,24],[0]),([274,18,52,2,3,4,5],[1],[]),([170,310,232,2,3,4,5],[15,20,13],[]),([355,274,18,2,3,4,5],[76,15],[0]),([102,18,54,2,3,5],[0,1,11],[]),([231,232,2,3,4,5],[40,15,3],[0]),([170,2,3,7,4,103],[20,0,1,15],[0]),([281,18,356,2,3,4,5],[77,10,24],[0]),([170,357,2,3,4,5],[0,15,3],[0]),([53,121,18,14,3,4,5],[24],[0]),([170,195,2,3,4,5],[7,11,13,14],[0]),([18,150,62,56,3,4,5],[10,3],[0]),([18,54,104,2,3,5],[0,1,11],[]),([253,170,61,2,3,4,5],[11,3],[0]),([170,18,231,56,3,4,5],[11,28],[]),([170,2,358,3,4,5],[1,11,2,78],[0]),([170,231,61,2,3,4,5],[11,3,10],[0]),([204,63,18,62,2,4,5],[30,11,10],[]),([45,18,54,2,3,7],[7,15,79,47,13],[]),([45,232,2,3,4,5],[7,11,5],[]),([170,45,2,3,7,4],[15,7,20,13],[]),([226,1,62,113,2,4,5],[7],[]),([45,18,62,61,2,4,5],[11,30],[]),([296,0,1,62,2,4,5],[37],[0]),([170,307,2,3,4,5],[80,3,10,13,14],[0]),([20,170,2,3,4,5],[35,13,2,11,3],[0]),([170,324,2,3,4,5],[1,81,2],[0]),([279,170,61,2,3,4,5],[0,11,1],[0]),([16,46,61,56,2,9,5],[3],[0]),([170,231,2,17,3,4,5],[1,13,35,15],[0]),([6,170,61,2,3,4],[1,7,15],[0]),([18,111,62,56,2,3,5],[10,2],[0]),([18,150,62,2,3,4,252],[1,13],[]),([0,1,111,61,242,4,5],[7,0],[0]),([359,215,0,2,3,4,5],[29,11],[0]),([170,45,56,2,3,4,5],[28],[0]),([170,2,202,3,4,5],[7,1,11],[]),([18,54,61,2,9,5],[7,48,0],[]),([18,62,113,61,2,4,5],[7],[0]),([170,18,2,329,3,4,5],[24,12],[]),([18,195,14,56,2,3,5],[11],[0]),([0,1,111,56,242,3,5],[7,2],[0]),([18,62,56,2,17,4,5],[13,59],[]),([170,2,268,3,7,4],[1,64,15,7,20,13],[0]),([18,232,2,268,3,4,5],[15,28],[0]),([18,62,2,202,4,5],[7,13,11],[]),([45,286,3,4,5],[28,3,11,30],[]),([360,281,18,2,3,4,5],[82],[0]),([170,18,2,335,3,4,5],[2,24,64,13,14],[0]),([18,54,2,58,3,7],[7,1,83,13,47],[]),([36,18,54,2,3,7],[7,1,0,84],[]),([170,2,58,3,7,4],[15,7,13,20],[0]),([18,111,56,2,3,5],[7,0,2],[0]),([18,229,14,2,3,4,5],[3],[0]),([170,2,268,9,3,4,5],[7,3],[0]),([127,0,1,62,113,2,5],[7],[0]),([247,0,1,111,56,3,5],[2],[0]),([361,274,18,2,3,4,5],[15],[])]
def P_46_6_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [0,1,2,3,5,7,10,11,12,13,14,15,19,20,24,28,29,30,35,37,40,44,47,48,50,57,58,59,61,64,65,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_6_1 : checkNodesBT W_46 G_46 fmask_46 P_46_6_1 autos_46 bk_46_5 6 nd_46_6_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_46_6_1 : ∀ ns ∈ nd_46_6_1, Impossible G_46 6 (nodeValsBT W_46 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_5_ok chk_46_6_1
def nodes_46_6 : List NodeSpec := nd_46_6_0 ++ nd_46_6_1
def bk_46_6 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_6
set_option maxRecDepth 500000 in
lemma bk_46_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 6 xs.toFinset) bk_46_6 :=
  buildBucketsBT_of_mem (forall_append (mem_46_6_0) mem_46_6_1)
def nd_46_7_0 : List NodeSpec := [([210,0,1,2,3,4,5],[87,88,3,24,29],[]),([53,84,11,1,2,3,4,5],[15,29],[]),([84,11,1,52,2,3,4,5],[89,2,29],[]),([53,121,11,0,1,3,4,5],[29],[]),([124,8,0,1,2,9,5],[32,92,93,27,90],[2]),([92,211,0,1,2,3,4,5],[24,96,95,34],[0,1]),([211,0,1,93,2,3,4,5],[97,39,29,34,95],[]),([34,8,0,1,56,2,9,5],[27,90,50,92,2,98],[]),([34,8,11,1,2,9,5],[0,27,32,92,2,51],[0]),([34,212,8,1,2,3,4,5],[2,26,29],[0]),([34,211,0,1,2,3,4,5],[34,95],[0]),([34,0,1,2,9,7],[0,39,33],[]),([34,11,0,1,2,9,5],[27,100,33,41],[]),([8,0,1,37,56,2,9,5],[27,50,101,28,2],[0]),([213,8,0,37,2,3,4,5],[29,24],[0]),([8,0,1,97,2,9,5],[27,90,91,50],[]),([8,0,1,97,56,2,3,5],[27,90],[]),([8,11,1,37,2,9,5],[0,27,2,32,92,51,28],[0]),([214,0,1,2,3,4,5],[27,30,11,24,85,86],[]),([26,8,1,2,9,5],[39,87,102,27,10,50],[2]),([215,0,2,3,4,5],[0,27],[0]),([53,121,0,1,3,4,5],[50,69,33,30,24],[]),([16,0,66,56,2,9,5],[7,50,28,10,0,103],[0]),([16,0,216,2,3,7,4],[28,36,104,2],[]),([217,16,0,56,2,3,4,5],[34],[]),([18,11,1,61,2,9,5],[39,30,33,105],[]),([16,0,1,61,56,9,5],[7,39,33,103,0,104,3,43,106],[0]),([204,18,62,2,3,4,5],[1,0,11,30,2],[0]),([127,16,0,1,61,56,3,5],[3,26,34],[0]),([218,0,1,56,2,3,4,5],[2,41,26],[]),([127,16,0,1,56,2,3,5],[107,34],[0]),([0,1,56,2,219,3,4,5],[1,34,13],[]),([36,0,1,54,2,3,7],[1,0,84],[0]),([0,1,61,2,220,3,4,5],[41,10],[]),([16,1,113,2,221,3,4,5],[34,29],[]),([0,1,2,222,3,4,5],[7,108,85,86,26],[]),([16,0,42,61,2,9,5],[7,33,92,31,36,48],[]),([177,0,1,54,2,3,4,5],[109,34,2,110,13],[0]),([18,14,2,9,3,7],[0,7],[0]),([16,223,0,66,2,3,4,5],[50,24],[]),([0,1,56,2,224,3,4,5],[34,104],[]),([16,0,1,225,2,3,4,5],[94,34,24,2],[0]),([226,1,14,2,3,4,5],[27,111,30,24,34,112],[]),([16,0,116,2,227,3,4,5],[32,7,113,24],[0]),([6,0,66,118,2,3,4],[0,31,114,32],[]),([18,54,2,3,7,5],[0,2,115,15,28],[0]),([0,66,118,2,9,4,5],[0,28,41,50],[0]),([48,0,66,118,2,3,4,5],[32,31],[]),([31,0,1,52,180,3,4,5],[24,9,109,34],[]),([0,66,228,2,3,4,5],[0,28,50],[0]),([229,11,0,1,2,3,4,5],[116,29],[]),([0,66,230,2,3,4,5],[28,10,91],[]),([106,11,0,1,2,3,4,5],[117,29],[]),([127,16,0,1,113,2,3,5],[7,107,104,34],[0]),([102,16,46,2,3,7,4],[0,89,118,1],[0]),([0,1,62,61,2,7,4],[36,119,7,2,104],[0]),([106,0,42,2,3,4,5],[36,1,2,3,24],[]),([16,46,2,3,7,4,103],[1,0,120],[0]),([177,26,0,1,2,3,4,5],[24,109,34],[]),([177,16,46,2,3,4,5],[121,89,13,2],[0]),([16,46,2,9,3,7],[0,7],[0]),([170,231,2,3,4,5],[15,1,65,40,13],[0]),([45,31,14,2,3,4,5],[28,11,30,1],[0]),([16,46,137,2,3,4,5],[7,3,13,14],[0]),([18,14,2,131,3,4],[30,3,28],[0]),([16,46,104,2,3,4,5],[0,1],[0]),([18,232,2,3,4,5],[7,15,2],[0]),([36,18,54,2,3,4,5],[7,3,84,0,14],[0]),([16,46,56,2,9,3,5],[7,2,123,0],[0]),([48,16,46,61,3,4,5],[7,3,0],[0]),([34,0,1,56,2,9,5],[28,7,0,124,33],[]),([16,46,133,56,2,3,4,5],[1,125,13],[0]),([6,16,46,61,2,3,4],[1,7,126],[0]),([18,54,2,58,3,4,5],[7,1,83],[0]),([16,46,61,56,2,3,4,5],[7,123,3],[0]),([16,0,1,61,56,2,9,5],[33,3,26,104],[0]),([18,14,113,56,2,3,4,5],[7,44],[0]),([16,46,56,2,17,3,4,5],[13,121],[0]),([16,46,61,56,3,4,5],[7,39,123,0,3],[0]),([18,229,0,1,2,3,4,5],[24,3],[0]),([20,18,14,2,3,4,5],[7,13,59,3],[0]),([177,0,1,50,2,3,4,5],[34,109],[]),([0,1,233,2,3,4,5],[36,1,24,12],[]),([0,66,50,2,9,5],[7,36,28,127,50],[]),([18,14,104,2,3,4,5],[0,128,3,11,24],[0]),([53,11,0,1,50,2,3,5],[15,29],[]),([63,18,62,2,4,5],[7,15,0],[0]),([18,0,1,234,2,3,7,4],[15,27,28,1],[0]),([0,1,38,56,2,9,5],[7,31,33,0,104],[]),([102,18,14,2,3,4,5],[0,1,129,11,24],[0]),([0,42,38,2,9,5],[7,31,36,130,33],[]),([18,62,2,17,4,5],[0,7,15,131,1],[0]),([0,1,51,3,7,4,103],[32,89,27],[]),([170,47,2,3,4,5],[7,15],[]),([102,18,0,1,2,3,7,4],[99,109,13],[]),([0,1,14,61,56,9,5],[43,132,39,33,0,103,3,104,7,106],[0]),([0,1,38,2,9,7],[36,7,33],[]),([18,0,1,2,3,7,4,103],[15,28,13,27],[]),([0,1,62,113,56,2,4,5],[104,7],[0]),([177,18,0,1,2,3,4,5],[24,109,34,13],[]),([53,31,0,1,2,3,4,5],[38,24,34,15],[0]),([31,0,1,52,2,3,4,5],[9,85,34],[]),([0,1,14,61,2,9,7],[36,7,103,33,132,0],[0]),([226,1,14,113,2,3,4,5],[34,133,7,12],[0]),([143,0,1,56,3,4,5],[26,134,34,0,2],[0]),([177,47,0,1,2,3,4,5],[34,109],[]),([0,1,2,235,3,4,5],[103,34,12,94,134],[]),([0,1,113,2,236,3,4,5],[7],[0]),([237,0,1,2,3,7,4],[15,135,136,137],[]),([238,0,1,62,2,3,4,5],[2,3,33,13,14],[0]),([0,116,239,2,3,4,5],[7,24,32,31,10,138],[0]),([102,0,1,54,2,3,5],[0,1],[0]),([18,0,1,61,2,9,7],[7,39,139,103,33],[0]),([102,0,1,54,2,3,7],[0,1,89,49],[0]),([0,1,62,61,56,4,5],[119,0,7,39,104,3],[0]),([0,1,54,104,2,3,5],[0,1],[0]),([105,1,54,2,3,4,5],[7,89,3],[]),([44,14,58,3,4,5],[28,3,30],[0]),([0,1,54,56,2,17,3,5],[13],[0]),([110,0,1,54,2,3,5],[140,7,39,2,13,141,94],[0]),([170,240,2,3,4,5],[0,15,1,142],[0]),([127,18,0,1,56,2,3,5],[143,34],[0]),([0,1,54,113,56,2,3,5],[26,140,2,31,7],[0,3]),([34,11,1,2,9,5],[39,100,27,0,144,33],[]),([241,0,1,2,3,4,5],[27,30,11,24,85,86],[]),([36,0,1,54,56,3,5],[3,141,122,0,7,2],[0]),([0,1,54,61,2,9,5],[48,39,0,33,26],[0]),([110,16,46,2,3,4,5],[123,7,39,14,13],[0]),([0,1,111,2,242,3,4,5],[7,0,31,38,34,42],[0]),([212,8,1,37,2,3,4,5],[39,50,29,145],[0]),([18,14,113,2,3,4,5],[7,111,13,14,11,44],[0]),([226,1,14,56,2,3,4,5],[34,28],[0]),([16,0,66,2,243,4,5],[28,36,122,26],[]),([127,0,1,14,56,2,3,5],[26,140,33],[0]),([0,1,54,61,56,2,3,5],[140,26,141],[0]),([0,1,54,113,61,2,3,5],[26,7,140],[0]),([178,244,2,3,4,5],[33,30,3],[]),([177,0,1,62,2,4,5],[13,146,89,10],[0]),([0,1,62,2,9,7],[0,31,132,33],[0]),([0,1,245,62,2,3,4,5],[3,14,13],[0]),([0,1,62,56,2,9,5],[7,31,0,33,104],[0]),([246,0,1,62,2,3,4,5],[34],[0]),([0,1,54,61,56,3,5],[48,140,39,0,141,26],[0]),([18,62,61,2,4,5],[0,7,1,147,11],[0]),([6,0,1,62,61,2,4],[1,119,0,7],[0]),([16,46,113,56,2,3,4,5],[7,123],[0]),([0,1,14,61,56,2,9,5],[33,3,26,104,41],[0]),([0,1,62,61,56,2,4,5],[104,3,148],[0]),([127,0,1,62,61,2,4,5],[104,119,10],[0]),([170,2,3,7,4,5],[0,2,149,15,1],[0]),([0,66,118,56,2,3,4,5],[50,10,24,31],[0]),([0,1,62,113,61,2,4,5],[104,3,10,7,119],[0,3]),([145,0,1,61,2,4,5],[0,119,10,104],[0]),([0,1,111,62,56,2,3,5],[10,2],[0]),([0,1,111,62,61,2,4,5],[0,2,3],[0]),([247,0,1,62,2,3,4,5],[34,2,10],[0]),([0,1,62,113,2,4,5],[111,150,119,13,7,104],[0,3]),([0,1,111,2,3,7],[0,31],[0]),([0,1,150,111,2,3,4,5],[34,3,0,2,42],[0]),([0,1,2,112,9,4,5],[7,103,151],[0]),([16,223,0,116,2,3,4,5],[32,24],[]),([0,1,111,56,2,3,5],[2,38,0,31,152],[0]),([177,16,0,42,2,3,4,5],[33],[]),([247,0,1,111,2,3,4,5],[2,10,38,34],[0]),([248,0,1,111,2,3,4,5],[34,38],[0]),([249,170,2,3,4,5],[1,11,78,66],[0]),([102,18,0,1,2,3,4,5],[13,99,109],[]),([204,0,1,62,56,3,4,5],[104,10,34],[0]),([53,31,18,14,2,3,4,5],[24,3,15],[0]),([204,0,1,111,2,3,4,5],[38,2,34,0],[0]),([6,18,14,61,2,3,4],[7,1],[0]),([0,1,62,2,250,3,4,5],[104,2,34],[0]),([48,18,62,2,3,4,5],[7,1,10],[0]),([0,1,62,2,251,4,5],[1,0],[0]),([6,0,1,150,62,2,3,4],[1,33],[0]),([0,1,56,2,220,3,4,5],[41,31],[]),([48,0,1,150,62,3,4,5],[3,10],[0]),([0,1,150,62,56,3,4,5],[10,3,33],[0]),([171,31,0,1,2,3,4,5],[109,34],[]),([0,1,150,62,2,3,4,252],[1,13,34],[0]),([0,1,14,225,2,3,4,5],[34,2,109,110],[0]),([0,1,59,104,3,4,5],[32,13,94],[]),([36,16,46,2,3,7,4],[1,0,7],[0]),([253,170,2,3,4,5],[15,2,7,3],[0]),([0,1,254,2,3,4,5],[0,1],[]),([229,0,1,2,3,4,5],[153,154,29,24,11],[]),([0,1,54,133,56,2,3,5],[1,13,155],[0]),([0,1,50,61,2,9,5],[7,39,36,33,26],[]),([18,0,1,225,2,3,4,5],[11,24,29,2],[0]),([143,0,1,2,9,4,5],[103,134,33,41,156,151],[0]),([255,18,2,3,4,5],[30,13,28,12],[]),([170,44,2,3,4,5],[28,30,1,15,13,157],[]),([0,1,2,256,3,4,5],[158,9,11],[]),([18,0,1,61,56,2,9,5],[33,3,104,28],[0]),([211,0,1,37,2,3,4,5],[34,95,29],[]),([18,0,1,61,56,9,5],[7,39,33,103,0,3,104,106],[0]),([127,0,1,14,113,2,3,5],[26,33,7,140],[0]),([6,143,0,1,2,3,4],[103,1,134,2,33],[]),([127,18,0,1,61,2,9,5],[26,33,10],[0]),([127,18,0,1,113,2,3,5],[7,34,143],[0]),([0,1,2,257,3,4,5],[103,11,7],[]),([218,0,1,113,2,3,4,5],[41,104,26,12],[]),([177,18,11,1,2,3,4,5],[89],[]),([45,18,54,2,3,4,5],[7,15,79],[0]),([0,1,258,111,2,3,4,5],[7,39,0,38,42,34],[0]),([259,0,1,2,3,4,5],[160,161,15],[]),([18,8,42,2,9,5],[7,92,162,163,32],[]),([177,64,0,1,2,3,4,5],[24,109,34],[]),([260,8,1,2,3,4,5],[27,90,91],[]),([0,1,62,56,2,17,4,5],[13,146,99],[0]),([127,16,46,2,3,4,5],[7,39,13,14],[0]),([0,1,56,2,236,3,4,5],[41,104],[0]),([102,18,14,2,3,7,4],[0,47,15,28],[0]),([170,2,3,7,4],[2,0,149],[0]),([48,18,14,61,3,4,5],[7,3,0],[0]),([16,46,113,61,2,3,4,5],[7,123],[0]),([151,14,2,3,4,5],[30,3,28],[0]),([153,14,2,3,4,5],[0,1,11],[0]),([18,0,1,104,2,3,4,5],[24,11,13,2],[]),([18,14,137,2,3,4,5],[7,3,13,14],[0]),([16,0,1,61,2,9,7],[7,36,103,33],[0]),([18,14,56,2,17,3,4,5],[13,59],[0]),([18,11,1,52,2,3,4,5],[89,2,29,31,28],[]),([16,46,61,2,9,4,5],[7,39,0,3],[0]),([18,14,133,56,2,3,4,5],[1,47,13],[0]),([204,0,1,62,2,9,4,5],[0,2,33],[0]),([18,14,61,2,3,7,4],[7,0,1],[0]),([170,261,2,3,4,5],[0,15,7,164,3],[0]),([18,14,61,56,2,3,4,5],[7,44,3],[0]),([18,14,61,56,3,4,5],[7,165,44,0,3],[0]),([48,171,18,0,1,3,4,5],[1,33],[]),([127,18,14,61,2,3,4,5],[7,3],[0]),([18,14,113,61,2,3,4,5],[7,44],[0]),([0,1,54,61,2,3,7],[36,48,1],[0]),([144,18,14,56,2,3,4,5],[28,11],[0]),([45,184,0,1,2,3,4],[28,30,166],[]),([262,18,0,1,2,3,4,5],[24,14],[0]),([16,46,113,2,3,4,5],[7,39,13,14,123],[0]),([170,39,2,3,4,5],[28,15,0,30,3],[0]),([198,18,14,61,2,3,4,5],[30,11],[0]),([101,34,2,3,4,5],[0,28,10],[]),([18,14,2,3,7,4,103],[1,0,167,15,28],[0]),([31,18,14,52,2,3,4,5],[1,13,2],[0]),([18,8,1,56,2,9,5],[39,27,50,0,103],[]),([18,14,61,2,9,4,5],[7,156,0,3],[0]),([45,39,14,2,3,4,5],[28,11,1,30,0],[0]),([121,65,0,1,2,3,4,5],[69,34,168,14],[0]),([119,0,1,2,3,7,5],[7,28,33,86],[]),([18,0,1,2,3,263,4,5],[24,33,109],[0]),([18,54,2,3,7],[2,7,0],[0])]
def P_46_7_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [0,1,2,3,7,9,10,11,12,13,14,15,24,26,27,28,29,30,31,32,33,34,36,38,39,40,41,42,43,44,47,48,49,50,51,59,65,66,69,78,79,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,160,161,162,163,164,165,166,167,168]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_7_0 : checkNodesBT W_46 G_46 fmask_46 P_46_7_0 autos_46 bk_46_6 7 nd_46_7_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_46_7_0 : ∀ ns ∈ nd_46_7_0, Impossible G_46 7 (nodeValsBT W_46 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_6_ok chk_46_7_0
def nd_46_7_1 : List NodeSpec := [([0,1,264,2,3,7,4],[0,1,169],[0]),([18,54,2,17,3,4,5],[7,13,170,115,3],[0]),([0,1,150,62,2,9,4,5],[0,3,2,171],[0]),([18,14,2,3,7,4,152],[7,15,47,13,1],[0]),([0,1,56,112,3,4,5],[7,26,28],[0]),([18,54,2,9,3,5],[7,2,0,172],[0]),([0,1,265,2,3,7,4],[36,173,99,28],[]),([18,54,52,2,3,4,5],[0,1,15],[]),([130,0,1,2,3,4,182],[28,30,174],[]),([127,16,46,61,2,3,4,5],[7,3],[0]),([0,1,54,113,2,3,5],[111,150,13,7,140,26],[0,3]),([6,18,62,2,3,4],[7,131,1,0],[0]),([0,1,2,220,3,4,5],[7,24,12,85,86],[]),([36,18,14,2,3,7,4],[7,0,1],[0]),([170,2,58,3,4,5],[1,11,7],[0]),([18,54,61,2,3,4,5],[7,48,0,3,14],[0]),([18,62,2,3,7,4],[7,0],[0]),([18,111,62,2,3,4,5],[0,7,2,3],[0]),([18,185,14,2,3,4,5],[7,11,13,14],[0]),([18,62,2,9,4,5],[7,0,45],[0]),([18,62,56,2,3,4,5],[7,3,10,13,14],[0]),([0,66,239,2,3,4,5],[10,24,31,50,91],[]),([18,111,2,3,4,5],[7,0,17,2],[0]),([18,150,62,2,3,4,5],[0,3,30,11,2,131,175],[0]),([170,18,2,3,7,4,5],[7,15,13,149,3],[0]),([48,170,2,3,4,5],[1,2,7,11],[0]),([170,18,2,3,7,4],[7,13,15],[0]),([218,0,1,61,2,3,4,5],[10,41,104],[]),([53,170,18,2,3,4,5],[0,15,3,176,24],[0]),([170,45,2,3,4,5],[15,7,1],[0]),([170,18,52,2,3,4,5],[0,1,15,177],[0]),([48,170,18,2,3,4,5],[7,1,11],[0]),([0,1,54,2,138,3,5],[3,122,178,13],[0]),([266,18,2,3,4,5],[28,30,1,157,11],[0]),([18,14,61,2,162,3,4,5],[30,11],[0]),([36,16,46,56,3,4,5],[7,3,0],[0]),([170,18,56,2,3,4,5],[7,1,11,13,5],[0]),([36,170,18,2,3,4,5],[7,1,11],[0]),([171,18,14,2,3,4,5],[0,1,11,2],[0]),([170,18,261,2,3,4,5],[15,7,3],[0]),([170,18,231,2,3,4,5],[15,3,179,65,40],[0]),([177,13,18,1,2,3,4,5],[13],[]),([267,170,2,3,4,5],[0,11,1,149,180],[0]),([170,18,2,268,3,4,5],[15,1,61,64,24],[0]),([6,170,2,3,4],[15,2,1,7,149],[0]),([53,18,54,2,3,4,5],[0,181,15,3,28,115],[0]),([170,2,17,3,4,5],[0,15,1,149,7],[0]),([45,18,14,61,2,3,4,5],[30,11],[0]),([170,56,2,3,4,5],[2,1,7,5,11,13],[0]),([18,54,56,2,3,5],[2,7,1,44,11,13],[0]),([170,61,2,3,4,5],[0,1,7,164,11],[0]),([18,261,2,3,4,5],[7,15,0,164],[0]),([45,18,62,2,3,4,5],[7,15,10],[0]),([170,232,2,3,4,5],[2,15,7,3,13],[0]),([18,0,1,2,181,3,7],[7,15],[0]),([170,63,2,3,4,5],[7,15],[]),([269,18,0,1,2,3,4,5],[1],[]),([65,18,14,56,2,3,4,5],[13,44,28,11,14],[0]),([126,18,14,2,3,4,5],[7,13,3,15],[0]),([18,195,14,2,3,4,5],[7,11,13,14],[0]),([121,18,14,2,3,4,5],[30,28,182,13,14],[0]),([0,1,113,2,220,3,4,5],[94,104,41],[]),([45,18,14,56,2,3,4,5],[28,11],[0]),([171,18,11,1,2,3,4,5],[33,89],[]),([170,52,2,3,4,5],[0,1,15,177],[0]),([153,11,1,2,3,4,5],[15,105,183,184,29],[]),([16,46,61,2,3,7,4],[7,0,1],[0]),([184,18,14,2,3,4],[28,13,30],[0]),([11,0,1,50,52,2,3,5],[86],[]),([270,18,0,1,2,3,4,5],[109,24,99],[0]),([170,40,2,3,4,5],[15,30,28],[]),([226,1,14,61,2,3,4,5],[34,30],[0]),([0,1,38,2,271,4,5],[7,10,38],[]),([48,0,1,62,61,4,5],[3,119,122,0,7],[0]),([253,18,2,3,4,5],[7,15],[]),([272,0,66,2,3,4,5],[28,10,91],[]),([18,14,2,202,3,4,5],[7,1],[0]),([68,45,14,3,4,5],[28,11,30],[0]),([31,229,0,1,2,3,4,5],[85,185,116],[]),([53,121,31,0,1,3,4,5],[24,38],[]),([18,8,1,2,9,7],[39,0,27,139,32],[]),([127,47,0,1,61,2,3,5],[34,2],[]),([273,0,1,56,2,3,4,5],[2,9,34],[0]),([170,18,61,2,3,4,5],[7,1,0,11],[0]),([170,31,2,3,4,5],[30,2,15,3,13],[0]),([36,18,14,56,3,4,5],[7,3,0],[0]),([274,18,2,3,4,5],[30,2,15],[0]),([20,16,46,2,3,4,5],[121,89,13,2,3],[0]),([127,0,1,14,61,2,9,5],[26,33,10],[0]),([0,1,54,2,3,7,103],[0,1,46],[0]),([0,1,111,61,2,4,5],[0,119,38,7,39,2],[0]),([31,0,1,61,2,9,5],[7,92,153,26,33],[]),([53,121,18,0,1,3,4,5],[24],[0]),([16,46,2,138,3,4,5],[7,3,13,14],[0]),([102,16,46,2,3,4,5],[0,1,118],[0]),([0,1,62,137,2,4,5],[3,186,122,13],[0]),([177,18,14,2,3,4,5],[59,13,11,2,24],[0]),([31,0,1,2,275,3,4,5],[85],[]),([127,18,0,1,61,56,3,5],[3,34,26],[0]),([276,170,2,3,4,5],[15,7,164,3],[0]),([121,18,0,1,52,3,4,5],[24,29,187,69],[0]),([177,31,0,1,2,3,4,5],[109,34],[]),([127,16,0,1,61,2,9,5],[33,26,10],[0]),([101,63,1,2,4,5],[36,28,11],[]),([277,31,0,1,2,3,4,5],[109,34],[]),([278,0,1,3,4,5],[15,28,30],[0]),([279,170,2,3,4,5],[15,1,60,57,149],[0]),([31,8,1,2,9,5],[7,92,153,188,50],[]),([18,185,0,1,61,2,4,5],[11,30],[0]),([65,18,54,2,3,4,5],[7,13,189,15,3],[0]),([119,0,1,2,3,7],[7,33,28,86],[]),([130,18,14,2,3,4,5],[28,30,190,13,14],[0]),([127,47,0,1,2,3,5],[7,39,34],[]),([170,18,2,17,3,4,5],[7,15,13,3],[0]),([121,31,0,1,52,3,4,5],[24,187,69,38],[]),([170,18,232,2,3,4,5],[15,7,3],[0]),([121,173,0,1,2,3,4,5],[69,15,168,34],[]),([127,18,14,2,3,4,5],[7,191,13,14],[0]),([16,0,1,2,3,263,4,5],[109,33],[0]),([68,170,2,3,4,5],[1,28,30],[0]),([53,18,11,1,2,3,4,5],[15,29],[]),([18,14,2,138,3,4,5],[7,3,13,14],[0]),([16,0,66,2,9,7],[7,36,32],[]),([276,18,2,3,4,5],[7,15],[]),([0,1,14,2,3,263,4,5],[109,33,110],[0]),([280,0,1,2,3,5],[33,30,24],[]),([145,18,2,3,4,5],[7,0],[0]),([47,18,54,2,3,5],[7,15,2],[]),([281,18,2,3,4,5],[28,192,0,15],[0]),([6,170,18,2,3,4],[7,15],[]),([53,170,2,3,4,5],[0,1,15,176,149],[0]),([127,0,1,62,2,4,5],[10,119,7,39,13],[0]),([0,1,258,62,2,3,4,5],[30,92,14,13,104],[0]),([282,0,1,2,3,4],[7,159,28],[]),([283,0,1,3,4,5],[33,30,24],[]),([16,284,2,3,4,5],[30,28,3],[0]),([39,0,1,56,2,9,5],[7,28,0,33,104],[]),([18,62,2,58,3,4,5],[7,1,10],[0]),([20,0,1,62,2,4,5],[13,146,89,2],[0]),([285,18,0,1,2,3,4,5],[2,11,29],[0]),([48,189,0,1,2,3,5],[7,28,34],[]),([218,0,1,2,3,4,5],[12,34,193,94,104,85,86],[]),([39,11,1,2,9,5],[7,28,105,194,33],[]),([18,286,2,3,4,5],[28,3,30,12],[0]),([0,1,61,2,236,3,4,5],[7],[0]),([276,18,62,2,3,4,5],[0,7,11,3],[0]),([170,65,2,3,4,5],[0,15,1,28],[0]),([206,18,2,3,4,5],[0,1,15,195],[0]),([6,0,1,2,112,3,4],[7,36,33,159,86],[]),([287,11,0,1,2,3,4,5],[196,29],[]),([130,184,0,1,2,3,4],[28,197,29],[]),([170,2,9,3,4,5],[7,0,53,11,3],[0]),([45,18,14,2,3,7,4],[15,7,47,13],[0]),([127,0,1,14,61,56,3,5],[26,33,3],[0]),([171,18,0,1,56,3,4,5],[11,34,2,38],[0]),([39,0,1,2,9,7],[7,28,139,99,33],[]),([18,195,0,1,56,2,3,5],[11,28],[0]),([18,14,2,58,3,7,4],[1,7,13,47],[0]),([18,14,2,181,3,4,5],[7,1],[0]),([170,2,268,3,4,5],[1,11,61,64],[0]),([18,14,56,2,9,3,5],[7,2,44,0],[0]),([110,18,14,2,3,4,5],[44,7,198,14,13],[0]),([36,170,2,3,4,5],[1,7,164,11],[0])]
def P_46_7_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [0,1,2,3,5,7,9,10,11,12,13,14,15,17,24,26,27,28,29,30,31,32,33,34,36,38,39,40,41,44,45,46,47,48,50,53,57,59,60,61,64,65,69,85,86,89,91,92,94,99,104,105,109,110,111,115,116,118,119,121,122,131,139,140,146,149,150,153,157,159,164,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_7_1 : checkNodesBT W_46 G_46 fmask_46 P_46_7_1 autos_46 bk_46_6 7 nd_46_7_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_46_7_1 : ∀ ns ∈ nd_46_7_1, Impossible G_46 7 (nodeValsBT W_46 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_6_ok chk_46_7_1
def nodes_46_7 : List NodeSpec := nd_46_7_0 ++ nd_46_7_1
def bk_46_7 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_7
set_option maxRecDepth 500000 in
lemma bk_46_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 7 xs.toFinset) bk_46_7 :=
  buildBucketsBT_of_mem (forall_append (mem_46_7_0) mem_46_7_1)
def nd_46_8_0 : List NodeSpec := [([0,70,1,2,3,4,5],[92,99,13,38,34],[]),([0,70,1,2,3,7,4],[0,28,104,33],[]),([0,71,1,2,3,7,4],[39,99,2,33,104],[4]),([72,0,1,2,3,4,5],[159,110,29,94,24,38,34],[1,4]),([73,0,1,2,3,4,5],[92,27,159,58,38,34],[]),([0,74,1,2,3,4,5],[50,89,33,29,12],[]),([75,13,0,1,2,3,4,5],[0,28,89,33,104,109],[2]),([13,0,76,1,2,3,4,5],[32,13,31,109],[]),([77,0,1,2,3,4,5],[11,33,50,86,85],[]),([11,0,76,1,2,3,4,5],[32,31,13,109,199,29,200,99],[]),([78,0,1,2,3,4,5],[30,31,15,13,38,34],[]),([79,11,0,1,2,3,4,5],[32,15,2,29],[]),([23,11,0,1,2,3,4,5],[126,30,28,2],[]),([29,11,0,1,2,3,5],[126,30,85],[]),([80,11,0,1,2,3,4,5],[30,201,28,13,99,104,33],[4]),([81,0,1,2,3,4,5],[30,2,24,202,203,38,34],[]),([0,82,1,2,3,4,5],[50,2,24,205,204,85],[]),([53,27,11,0,1,2,3,4,5],[29,181,13,15,99],[0]),([11,0,1,83,2,3,4,5],[30,33,31,15,122,89,13],[]),([84,11,1,2,3,4,5],[30,31,15,33],[0]),([53,31,11,0,1,2,3,4,5],[29,181,104,206,15,207],[0]),([31,11,0,1,52,2,3,4,5],[29,209,126,13,208,33,15],[]),([0,85,1,2,3,4,5],[92,2,87,210,34,38],[]),([15,0,86,1,2,3,4,5],[32,11,36,122,200,110],[]),([15,84,1,2,3,4,5],[15,30,2],[]),([87,0,1,2,3,4,5],[15,28,30],[]),([60,0,1,2,3,7,4],[7,211,28,33,104],[]),([48,60,0,1,2,3,4,5],[7,3,28,33,109,14,13,99],[]),([33,60,0,2,3,4,5],[7,15],[]),([60,0,42,2,3,4,5],[92,2,15,212,33],[]),([60,11,1,2,3,4,5],[28,30,15,213,33],[]),([88,0,1,2,3,4,5],[7,15],[]),([89,0,1,2,3,4,5],[30,2,15,214,24,38,34],[]),([90,0,1,2,3,4,5],[33,11,50,86,85],[]),([8,0,86,1,2,3,4,5],[39,32,36,11,29,90,200,110],[]),([84,8,1,2,3,4,5],[39,27,36,15,91,50],[]),([64,8,1,2,3,4,5],[27,92,0,15,50],[]),([8,11,0,1,2,9,5],[27,41,2,0,215],[0,2,1,4]),([6,60,0,1,2,3,4],[7,15],[]),([8,11,1,2,9,5],[41,27,2,216,215],[0,2,1,4]),([91,11,1,2,3,4,5],[30,31,13,15,33,109],[]),([26,8,1,2,3,4,5],[92,2,87,217,29,50,10],[2,0]),([41,8,0,1,2,9,5],[0,41,27],[1,4]),([41,8,11,1,2,3,5],[0,27,12],[1,4]),([92,8,0,1,2,3,4,5],[27,92,219,218,3,50,94],[2,5,1]),([92,0,1,2,3,4,5],[28,92,29,218,219,220,38,34],[1]),([55,0,1,93,2,3,4,5],[27,96,30,221,39,32,0,122,89,95],[0,5,1]),([34,8,0,1,56,2,3,4,5],[27,90,50,101,92,31,2,222],[0]),([34,0,1,2,3,7,4],[0,28,104,33],[0]),([34,0,1,56,2,3,4,5],[39,27,0,104,34,223,15,124,2,99,109,222],[0]),([34,11,0,1,2,3,4,5],[90,29,100,13,104,33,99],[0]),([94,0,1,2,3,4,5],[0,28,38,34],[]),([34,0,1,2,95,3,4,5],[0,28,223,34],[]),([96,8,1,2,3,4,5],[27,92,0,15,94,50],[]),([6,8,0,1,37,2,3,4],[0,27,126,114,2,32,28],[]),([8,0,1,37,2,9,4,5],[0,27,2,32,224,98,28],[0]),([8,0,1,37,56,2,3,4,5],[27,90,50,101,10,2,28],[0]),([8,0,1,97,2,3,4,5],[0,27,50,3,10],[0]),([8,0,1,98,2,3,4,5],[32,0,222,29],[]),([99,39,0,1,2,3,4,5],[0,27,10,28,225,3,34,122],[]),([39,0,1,2,100,3,4,5],[27,0,9,10,50,24],[0]),([39,0,37,2,3,4,5],[0,27],[0]),([101,8,1,2,3,4,5],[36,27,91,50],[0]),([102,16,0,1,2,3,4,5],[36,1,226,13,109,34,29],[0]),([16,0,1,2,3,7,4,103],[36,1,227,13,104,99,27,91],[0]),([20,16,0,1,2,3,4,5],[7,89,228,159,32,3,109],[0]),([16,0,1,2,9,3,7],[7,36,32,91,104],[0]),([16,0,1,104,2,3,4,5],[36,107,3,2,29,91,99],[0]),([16,105,1,2,3,4,5],[30,89,27,85,3],[0]),([106,0,1,2,3,4,5],[36,1,3,229,29],[0]),([107,0,1,2,3,4,5],[1,30,27],[]),([108,16,0,2,3,4,5],[36,126],[]),([35,99,0,1,2,3,4,5],[27,0,92,33,3,94],[0]),([109,0,1,2,3,4,5],[32,122,27,3],[]),([16,0,1,56,2,17,3,4,5],[109,50,231,13,228,230],[0]),([110,16,0,1,2,3,4,5],[7,107,39,50,94,198,103,14,13,232],[0]),([36,16,0,1,2,3,7,4],[7,1,36,32,104],[0]),([16,46,2,3,7,4,5],[0,31,233,3],[0]),([16,0,1,61,2,3,7,4],[7,36,103,33,1],[0]),([0,1,111,62,2,3,4,5],[0,31,3],[0]),([16,0,1,61,2,9,4,5],[7,151,33,36,104,3,26,110,91],[0]),([34,55,0,1,2,3,4,5],[0,27,2,32,95,10,24,223,31],[0]),([0,1,2,112,3,4,5],[103,235,30,234,58],[0]),([0,1,50,2,17,3,4,5],[7,89,236,109,110,50,122],[0]),([16,0,1,113,61,2,3,4,5],[7,34,26,107,147],[0]),([102,0,1,14,2,3,7,4],[0,237,89,109,99,1,33],[0]),([6,0,1,38,2,3,4],[7,1,31,36,159,33],[]),([18,0,1,2,17,3,4,5],[7,15,13,3],[0]),([16,0,42,2,17,3,4,5],[7,89,238,92,170,31,32,122],[0]),([53,16,0,42,2,3,4,5],[36,181,238,27,122,239,31,2,24],[0,3]),([36,16,0,42,2,3,4,5],[7,122,36,92,32,84,31,200],[]),([0,114,1,2,3,4,5],[13,28,110,38,34],[]),([6,16,0,66,2,3,4],[7,1,36,28,114,32],[0]),([115,0,1,2,3,4,5],[50,28,27,86,85],[]),([16,0,116,66,2,3,4,5],[36,24,31,32,11,30,122],[0]),([16,0,1,56,2,9,3,5],[7,31,107,50,104,0,103,99],[0]),([117,16,0,66,2,3,4,5],[28,36,122,11,30],[0]),([0,66,118,2,3,4,5],[0,10,31,50],[0]),([119,0,1,2,3,4,5],[7,33,28,85,86],[0]),([16,0,42,52,2,3,4,5],[36,1,209],[3]),([0,1,2,3,120,4,5],[13,27,110],[1,4]),([102,16,0,1,2,3,7,4],[36,226,109,33,13,1,27],[0]),([6,16,46,2,3,4],[31,2,233,1,7],[0]),([13,39,1,2,3,4,5],[7,28,0,15,33],[]),([16,0,1,113,2,3,4,5],[7,39,34,103,94,13,14,111,107,104,12,240],[0]),([16,46,2,17,3,4,5],[0,89,7,1,233],[0]),([121,18,0,1,2,3,4,5],[28,30,168,34,187,13],[0]),([16,46,2,9,3,4,5],[7,2,0,241,3],[0]),([53,16,46,2,3,4,5],[0,89,3,233,2],[0]),([8,0,42,1,2,9,5],[41,27,92,242,244,243,2,90],[3,2,0,5,1,4]),([48,16,46,2,3,4,5],[1,2,10],[0]),([53,64,0,1,2,3,4,5],[0,15,245,3,24],[]),([0,1,14,61,56,3,4,5],[165,246,39,148,34,140,0,103,7,104,3,247],[0]),([31,18,0,1,52,2,3,4,5],[15,249,24,1,208,29,209,248],[0]),([0,1,50,2,9,3,5],[7,31,36,250,50],[0]),([0,1,59,56,3,4,5],[50,2,31,13],[]),([48,65,18,0,1,2,3,4,5],[1,28,15,13],[0]),([36,0,1,50,2,3,4,5],[7,122,36,50,200,110],[]),([41,18,1,2,3,4,5],[39,27,0,251,31,32],[]),([0,66,50,2,3,4,5],[7,36,28,252,31,50],[0]),([92,11,0,1,2,3,4,5],[30,28,253,254,104,33,13],[1]),([121,11,0,1,2,3,4,5],[30,255,33,28,31,99,13],[0]),([45,18,8,1,2,3,4,5],[15,27,30],[]),([0,1,38,2,9,4,5],[7,31,36,256,33],[0]),([0,1,38,56,2,3,4,5],[7,31,104,34,122,89,200,109,99],[0]),([122,0,1,2,3,4,5],[36,30,31,38,34],[]),([0,1,123,38,2,3,4,5],[7,36,122],[]),([48,34,0,1,2,3,4,5],[39,223,27,0,33,109,15,2,99],[]),([0,42,38,2,3,4,5],[7,31,36,257,33],[0]),([124,15,0,1,2,3,4,5],[32,258,92,93,30,1,11,110],[]),([8,0,1,38,2,4,5],[27,222,30,15,0,259],[]),([6,0,1,51,2,3,4],[32,1],[]),([0,1,51,2,3,7,4],[32,31,7,260,1,99,85],[0]),([0,1,54,2,3,7,5],[0,31,261],[0]),([0,1,51,2,17,3,4,5],[32,89,30,122,13,3],[]),([34,8,0,1,2,9,4,5],[0,27,2,32,92,98],[0]),([0,1,2,125,3,4,5],[36,126],[]),([102,18,0,1,2,3,7,4],[263,139,13,89,109,28,33,27,15],[0]),([0,1,51,56,3,4,5],[50,31,27,1,264],[]),([126,18,0,1,2,3,4,5],[7,15,265,3],[0]),([36,0,1,51,3,4,5],[32,122,30,3],[]),([57,45,0,1,3,4,5],[27,11,30,12],[]),([127,0,1,14,61,2,3,4,5],[26,33,246,10,3],[0]),([0,1,128,2,3,4,5],[50,31,27,266,1,85],[]),([0,42,51,2,3,4,5],[32,31,7,268,267],[]),([10,0,1,51,2,3,4,5],[126,30,27,89,122,34],[]),([11,0,1,51,2,3,4,5],[30,33,31,15,2,13,89],[]),([0,1,123,2,3,4,5],[33,36,30,269,122,24,86],[]),([129,0,1,2,3,4,5],[28,30,36,15,86,85,38,34],[]),([8,0,1,51,2,3,4,5],[27,50,36,15,222,122],[]),([130,8,0,1,2,3,4,5],[27,50,92,272,270,271,90],[]),([18,0,1,2,131,3,4],[30,28,273,9,91],[0]),([132,0,1,2,3,4,5],[32,122,30,3],[]),([16,46,2,3,7,4],[31,0,2,233],[0]),([16,0,66,56,2,3,4,5],[7,28,50,122,10,89,200,103],[0]),([18,0,1,2,3,7,4,5],[7,15,13,99,3],[0]),([45,18,0,1,56,2,3,4,5],[28,11,38],[0]),([15,18,1,56,2,3,4,5],[7,39,50,3,13,14,2,103],[]),([18,0,1,52,2,3,4,5],[0,1,15,24,99],[0,3]),([18,0,1,56,2,3,4,5],[7,31,3,34,104,13,14,99,109],[]),([36,18,0,1,2,3,4,5],[7,122,0,11,14,110],[]),([18,0,1,61,2,3,4,5],[7,92,0,3,34,26,14,147,110],[]),([18,0,1,2,3,7,4],[7,31,13,15,33,104,99],[0]),([18,11,1,2,3,4,5],[30,31,15,33],[0]),([44,0,1,2,3,4,5],[33,30,24,86,85],[]),([18,8,1,2,3,4,5],[27,92,0,15,94,50],[]),([47,0,1,2,3,4,5],[7,15],[]),([63,0,1,2,3,4,5],[7,15],[]),([18,8,1,2,58,3,4,5],[15,27,30,50],[]),([18,14,2,3,7,4,5],[0,2,274,1,15,28],[0]),([0,1,14,2,3,7,4,103],[0,1,275,104],[0]),([41,55,0,1,2,3,5],[0,27,41,2],[1,4]),([53,18,11,1,2,3,4,5],[105,277,15,181,28,278,33,30,89],[0]),([20,0,1,14,2,3,4,5],[13,146,89,279,159,3,32,109],[0]),([0,1,59,2,17,3,4,5],[32,13,89,110],[]),([16,0,66,2,9,4,5],[7,36,28,280,32,91],[0]),([18,0,1,133,56,2,3,4,5],[34,104,281,28,109,27,263,1,2,31,13],[0]),([0,1,14,104,2,3,4,5],[0,140,89,2],[0]),([134,0,1,38,2,3,4,5],[7,122,200,89,109,9,34],[0]),([0,1,135,2,3,4,5],[0,1,58],[0]),([102,0,1,14,2,3,4,5],[0,1,99,109,237],[0]),([105,1,14,2,3,4,5],[0,1],[0]),([0,1,136,2,3,4,5],[32,3,31],[]),([18,0,1,113,56,2,3,4,5],[7,34,143],[0]),([110,0,1,14,2,3,4,5],[140,198,39,148,50,7,10,14,13,103,232],[0]),([16,0,1,137,2,3,4,5],[7,122,26,33,13,14,9,109],[0]),([0,1,14,113,56,2,3,4,5],[140,34,2,148,31,7],[0,3]),([26,0,1,52,2,3,4,5],[87,209,15,9,282,34,24],[0]),([16,34,0,2,3,4,5],[0,27,12],[]),([13,91,1,2,3,4,5],[7,13,31],[]),([13,45,1,2,3,4,5],[32,11],[]),([36,0,1,14,56,3,4,5],[3,7,283,122,148,104,50,0,109,9],[0]),([0,1,14,2,138,3,4,5],[3,283,122,284,104,50,13,14,109,9],[0]),([0,1,139,2,3,4,5],[32,3,122],[]),([26,0,1,2,9,3,5],[39,2,87,285,50],[0,5]),([53,16,11,0,1,2,3,4,5],[181,29,15,13,99],[0]),([6,0,1,14,61,2,3,4],[1,7,246,126,33,286,103,104],[0]),([140,0,1,2,3,4,5],[32,1],[]),([45,11,0,1,2,3,4,5],[15,30,33,2],[]),([0,1,14,61,2,9,4,5],[132,156,151,33,0,104,3,26,91,110],[0]),([48,0,1,14,61,3,4,5],[3,246,122,26,33,7,287,0,109,9],[0]),([0,1,14,61,56,2,3,4,5],[140,34,3,148,26],[0]),([141,0,1,2,3,4,5],[7,92,50,85,86],[]),([16,0,1,61,56,3,4,5],[7,39,34,107,103,0,104,165,122,247],[0]),([127,0,1,14,2,3,4,5],[191,246,39,103,33,288,10,13,14,7,289],[0]),([36,0,1,54,2,3,4,5],[3,84,122,0,290,50,14,110],[0]),([48,16,0,66,2,3,4,5],[7,122,28,32,10,200,89,103],[0]),([6,18,0,1,2,3,4],[7,15,2],[]),([142,0,1,2,3,4,5],[33,30,24,86,85,58],[0]),([0,1,14,113,61,2,3,4,5],[34,26,246,3,10,7,140],[0,3]),([0,1,54,2,3,7],[2,31,0,86],[0]),([143,0,1,2,3,4,5],[103,147,235,58],[0]),([0,1,54,2,17,3,4,5],[0,170,89,261,109,110,50,3],[0]),([44,18,0,1,52,2,3,4,5],[1,15,291,24,3],[]),([53,0,1,54,2,3,4,5],[0,181,89,3,261,94],[0,3]),([0,1,54,52,2,3,4,5],[0,1],[0]),([34,0,1,2,9,4,5],[39,0,27,292,33],[0]),([53,0,1,50,2,3,4,5],[36,206,122,236,27,2,99],[0]),([0,1,62,2,3,7,4],[0,31,104,33],[0]),([53,18,0,1,2,3,4,5],[0,15,3,24,2,99],[0,3]),([0,1,14,133,56,2,3,4,5],[1,34,104,109,13,99,155],[0]),([0,1,62,2,9,4,5],[132,0,31,2,171,33],[0]),([144,0,1,2,3,4,5],[11,50,33,86,85],[]),([0,1,62,56,2,3,4,5],[2,148,31,104,34,3,10,99,109,13,14],[0]),([0,1,62,61,2,4,5],[0,235,1,147,119],[0]),([31,18,14,2,3,4,5],[30,2,15,3,13],[0]),([145,0,1,2,3,4,5],[0,31,34,38],[0]),([146,0,1,2,3,4,5],[33,10,90,86,85],[]),([0,1,147,2,3,4,5],[7,200,13],[]),([6,0,1,59,2,3,4],[1,2,33],[]),([47,0,1,52,2,3,4,5],[15,293,294,9,34],[]),([0,1,54,61,2,3,4,5],[48,0,39,290,10,26,34,3,14,110],[0]),([0,1,59,2,3,7,4],[32,13,31,2,1,99],[]),([0,1,59,52,3,4,5],[50,13,33,94],[]),([36,16,0,1,56,3,4,5],[7,122,50,104,0,9,109],[0]),([36,0,1,59,3,4,5],[32,3,122],[]),([0,1,59,61,3,4,5],[33,0,36,147,3,38],[]),([148,0,1,2,3,4,5],[32,3,31],[]),([149,0,1,2,3,4,5],[32,3,122],[]),([45,18,0,1,2,3,7,4],[7,15,13,263,104],[0]),([0,1,150,2,3,4,5],[33,0,36,295,86,3,24,85],[]),([55,0,1,37,2,3,4,5],[0,27,122,2,32,92,95,28],[0]),([18,8,37,2,3,4,5],[0,27],[]),([102,18,0,1,2,3,4,5],[139,262,15,24,296,13,89,109,34,29],[0]),([53,18,14,2,3,4,5],[0,3,15,274,128,24],[0]),([151,0,1,2,3,4,5],[30,28,1,13,34],[0]),([0,1,14,137,2,3,4,5],[3,297,122,26,33,13,14,287,109,9],[0]),([44,11,1,2,3,4,5],[28,30,33,58],[]),([127,16,0,1,2,3,4,5],[7,39,103,33,94,13,14,191,289],[0]),([0,1,50,61,2,3,4,5],[7,36,39,26,34,122,200,110],[0])]
def P_46_8_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [0,1,2,3,7,9,10,11,12,13,14,15,24,26,27,28,29,30,31,32,33,34,36,38,39,41,48,50,58,84,85,86,87,89,90,91,92,93,94,95,96,98,99,100,101,103,104,105,107,109,110,111,114,119,122,124,126,128,132,139,140,143,146,147,148,151,155,156,159,165,168,170,171,181,187,191,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_8_0 : checkNodesBT W_46 G_46 fmask_46 P_46_8_0 autos_46 bk_46_7 8 nd_46_8_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_46_8_0 : ∀ ns ∈ nd_46_8_0, Impossible G_46 8 (nodeValsBT W_46 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_7_ok chk_46_8_0
def nd_46_8_1 : List NodeSpec := [([18,0,1,2,3,7,4,103],[137,139,298,89,13,28,27,15,2,31],[0]),([18,0,1,2,3,7,4,152],[7,15,265,263,137],[0]),([18,0,1,104,2,3,4,5],[143,139,89,3,24,11,2,29],[0]),([153,0,1,2,3,4,5],[15,139,273,58],[0,3]),([16,0,1,2,138,3,4,5],[7,122,50,104,13,14,9,109],[0]),([27,11,0,1,52,2,3,4,5],[29,209,126,13],[0]),([34,18,8,2,3,4,5],[0,27,94],[]),([154,18,0,1,2,3,4,5],[1,139,294,11,24,13,29],[]),([155,18,1,2,3,4,5],[1,30,27,85,94],[]),([124,8,0,1,2,3,4,5],[32,92,93,90,29,1,258,10,104,110],[2,0]),([0,1,2,156,3,4,5],[9,11,139,58],[0]),([18,0,1,137,2,3,4,5],[7,39,273,33,26,13,14,9,109],[0]),([57,0,1,51,3,4,5],[27,122,30,200,12],[]),([130,0,1,2,3,4,5],[33,50,29,24,190,299,174,85],[]),([6,36,18,0,1,2,3,4],[7,1,32],[]),([157,0,1,2,3,4,5],[33,30,24,86,85],[]),([0,1,14,56,2,17,3,4,5],[13,109,231,146,50,230],[0]),([158,0,1,2,3,4,5],[32,28,122,27,3,58,85,86],[]),([0,1,50,52,2,3,4,5],[36,1,300],[0]),([35,34,0,2,3,4,5],[0,27],[0]),([110,18,0,1,2,3,4,5],[7,143,39,50,103,14,13,232],[0]),([0,1,159,2,3,4,5],[7,31,36,301,34,38],[]),([16,23,0,2,3,4,5],[126,27,89,12],[]),([36,18,0,1,2,3,7,4],[7,137,139,39,32],[0]),([36,18,0,1,56,3,4,5],[7,273,92,0,3,122,28,50,104,9,109],[0]),([18,0,1,2,138,3,4,5],[7,39,273,50,104,13,14,9,109],[0]),([160,0,1,2,3,4,5],[32,11,37,85,86],[]),([161,0,1,2,3,4,5],[28,26,29,86,85],[]),([39,0,1,2,58,3,4,5],[28,15,30,302,109,50],[]),([48,18,0,1,61,3,4,5],[7,273,28,3,122,33,92,26,0,9,109],[0]),([127,18,0,1,2,3,4,5],[7,39,103,33,13,14,289],[0]),([16,0,42,61,2,3,4,5],[7,36,92,33,122,31,200,48],[0]),([18,0,1,61,2,9,4,5],[7,39,139,33,26,3,110],[0,3]),([18,0,1,113,61,2,3,4,5],[7,34,26,143],[0]),([18,0,1,61,2,162,3,4,5],[30,11,34],[0]),([47,0,1,2,17,3,4,5],[7,15,303,304],[0]),([0,1,2,162,3,4,5],[103,15,37,58],[0]),([33,15,18,2,3,4,5],[7,15,2],[]),([13,18,1,2,17,3,4,5],[7,15,13,3],[0]),([13,18,1,52,2,3,4,5],[0,15,294,27,28,33],[]),([48,18,8,1,2,3,4,5],[7,305,39,32,103,15,0,31],[]),([13,18,1,61,2,3,4,5],[7,39,0,33,3,14,147],[]),([18,25,1,2,3,4,5],[39,27,15,0,94,32],[]),([53,18,11,0,1,2,3,4,5],[15,181,29,277],[]),([8,0,163,1,2,3,4,5],[32,0,92,306,29],[]),([16,46,56,2,3,4,5],[31,2,1,7,123,13],[0]),([45,8,0,1,2,3,4,5],[15,27,30,3,34,26,12],[]),([18,11,1,2,17,3,4,5],[7,39,276,89,278,32,307],[0]),([0,1,59,2,3,7,4,5],[32,1,13,99],[]),([18,11,1,2,9,3,5],[7,28,31,105,308,2,32],[0,3]),([18,0,1,2,9,3,7],[7,139,28,31,0,32,104],[0,3]),([36,18,11,1,2,3,4,5],[7,307,39,32,105,15,122],[]),([48,15,18,1,2,3,4,5],[7,3,39,11,14,13,103],[]),([164,0,1,2,3,4,5],[15,7],[]),([15,18,42,2,3,4,5],[92,2,15,162,32],[]),([39,0,1,2,165,3,4,5],[28,30,302,9,109,0,15,34],[]),([36,0,1,14,2,3,7,4],[0,1,283,32,104],[0]),([99,18,0,1,2,3,4,5],[0,27,122,3,34,24],[]),([0,1,51,61,3,4,5],[33,36,30,50,309,37,200,38],[]),([11,0,1,50,2,3,5],[30,31,15,2],[0]),([6,45,0,1,2,3,4],[15,32],[]),([6,18,8,1,2,3,4],[39,27,310,31,32],[]),([13,63,1,2,3,4,5],[7,15],[]),([18,8,1,2,9,4,5],[39,27,139,311,32],[0]),([16,0,1,113,56,2,3,4,5],[7,34,107,2],[0]),([33,18,8,2,3,4,5],[39,27,15,36,94,32],[]),([18,8,1,2,100,3,4,5],[0,27,92,50,10],[0]),([15,18,1,2,3,7,4],[7,39,139,2,32],[]),([18,32,0,166,1,2,3,4,5],[3,122,24,34],[]),([18,14,52,2,3,4,5],[0,1,15,312,12],[0]),([167,0,1,2,3,4,5],[7,15,28,313,34,38],[]),([18,69,1,2,3,4,5],[39,2,15,314,32],[]),([18,8,42,2,3,4,5],[27,92,162,315,31,32],[0]),([168,0,1,2,3,4,5],[0,28,38,34],[]),([18,14,56,2,3,4,5],[2,7,1,44,11,13],[0]),([39,0,1,2,3,7,4],[7,139,28,99,104,33],[0]),([18,11,1,61,2,3,4,5],[39,30,33,105,15,307,235],[0]),([18,8,1,2,3,7,4],[39,139,27,31,32],[0]),([36,18,14,2,3,4,5],[1,7,316,11],[0]),([41,11,0,1,2,3,5],[0,27,2],[1,4]),([16,46,61,2,3,4,5],[0,1,7,147,235,317],[0]),([169,0,1,2,3,4,5],[36,2,28],[]),([44,8,1,2,3,4,5],[27,92,50,91],[]),([18,62,2,3,4,5],[7,0,316,131,2],[0]),([53,31,18,0,1,2,3,4,5],[15,24,3,206,181],[0]),([0,1,54,2,9,3,5],[132,2,31,0,318,50],[0]),([63,8,0,1,2,4,5],[15,27,37],[3]),([170,18,2,3,4,5],[7,15,2,164,149],[0]),([18,55,1,2,3,4,5],[39,27,319,320,94,32],[]),([65,18,14,2,3,4,5],[0,11,1,274,28],[0]),([171,18,0,1,2,3,4,5],[15,139,109,34,2,159],[0,3]),([31,0,1,2,58,3,4,5],[15,30,28,168,33],[]),([0,1,38,2,3,7,4],[7,36,33,104],[0]),([34,13,1,2,3,4,5],[0,28,33],[]),([127,18,0,1,61,2,3,4,5],[7,33,26,3],[0]),([172,0,1,2,3,4,5],[50,89,33,12,94],[1]),([45,31,0,1,2,3,4,5],[15,30,28,3,34,104],[0]),([47,18,11,1,2,3,5],[15,30],[]),([6,34,0,1,2,3,4],[39,321,27,15,104,33],[]),([173,31,0,1,2,3,4,5],[30,28,249,248,109,168],[0]),([47,18,14,2,3,4,5],[7,15,2],[0]),([18,0,1,56,2,17,3,4,5],[109,15,231,13,50,322,30],[0]),([64,0,1,2,17,3,4,5],[7,15,13,3],[0]),([60,0,1,56,2,3,4,5],[7,28,3,34,104,13,14,99,109],[]),([0,174,1,2,3,4,5],[0,28,58,34,38],[]),([121,0,1,2,3,4,5],[50,33,29,24,182,323,187,85],[0]),([47,0,1,61,2,3,4,5],[7,92,15,293,304,34,26,41,110],[0]),([48,8,0,1,37,2,3,4,5],[27,90,3,32,28],[]),([0,1,62,2,17,4,5],[0,89,325,1,324],[0]),([15,47,1,2,3,4,5],[7,15],[]),([53,13,18,1,2,3,4,5],[0,15,277,3,28],[]),([18,0,1,61,2,3,7,4],[7,139,39,103,33,137],[0]),([47,8,1,2,3,4,5],[7,15,92,293,50],[]),([175,0,1,2,3,4,5],[27,92,0,326,86,85,38,34],[]),([48,18,0,1,2,17,3,4,5],[7,1,322,13,109,32,327],[]),([65,31,0,1,2,3,4,5],[30,15,28,249,109,168,99],[0]),([65,18,11,1,2,3,4,5],[15,30,28,276,307],[0]),([31,0,1,2,17,3,4,5],[7,249,92,248,109,110,50,168],[0]),([16,46,52,2,3,4,5],[0,1],[0]),([18,11,1,52,2,3,4,5],[105,294,15,209,28,278,33,29,89,2,31],[]),([176,0,1,2,3,4,5],[7,92,153,328,34,38],[]),([177,18,0,1,2,3,4,5],[322,13,89,109,24,34,159,265,15,29,2],[0,3]),([31,0,1,2,9,3,5],[7,153,28,31,329,2,91,50],[0,3]),([6,18,0,1,61,2,3,4],[7,1,330,39,33,15,103],[0]),([18,0,1,56,2,9,3,5],[7,28,143,50,0,31,2,103,99],[0,3]),([178,44,1,2,3,4,5],[33,30,24,37],[0,2]),([53,31,0,1,2,3,4,5],[153,168,15,30,277,206,181,248,24],[0]),([31,0,1,52,2,3,4,5],[153,9,15,248,34,208,209,24,294,29],[0]),([48,18,14,2,3,4,5],[1,7,2,11],[0]),([36,31,0,1,2,3,4,5],[7,168,92,153,50,15,110],[]),([31,8,1,2,3,4,5],[27,92,153,331,91,50],[0]),([18,14,2,17,3,4,5],[0,7,1,15,274],[0]),([45,0,1,2,17,3,4,5],[32,1,30,92,13,110,3],[]),([0,1,14,2,9,3,7],[0,132,31,32,104],[0]),([179,0,1,2,3,4,5],[7,13,31],[]),([178,0,1,2,3,4,5],[122,27,30,86,85],[]),([31,0,1,2,180,3,4,5],[30,28,168,15,9,109,249,34],[0]),([18,0,1,113,2,3,4,5],[7,39,34,103,13,14,11,143,240],[0]),([18,0,1,2,58,3,7,4],[7,15,13,263,33],[0]),([63,18,14,2,3,4,5],[7,15,316],[0]),([16,0,66,2,3,7,4],[7,36,32],[0]),([63,18,8,1,2,4,5],[15,27],[]),([121,31,0,1,2,3,4,5],[30,28,168,187,249],[0]),([18,0,1,2,181,3,4,5],[7,15,122],[0]),([92,55,0,1,2,3,4,5],[39,29,218,219,32,95,94],[2,5,1]),([18,14,61,2,3,4,5],[7,1,147,0,316,11],[0]),([63,0,1,2,3,7,4],[7,139,28,36,33,104],[]),([48,63,0,1,2,3,4,5],[7,333,28,15,109,0,41,99],[]),([44,18,14,2,3,4,5],[28,1,30,157,11,13],[0]),([39,0,1,2,3,4,182],[28,30,334,9,85],[0]),([63,0,1,56,2,3,4,5],[7,28,15,333,34,0,104,31,109,99],[]),([6,39,0,1,2,3,4],[7,334,28,104,33],[0]),([36,13,18,1,2,3,4,5],[7,3,39,0,11,14],[]),([16,11,0,1,52,2,3,4,5],[209,126,13,89],[0]),([183,0,1,2,3,4,5],[30,9,28,38],[]),([0,1,150,62,2,3,4,5],[0,10,3,2,175,33,325],[0]),([63,11,1,2,3,4,5],[7,15,28,105,33],[]),([44,0,1,58,3,4,5],[28,30,11],[0]),([0,1,54,56,2,3,5],[2,1,31,141,140,13],[0]),([184,18,0,1,2,3,4],[28,30,265,109],[0]),([18,185,0,1,2,3,4,5],[7,11,13,14],[0]),([18,0,1,61,56,3,4,5],[7,39,143,34,103,0,273,247],[0]),([186,0,1,2,3,4,5],[33,30,92,86,85],[]),([101,18,1,2,3,4,5],[36,28,94],[0]),([187,0,1,2,3,4,5],[32,1],[]),([65,18,0,1,56,2,3,4,5],[28,15,143,13,99],[0]),([184,39,0,1,2,3,4],[28,139,29,334,109],[0]),([39,0,1,56,2,3,4,5],[7,28,104,34,302,0,15,99,335],[0]),([6,44,0,1,2,3,4],[7,336,33,28],[]),([127,16,0,1,61,2,3,4,5],[7,33,26,122],[0]),([8,0,1,188,2,3,4,5],[27,50,36,15,222,122],[]),([44,0,1,2,17,3,4,5],[7,92,50,1,85,110],[]),([39,11,1,2,3,4,5],[28,30,105,337,58,33],[0]),([189,0,1,2,3,4,5],[7,28,338,339,85,86,34,38],[0]),([36,47,0,1,2,3,4,5],[7,304,92,293,15,41,110],[]),([75,11,0,1,2,3,4,5],[39,13,89,340,110,29,109,99,33,104],[2,5]),([18,11,0,1,52,2,3,4,5],[15,209,29,13,294,99,28],[]),([15,44,1,2,3,4,5],[7,92,50,91],[]),([6,16,0,1,61,2,3,4],[7,1,33,103,104],[0]),([45,0,1,2,3,7,4,5],[32,15,91,99],[]),([6,34,8,0,1,2,3,4],[0,27,126,114,32,2,31],[]),([48,39,0,1,2,3,4,5],[7,302,28,99,109,33,15,0],[0]),([39,0,1,2,3,4,5],[28,30,0,15,86,85,38,34],[]),([190,0,1,2,3,4,5],[28,30,341,342,38,86,85,34],[0]),([191,0,1,2,3,4,5],[33,10,30,86,85],[]),([6,63,0,1,2,3,4],[7,15],[]),([16,0,116,2,3,4,5],[7,36,343,24,31,32],[0]),([18,14,2,3,7,4],[2,7,0,274],[0]),([65,44,0,1,2,3,4,5],[30,28,15,291,3,33,9],[]),([101,0,1,2,3,4,5],[36,27,38,34],[]),([18,11,1,2,58,3,4,5],[15,30,28,33],[]),([48,0,1,62,2,3,4,5],[1,2,287,33,10],[0]),([18,14,2,9,3,4,5],[7,2,0,344,3],[0]),([44,0,1,2,3,7,4,5],[7,336,33,28,99,91],[0]),([64,0,1,52,2,3,4,5],[0,126,15,99],[0,3]),([8,0,1,2,9,7],[91,41,0,27],[0,2,3,5,1,4]),([34,11,1,2,3,4,5],[39,0,100,29,345,33],[0]),([48,0,1,59,3,4,5],[32,3,31],[]),([0,163,1,2,3,4,5],[33,0,50,24,306,29,86],[]),([170,2,3,4,5],[164,2,149],[0]),([45,18,0,1,61,2,3,4,5],[30,11,38],[0]),([34,8,11,1,2,3,4,5],[0,27,92,32,145],[0]),([45,18,11,1,2,3,4,5],[15,30,28],[]),([13,44,1,2,3,4,5],[7,33,28],[]),([48,18,0,1,2,3,4,5],[7,3,28,33,109,14,13,99],[]),([130,39,0,1,2,3,4,5],[28,30,302,197,174],[0]),([45,11,1,2,3,4,5],[32,15,28,79,29],[]),([0,1,111,2,3,4,5],[2,31,0,42,346,34,38],[0]),([6,15,18,1,2,3,4],[7,15,2],[]),([45,18,14,2,3,4,5],[15,7,1],[0]),([0,1,14,113,2,3,4,5],[111,150,246,34,347,7,13,14,104,103,140,240],[0,3]),([192,18,1,2,3,4,5],[1,28,30,85,12],[]),([0,1,193,2,3,4,5],[50,2,31,86,85],[]),([39,18,14,2,3,4,5],[28,0,30,348,15,274,3],[0]),([194,0,1,2,3,4,5],[28,50,30,86,85],[]),([53,26,0,1,2,3,4,5],[87,181,282,24,31,38,34],[0]),([16,99,0,1,2,3,4,5],[0,27,3,33,94,24],[0]),([18,195,0,1,2,3,4,5],[7,11,13,14],[0]),([68,18,14,2,3,4,5],[28,3,30,274,13],[0]),([0,196,1,2,3,4,5],[36,28,14,27],[]),([48,34,8,0,1,2,3,4,5],[27,90,3,32,31],[]),([8,11,1,37,2,3,4,5],[0,27,2,32,92,145,28],[0]),([47,31,0,1,2,3,5],[15,30,2,31],[]),([101,39,1,2,3,4,5],[36,28,37],[0]),([0,197,1,2,3,4,5],[39,0,27,350,34,38],[]),([198,0,1,2,3,4,5],[33,11,50,86,85],[]),([6,18,14,2,3,4],[2,274,7,1,15],[0]),([45,0,1,2,3,7,4],[32,15,28,27,31,2,91,99],[]),([199,0,1,2,3,4,5],[30,33,24,86,85],[]),([26,0,1,2,17,3,4,5],[39,349,30,282,13,109,110,2,31,50,351],[0]),([18,0,1,56,52,2,3,4,5],[1,34,13,104,28,109,31],[]),([16,0,200,66,2,3,4,5],[28,36,122,50,352,11,30],[0]),([177,16,0,1,2,3,4,5],[89,228,109,13,34,29,2,159],[0]),([68,45,0,1,3,4,5],[28,30,11],[0]),([15,45,1,2,3,4,5],[32,11,91],[]),([99,18,8,1,2,3,4,5],[0,27,50,92,10],[]),([16,0,42,2,9,3,5],[7,31,36,353,32],[0]),([31,0,1,61,2,3,4,5],[7,92,153,26,34,168,15,110],[0]),([20,18,0,1,2,3,4,5],[7,322,39,265,159,32,3,109],[0]),([45,8,1,2,3,4,5],[32,15,92,354,26],[]),([177,0,1,14,2,3,4,5],[13,146,89,109,2,34,159],[0]),([40,18,14,2,3,4,5],[15,30,28],[0]),([18,1,201,2,3,4,5],[7,36,12],[]),([18,0,1,2,202,3,4,5],[7,15,122],[0]),([185,0,1,2,3,4,5],[32,11,30,92,85,86],[]),([18,0,1,61,56,2,3,4,5],[7,143,34,273,26],[0]),([45,39,0,1,2,3,4,5],[15,28,30,3,34,26],[0]),([6,0,1,62,2,3,4],[2,1,286,325,33,31,0],[0]),([18,203,1,2,3,4,5],[28,30,1,38,12],[]),([195,0,1,2,3,4,5],[32,11,28,27,85,86],[])]
def P_46_8_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [0,1,2,3,7,9,10,11,12,13,14,15,24,26,27,28,29,30,31,32,33,34,36,37,38,39,41,42,44,48,50,58,79,85,86,87,89,90,91,92,93,94,95,99,100,103,104,105,107,109,110,111,114,122,123,126,131,132,137,139,140,141,143,145,146,147,149,150,153,157,159,162,164,168,174,175,181,182,187,190,197,200,206,208,209,218,219,222,228,230,231,232,235,240,246,247,248,249,258,263,265,273,274,276,277,278,282,283,286,287,289,291,293,294,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_8_1 : checkNodesBT W_46 G_46 fmask_46 P_46_8_1 autos_46 bk_46_7 8 nd_46_8_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_46_8_1 : ∀ ns ∈ nd_46_8_1, Impossible G_46 8 (nodeValsBT W_46 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_7_ok chk_46_8_1
def nd_46_8_2 : List NodeSpec := [([15,31,1,2,3,4,5],[30,2,92,153,15,50],[]),([8,0,197,1,2,3,4,5],[27,90,50,3,91,110,92],[]),([39,0,1,2,9,4,5],[7,28,139,355,33,58],[0,3]),([53,0,1,59,3,4,5],[0,1],[0]),([18,54,2,3,4,5],[2,7,115],[0]),([16,0,1,133,56,2,3,4,5],[1,34,104,356,13],[0]),([0,66,51,2,3,4,5],[32,36,30,358,357,94],[]),([18,14,2,58,3,4,5],[1,7,11],[0]),([34,0,163,1,2,3,4,5],[0,28,223],[]),([144,18,0,1,56,2,3,4,5],[28,104,11],[0]),([130,18,0,1,2,3,4,5],[28,30,197,302,34,174],[0]),([47,11,0,1,2,3,5],[15,30,2],[]),([204,0,1,62,2,3,4,5],[0,1,2,104,34],[0]),([0,1,14,56,2,9,3,5],[2,132,31,140,50,0,104,103,99],[0]),([63,39,0,1,2,4,5],[15,28,37],[0,3]),([178,18,1,2,3,4,5],[28,30,122,12],[2]),([198,18,0,1,61,2,3,4,5],[30,26,11],[0]),([0,1,51,2,3,7,4,5],[32,1,89,359,27,3],[]),([205,0,1,2,3,4,5],[7,15],[]),([206,0,1,2,3,4,5],[0,9,89],[0]),([31,0,1,2,3,4,5],[30,2,15,24,38,34,85],[0]),([207,0,1,2,3,4,5],[7,28,15,293,86,85,38,34],[]),([36,16,46,2,3,4,5],[1,3,7,317],[0]),([208,44,0,1,2,3,4,5],[30,33,24,1],[]),([48,0,1,38,2,3,4,5],[7,122,33,109,200,89,99],[]),([44,0,1,2,3,7,4],[7,33,28,99,91,336],[0]),([16,0,1,61,56,2,3,4,5],[7,107,34,122,26],[0]),([48,0,1,51,3,4,5],[32,122,27,3],[]),([0,1,14,61,2,3,7,4],[36,246,0,103,33,1],[0]),([48,16,0,1,61,3,4,5],[7,122,33,26,0,9,109],[0]),([18,8,1,56,2,3,4,5],[39,27,50,0,15,305,31,103],[0]),([30,18,1,2,3,4,5],[39,2,105,360,32],[]),([16,209,0,2,3,4,5],[7,36,32],[]),([53,47,0,1,2,3,4,5],[15,293,277,28,38,34],[])]
def P_46_8_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [0,1,2,3,7,9,11,12,13,15,24,26,27,28,30,31,32,33,34,36,37,38,39,50,58,85,86,89,90,91,92,94,99,103,104,105,107,109,110,115,122,132,139,140,153,174,197,200,223,246,277,293,302,305,317,336,355,356,357,358,359,360]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_8_2 : checkNodesBT W_46 G_46 fmask_46 P_46_8_2 autos_46 bk_46_7 8 nd_46_8_2 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_46_8_2 : ∀ ns ∈ nd_46_8_2, Impossible G_46 8 (nodeValsBT W_46 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_7_ok chk_46_8_2
def nodes_46_8 : List NodeSpec := nd_46_8_0 ++ nd_46_8_1 ++ nd_46_8_2
def bk_46_8 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_8
set_option maxRecDepth 500000 in
lemma bk_46_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 8 xs.toFinset) bk_46_8 :=
  buildBucketsBT_of_mem (forall_append (forall_append (mem_46_8_0) mem_46_8_1) mem_46_8_2)
def nodes_46_9 : List NodeSpec := [([19,0,1,2,3,4,5],[99,91,2,29,94,38],[0,2,1,4]),([20,0,1,2,3,4,5],[110,41,85,12,94,38],[0,3,5,2,1,4]),([21,0,1,2,3,4,5],[110,27,13,85,94,38,58],[0,2,1,4,3,5]),([0,1,2,9,3,7],[91,41],[0,3,2,5,1,4]),([22,0,1,2,3,4,5],[91,12,89,24,2,38,361],[1,0,3,5]),([23,0,1,2,3,4,5],[91,126,28,362,89,38,58,12],[1,0,3,4,5]),([13,0,24,1,2,3,4,5],[0,15,363,91,12,109],[0,2]),([25,0,1,2,3,4,5],[41,0,12,364,27,94,38,85],[3,0,5,2,1,4]),([11,0,24,1,2,3,4,5],[216,28,15,365,363,109,29,99,31,2,104],[0,2,5]),([11,10,0,1,2,3,4,5],[30,2,126,15,12,85,86,31,104],[0,2,1]),([26,0,1,2,3,4,5],[2,92,282,31,38,37,85],[0,5]),([27,11,0,1,2,3,4,5],[30,31,2,15,104,99,366],[0]),([28,0,1,2,3,4,5],[2,91,58,94,38],[3,5,1,4]),([29,0,1,2,3,4,5],[91,126,367,15,94,38,2,99],[3,0,5,2,1]),([6,15,0,1,2,3,4],[2,368,41,126,15,31,104],[0,2,1]),([30,0,1,2,3,4,5],[2,41,216,369,94,38],[0,2,1,4]),([31,0,1,2,3,4,5],[30,370,2,248,31,24,38,37,85],[0,3]),([18,32,0,1,2,3,4,5],[27,30,126,15,12,94,38,24,34,371,265],[0,5,3]),([0,1,14,2,17,3,4,5],[0,89,279,110,85,1,372,109],[0]),([15,0,1,2,3,7,4],[2,91,31,104],[0,2,1,4]),([8,0,1,2,9,4,5],[41,27,91,2,373],[0,2,3,5,1,4]),([33,15,0,1,2,3,4,5],[15,41,2,94,3,104],[0,2,1]),([15,11,1,2,3,4,5],[2,41,216,374],[0,2,1,4]),([33,8,0,1,2,3,4,5],[222,41,15,27,36,90,104,110,91,12,375],[0,3,2,5,1]),([13,8,1,2,3,4,5],[41,0,12,27,376,91],[0,2,1,4]),([11,0,1,2,17,3,4,5],[366,41,30,170,377,13,110,89,109,31,104],[0,2,3,5,1,4]),([6,8,0,1,2,3,4],[41,378,27,2,31,104],[0,2,3,5,1,4]),([8,11,0,1,2,3,4,5],[2,29,41,379,0,12,31,104,366],[0,2,1,4]),([34,8,0,1,2,3,4,5],[0,27,92,222,41,12,28,375],[0,3,2]),([8,0,1,2,3,7,4],[41,91,0,27,2,31,104],[0,2,3,5,1,4]),([34,0,1,2,3,4,5],[0,28,380,321,222,38,58,85],[3,1,0,2]),([35,8,0,1,2,3,4,5],[27,36,222,30,15,122,375,110,91],[0,5]),([36,16,0,1,2,3,4,5],[1,7,381,38,3,94,2,41],[0]),([8,0,1,37,2,3,4,5],[0,222,27,41,12,31,122,375],[0,3,2]),([0,1,38,2,3,4,5],[7,94,381,382,36,259,38,58,85],[0]),([39,8,0,1,2,3,4,5],[27,384,92,222,30,383,90,378,91,375],[0,3,5]),([40,18,0,1,2,3,4,5],[15,30,28,385,85],[0,3]),([36,0,1,14,2,3,4,5],[1,3,386,2,38,41],[0]),([16,0,1,2,3,7,4,5],[36,31,387,2,27,91,99,122,104],[0]),([41,0,1,2,3,4,5],[41,0,27,388,94,38,85],[0,2,3,5,1,4]),([16,0,1,2,3,7,4],[31,7,36,2,91,104,99,387],[0]),([16,0,1,2,9,3,4,5],[7,31,36,389,41,32,122,91,104],[0]),([16,0,42,2,3,4,5],[31,7,2,238],[3,0]),([16,11,0,1,2,3,4,5],[30,2,31,15,104,99,366],[0]),([43,13,0,1,2,3,4,5],[0,31,12,390,109,104],[0,2]),([16,8,0,1,2,3,4,5],[27,222,30,0,15,12,41,110,122,89,375],[0]),([44,0,1,2,3,4,5],[7,336,33,24,391,273,37,58,85,157],[0,3,5]),([45,18,0,1,2,3,4,5],[15,7,273,50,33],[0,5,3]),([16,46,2,3,4,5],[94,12,2,317,233],[0]),([18,0,1,2,17,3,4,5],[265,7,15,392,92,89,13,385,110,109,41,273],[0,3]),([6,16,0,1,2,3,4],[31,387,7,2,1,104,91],[0]),([47,18,0,1,2,3,4,5],[7,15,370,2,31],[0,3]),([48,16,0,1,2,3,4,5],[1,31,27,2,38,10,41],[0]),([0,1,2,3,7,4,49],[2,91,31,104],[1,4,0,2]),([43,11,0,1,2,3,4,5],[216,31,393,13,2,109,29,377,104],[0,2,5]),([0,1,50,2,3,4,5],[31,7,2,236,38,37,85],[0]),([0,1,51,2,3,4,5],[1,32,94,394,359,31,37,85],[0,5]),([18,0,1,2,3,4,5],[7,94,15,12,2,38,37,85,86],[0,5,3]),([16,0,1,2,17,3,4,5],[36,7,1,387,85,13,110,109,41,12],[0]),([6,0,1,14,2,3,4],[2,1,372,31,286,104],[0]),([16,0,1,52,2,3,4,5],[36,1,13,94,300,91],[0]),([39,0,1,2,3,4,5],[28,392,139,334,29,348,395,38,58,85,86],[0,3]),([0,1,14,2,3,7,4,5],[0,31,372,99,85,3,104],[0]),([53,0,1,14,2,3,4,5],[0,3,89,2,372,38,94,99],[0,3]),([41,8,0,1,2,3,4,5],[0,27,41,12],[0,1,4]),([0,1,54,2,3,4,5],[2,94,290,261,38,85],[0]),([48,0,1,14,2,3,4,5],[1,2,38,10,41],[0]),([18,8,1,2,3,4,5],[392,27,139,222,92,310,12,94],[0]),([55,11,0,1,2,3,4,5],[2,29,41,216,396,31,104],[0,2,1,4]),([0,1,14,56,2,3,4,5],[2,1,31,148,104,140,13,34,99,335],[0]),([6,18,0,1,2,3,4],[7,15,370,385,31,2,28,104,91],[0,3]),([18,0,1,2,3,7,4,5],[139,370,15,385,28,31,2,27,99,104,273],[0]),([31,11,0,1,2,3,4,5],[30,2,31,28,207,104,366],[0]),([15,18,1,2,3,4,5],[15,392,12,92,139,2,94],[0]),([15,0,42,1,2,3,4,5],[2,41,15,92,244,397,31,3,104,99],[0,2,1,4]),([57,18,0,1,2,3,4,5],[27,30,273,15,12,94,9,109,24,265],[0,3]),([18,0,1,2,3,7,4],[7,370,139,2,31,28,104,99,385],[0,3]),([18,0,1,2,58,3,4,5],[15,273,7,104,26],[0,5,3]),([18,0,1,2,9,3,4,5],[7,139,398,28,31,41,92,2,32,104,12,94,273],[0,3]),([0,1,59,2,3,4,5],[32,1,12,94,37,58,85,86],[0]),([60,0,1,2,3,4,5],[15,399,2,24,211,12,38,86],[1,0,3]),([18,0,1,56,2,3,4,5],[7,143,370,2,31,28,281,34,104,273,11,41,335,265],[0,5,3]),([55,8,0,1,2,3,4,5],[29,41,400,332,2,222,375],[0,2,3,5,1,4]),([16,0,1,61,2,3,4,5],[235,7,1,36,147,381,26,34,41,110,91,38],[0]),([0,1,62,2,3,4,5],[0,94,2,386,325,12,38,85],[0]),([18,0,1,61,2,3,4,5],[7,139,92,235,273,147,330,392,34,11,26,41,38],[0,5,3]),([18,10,0,1,2,3,4,5],[15,30,27,85,86,12,94],[3]),([18,8,0,1,2,3,4,5],[27,392,15,12,0,92,94,110,375,273,265],[0,3]),([13,0,1,2,17,3,4,5],[13,41,126,390,85,15,110,89,109],[0,2,1]),([18,0,1,52,2,3,4,5],[139,1,15,294,126,385,24,34,29,12,94],[0,3]),([11,0,1,2,9,3,5],[41,2,30,216,401],[0,2,3,5,1,4]),([18,14,2,3,4,5],[12,2,316,274],[0]),([48,18,0,1,2,3,4,5],[273,7,1,370,3,15,28,109,41,265],[0,5,3]),([8,0,42,1,2,3,4,5],[41,27,92,242,244,402,2,31,222,90,104,375,12],[0,3,2,5,1,4]),([0,1,14,52,2,3,4,5],[0,1,85,2,99,38,86],[0]),([31,18,0,1,2,3,4,5],[30,28,248,370,31,2,273,265],[0]),([45,0,1,2,3,4,5],[15,32,273,94,12,37,58,85,86],[5,0,4,3]),([63,18,0,1,2,3,4,5],[7,15,392,94,12],[0,3]),([64,0,1,2,3,4,5],[15,403,92,12,38,37,85,86],[1,0,3,5]),([44,18,0,1,2,3,4,5],[28,30,15,273,336,265,34],[0,3,5]),([47,0,1,2,3,4,5],[15,370,7,28,38,37,85,86,31,2],[0,3]),([53,16,0,1,2,3,4,5],[36,122,239,387,85,3,12,94,29],[0]),([36,18,0,1,2,3,4,5],[273,7,1,392,3,139,15,92,41],[0,5,3]),([19,0,1,2,3,7,4],[99,91,27,2,31,104],[0,2,1,4]),([16,10,0,1,2,3,4,5],[15,30,27,91,86,12,94,109],[0]),([0,1,14,2,3,7,4],[2,31,0,91,104,99,58,372],[0]),([65,18,0,1,2,3,4,5],[11,139,385,28,109,159,273],[0,3]),([63,0,1,2,3,4,5],[15,392,7,139,92,38,58,86,94,12],[0,3]),([39,18,0,1,2,3,4,5],[28,392,29,139,334,385,273],[0,3]),([16,0,66,2,3,4,5],[36,94,404,30,381,31,352,91],[3,0]),([0,1,14,61,2,3,4,5],[147,1,0,235,246,386,26,34,91,110,38],[0]),([8,11,1,2,3,4,5],[41,29,2,216,379,12],[0,2,1,4]),([57,16,0,1,2,3,4,5],[27,122,30,94,12,38,200,89,9,109],[0,2]),([67,11,0,1,2,3,4,5],[30,2,99,13,31,104],[0,2,1,4]),([0,1,14,2,9,3,4,5],[132,2,31,0,405,32,3,91,104],[0]),([53,18,0,1,2,3,4,5],[139,273,15,277,3,89,385,30,24],[0,3]),([13,18,1,2,3,4,5],[7,15,370,12,28,31],[0,3]),([18,11,1,2,3,4,5],[370,30,2,31,28,278,94,12],[0,3]),([16,0,1,56,2,3,4,5],[31,7,1,2,107,104,89,34,41,99,335],[0]),([68,18,0,1,2,3,4,5],[28,30,273,385,9,109,265],[0,3]),([0,69,1,2,3,4,5],[2,41,406,407,94,38],[0,2,1,4]),([55,0,1,2,3,4,5],[41,29,400,332,2,94,38],[0,2,3,5,1,4]),([18,11,0,1,2,3,4,5],[30,2,15,28,370,31,12,104,99,366],[0])]
def P_46_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [0,1,2,3,7,9,10,11,12,13,15,24,26,27,28,29,30,31,32,33,34,36,37,38,41,50,58,85,86,89,90,91,92,94,99,104,107,109,110,122,126,132,139,140,143,147,148,157,159,170,200,207,211,216,222,233,235,236,238,239,242,244,246,248,259,261,265,273,274,277,278,279,281,282,286,290,294,300,310,316,317,321,325,330,332,334,335,336,348,352,359,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_9 : checkNodesBT W_46 G_46 fmask_46 P_46_9 autos_46 bk_46_8 9 nodes_46_9 = true := by decide +kernel
def bk_46_9 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_9
set_option maxRecDepth 500000 in
lemma bk_46_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 9 xs.toFinset) bk_46_9 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_8_ok chk_46_9
def nodes_46_10 : List NodeSpec := [([6,0,1,2,3,4],[86,58,41],[0,3,2,5,1,4]),([0,1,2,3,7,4,5],[91,58,86,12,94,38],[0,3,2,5,1,4]),([8,0,1,2,3,4,5],[91,41,12,378,37,94,38],[0,2,3,5,1,4]),([0,1,2,9,3,4,5],[41,91,408,12,94,38],[0,3,2,5,1,4]),([10,0,1,2,3,4,5],[91,12,367,86,94,38],[0,2,1,4,3,5]),([11,0,1,2,3,4,5],[58,2,41,377,12,94,38,85],[0,2,3,5,1,4]),([0,1,2,3,7,4],[58,91,86],[0,3,2,5,1,4]),([12,0,1,2,3,4,5],[91,12,2,86,94,38,58],[0,2,1,4,3,5]),([13,0,1,2,3,4,5],[12,58,41,390,94,38,85],[0,2,1,4,3,5]),([0,1,14,2,3,4,5],[12,94,386,372,2,38,58,85],[0]),([15,0,1,2,3,4,5],[12,91,41,37,368,94,38],[0,2,1,4]),([16,0,1,2,3,4,5],[94,12,381,387,31,38,58,85],[0,2]),([0,1,2,17,3,4,5],[85,41,37,86,12,94,38],[0,3,2,5,1,4]),([18,0,1,2,3,4,5],[94,12,392,370,385,38,85],[0,3])]
def P_46_10 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [2,12,31,37,38,41,58,85,86,91,94,367,368,370,372,377,378,381,385,386,387,390,392,408]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_10 : checkNodesBT W_46 G_46 fmask_46 P_46_10 autos_46 bk_46_9 10 nodes_46_10 = true := by decide +kernel
def bk_46_10 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_10
set_option maxRecDepth 500000 in
lemma bk_46_10_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 10 xs.toFinset) bk_46_10 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_9_ok chk_46_10
def nodes_46_11 : List NodeSpec := [([0,1,2,3,4,5],[37,58,86],[0,3,2,5,1,4])]
def P_46_11 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 R_46 slices_46 ps_46 [37,58,86]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_46_11 : checkNodesBT W_46 G_46 fmask_46 P_46_11 autos_46 bk_46_10 11 nodes_46_11 = true := by decide +kernel
def bk_46_11 : BT (List (List Nat)) := buildBucketsBT W_46 nodes_46_11
set_option maxRecDepth 500000 in
lemma bk_46_11_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_46 11 xs.toFinset) bk_46_11 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound slices_46_ok) autos_46_ok bk_46_10_ok chk_46_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_46_ok : forestRootCheck R_46 G_46 [(VAR 0,15,14),(VAR 1,15,13),(VAR 2,15,11),(VAR 3,15,7),(VAR 4,27,11),(VAR 5,55,23)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_46_in : bucketContainsBT bk_46_11 R_46 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_46 : Lower R_46 G_46 12 := lower_of_forestBT root_46_ok bk_46_11_ok root_46_in
def wit : List PEqualNP.CircuitLowerBounds.Gate := [
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 12]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 15]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 14]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 17]⟩
]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by intro g hg; simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4269834240 * 2 ^ 32 + 3892346880) ||| ((4269834240 * 2 ^ 32 + 3892346880) <<< 64)).testBit r.val := by decide +kernel
lemma root_eq : G_46 = ((4269834240 * 2 ^ 32 + 3892346880) ||| ((4269834240 * 2 ^ 32 + 3892346880) <<< 64)) := by decide
lemma low_root : Lower (varsOf 63) ((4269834240 * 2 ^ 32 + 3892346880) ||| ((4269834240 * 2 ^ 32 + 3892346880) <<< 64)) 12 := root_eq ▸ low_46
end PEqualNP.Outside.L_meta_12046
theorem PEqualNP.Outside.L_meta_12046 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269834240 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269834240 * 2 ^ 32 + 3892346880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_12046.table2_of_lower (4269834240 * 2 ^ 32 + 3892346880) (by decide) (by decide) (by decide) (by decide) 12 PEqualNP.Outside.L_meta_12046.low_root PEqualNP.Outside.L_meta_12046.wit PEqualNP.Outside.L_meta_12046.wo (by decide) PEqualNP.Outside.L_meta_12046.wit_mono PEqualNP.Outside.L_meta_12046.wit_eval s hcs
