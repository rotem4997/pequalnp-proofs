import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_12068
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
def hashWs (nb : Nat) (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) % nb
def bucketContains (buckets : Array (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (buckets.getD (hashWs buckets.size s) []).contains s
def closeChild (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContains prevBuckets (ws.map (permWord sw)))
lemma closeChild_sound {raw T pools autos prevBuckets k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T k xs.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChild pools autos prevBuckets k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContains at hhit
    simp only [Array.getD, List.contains_eq_mem, decide_eq_true_eq] at hhit
    split at hhit
    next hlt_b =>
      have himp := hPrev _ hlt_b _ hhit
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
        · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
              Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
      have hfix_r : permWord sw.reverse T = T := by
        conv_lhs => rw [← hfix]
        exact hinv_w T hT
      have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [permWord_eq_renameW sw hsv x (hlt x hx)]
        exact renameW_lt _ x
      have hrot := rotate_impossible himp sw.reverse hvr hT hfix_r hmap_lt
      have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
        exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
      rwa [hback] at hrot
    next => simp at hhit
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
def evalMove (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild pools autos prevBuckets (cap - 1) rest (d, a.1, b.1)
def testPair (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMove cap n fmask ws cov pools autos prevBuckets d a b z
  go false false && go true false && go false true && go true true
def testAll (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPair cap n fmask ws cov pools autos prevBuckets a b)) &&
      testAll cap n fmask ws cov pools autos prevBuckets bs
lemma evalMove_sound {raw T pos neg ws pools autos prevBuckets cap a b d ka kb}
    (hT : T < 2^128)
    (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (hd : d < 4)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (hnz : (dbin d a b).1 ≠ 0) (hfr : (dbin d a b).1 ∉ ws.map Prod.fst)
    (test : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets
      d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => hfr ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact hlt w (sub.subset hw)
  have hfr_b : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
    exact hfr (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, delTwo_len ws a b ka kb ha hb ne, Nat.add_comm 1]
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
  unfold evalMove at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  exact closeChild_sound (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT hPools hAutos hPrev ndc hltc test k hk h
lemma testAll_pair {cap n fmask ws cov pools autos prevBuckets l}
    (h : testAll cap n fmask ws cov pools autos prevBuckets l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets a b d = true) ∨
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAll, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma node_sound {raw T pos neg ws pools autos prevBuckets cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (checks : cap = 0 ∨ testAll cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0; intro k hk h
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
      (ht : testPair cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPair, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMove_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAll_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
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
lemma lower_of_forest {roots T cap} {topBuckets : Array (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : ∀ i (hi : i < topBuckets.size), ∀ xs ∈ topBuckets[i], Impossible T cap xs.toFinset)
    (hRoot : bucketContains topBuckets roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContains Array.getD at hRoot
    dsimp only at hRoot
    split at hRoot
    next hi => exact hTop _ hi _ (List.contains_iff_mem.mp hRoot)
    next => simp at hRoot
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def buildWires (base : List Decor) (steps : List (Nat × Nat × Nat)) : Array Decor :=
  steps.foldl (fun arr s =>
    let a := arr.getD s.2.1 (0, 0, 0)
    let b := arr.getD s.2.2 (0, 0, 0)
    arr.push (dbin s.1 a b)) base.toArray
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma buildWires_faithful {pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    ∀ x ∈ (buildWires base steps).toList, faithful pos neg x ∧ x.1 < 2^128 := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hstep : ∀ (arr : Array Decor) (s : Nat × Nat × Nat),
      (∀ x ∈ arr.toList, faithful pos neg x ∧ x.1 < 2^128) →
      ∀ x ∈ (arr.push (dbin s.1 (arr.getD s.2.1 (0, 0, 0)) (arr.getD s.2.2 (0, 0, 0)))).toList,
        faithful pos neg x ∧ x.1 < 2^128 := by
    intro arr s harr x hx
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact harr x hx
    · have hget (i : Nat) : faithful pos neg (arr.getD i (0, 0, 0)) ∧ (arr.getD i (0, 0, 0)).1 < 2^128 := by
        unfold Array.getD
        split
        next hi => exact harr arr[i] (Array.getElem_mem_toList hi)
        next => exact hdef
      exact ⟨faithful_bin s.1 (hget s.2.1).1 (hget s.2.2).1, bin_lt s.1 _ _ (hget s.2.1).2 (hget s.2.2).2⟩
  unfold buildWires
  have hinit : ∀ x ∈ base.toArray.toList, faithful pos neg x ∧ x.1 < 2^128 := by simpa using hbase
  clear hbase
  generalize base.toArray = acc at hinit ⊢
  induction steps generalizing acc with
  | nil => exact hinit
  | cons s ss ih => exact ih _ (hstep acc s hinit)
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
lemma array_forall_of_list {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) :
    ∀ i (hi : i < l.toArray.size), P l.toArray[i] :=
  fun i hi => h l.toArray[i] (Array.getElem_mem_toList hi)
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat
def buildPools (W : Array Decor) (raw : List Nat) (slices : Array (Nat × Nat))
    (pspecs : List PoolSpec) : Array (Option BoundPool) :=
  (pspecs.map fun (slIdx, chIdxs) =>
    match slices[slIdx]? with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
      materialize raw cs dom lb).toArray
lemma buildPools_sound {W : Array Decor} {raw T} {slices : Array (Nat × Nat)} {pspecs : List PoolSpec}
    (hSlices : ∀ i (hi : i < slices.size), Slice raw T slices[i].1 slices[i].2) :
    ∀ i (hi : i < (buildPools W raw slices pspecs).size),
      ∀ c, (buildPools W raw slices pspecs)[i] = some c → ValidPool raw T c := by
  intro i hi c hc
  unfold buildPools at hi hc
  have hmem : some c ∈ pspecs.map (fun (slIdx, chIdxs) =>
      match slices[slIdx]? with
      | none => none
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
        materialize raw cs dom lb) := by
    rw [← hc]
    exact Array.getElem_mem_toList hi
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp hmem
  cases hget_sl : slices[slIdx]? with
  | none => simp [hget_sl] at hmat
  | some sl =>
    simp only [hget_sl] at hmat
    have ⟨hsi, hval⟩ := Array.getElem?_eq_some_iff.mp hget_sl
    exact materialize_sound (hval ▸ hSlices slIdx hsi) hmat
def checkNode (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  let vals := ws.map Prod.fst
  let pools := ns.2.1.filterMap fun pIdx => poolTable.getD pIdx none
  let nodeAutos := ns.2.2.filterMap fun aIdx => autosTable[aIdx]?
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAll k ws.length fmask ws (coverage ws) pools nodeAutos prevBuckets ws)
def checkNodes (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNode W T fmask poolTable autosTable prevBuckets k)
lemma checkNode_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (ok : checkNode W T (fullMask pos.length) poolTable autosTable prevBuckets k ns = true) :
    Impossible T k ((ns.1.map fun idx => (W.getD idx (0, 0, 0)).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (W.getD idx (0, 0, 0)) ∧ (W.getD idx (0, 0, 0)).1 < 2^128 := by
    unfold Array.getD; split
    next hi => exact hW W[idx] (Array.getElem_mem_toList hi)
    next => exact hdef
  unfold checkNode at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (W.getD idx (0, 0, 0)).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply node_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun c hc => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hc
      unfold Array.getD at hmat
      split at hmat
      next hi => exact hPoolTable pIdx hi c hmat
      next => simp at hmat)
    (fun sw hsw => by
      obtain ⟨aIdx, _, ha⟩ := List.mem_filterMap.mp hsw
      have ⟨hi, hval⟩ := Array.getElem?_eq_some_iff.mp ha
      exact hAutos sw (hval ▸ Array.getElem_mem_toList hi))
    hPrev ok.2
def nodeVals (W : Array Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (W.getD idx (0, 0, 0)).1)
def insertBucket (buckets : Array (List (List Nat))) (xs : List Nat) : Array (List (List Nat)) :=
  let idx := hashWs buckets.size xs
  if h : idx < buckets.size then
    let b := buckets[idx]
    if b.contains xs then buckets else buckets.set idx (xs :: b) h
  else buckets
def buildBuckets (nb : Nat) (W : Array Decor) (nodes : List NodeSpec) : Array (List (List Nat)) :=
  nodes.foldl (fun acc ns => insertBucket acc (nodeVals W ns)) (Array.replicate nb [])
lemma insertBucket_mem {bks : Array (List (List Nat))} {P : List Nat → Prop} {xs : List Nat}
    (hb : ∀ i (hi : i < bks.size), ∀ ys ∈ bks[i], P ys) (hxs : P xs) :
    ∀ i (hi : i < (insertBucket bks xs).size), ∀ ys ∈ (insertBucket bks xs)[i], P ys := by
  unfold insertBucket
  dsimp only
  split
  next hidx =>
    split
    · exact hb
    · intro i hi ys hys
      rw [Array.size_set] at hi
      rw [Array.getElem_set] at hys
      split at hys
      next =>
        rcases List.mem_cons.mp hys with rfl | hys'
        · exact hxs
        · exact hb _ hidx ys hys'
      next => exact hb i hi ys hys
  next => exact hb
lemma buildBuckets_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k nb}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (hNodes : checkNodes W T (fullMask pos.length) poolTable autosTable prevBuckets k nodes = true) :
    ∀ i (hi : i < (buildBuckets nb W nodes).size), ∀ xs ∈ (buildBuckets nb W nodes)[i], Impossible T k xs.toFinset := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeVals W ns).toFinset := fun ns hns => by
    unfold nodeVals
    rw [sortNats_toFinset]
    exact checkNode_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBuckets
  have hinit : ∀ i (hi : i < (Array.replicate nb ([] : List (List Nat))).size),
      ∀ xs ∈ (Array.replicate nb ([] : List (List Nat)))[i], Impossible T k xs.toFinset := by
    intro i hi xs hxs; simp at hxs
  generalize Array.replicate nb ([] : List (List Nat)) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      (insertBucket acc (nodeVals W ns)) (insertBucket_mem hinit (hmem ns (List.mem_cons_self ..)))
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
def G_0 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_0 : List Nat := varsOf 22
def pos_0 : List Nat := [6,6,18,18,20,20,6,18,20]
def neg_0 : List Nat := [4,2,16,2,16,4,16,4,2]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : Array Decor := buildWires base_0 steps_0
def autos_0 : Array (List (Nat × Nat)) := #[]
def slicesL_0 : List (Nat × Nat) := []
def slices_0 : Array (Nat × Nat) := slicesL_0.toArray
def ps_0 : List PoolSpec := []
def P_0 : Array (Option BoundPool) := buildPools W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_0_ok : ∀ x ∈ W_0.toList, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := buildWires_faithful base_0_ok
lemma autos_0_ok : ∀ sw ∈ autos_0.toList, swapsValid sw = true ∧ permWord sw G_0 = G_0 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma slices_0_ok : ∀ i (hi : i < slices_0.size), Slice R_0 G_0 slices_0[i].1 slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma P_0_ok : ∀ i (hi : i < P_0.size), ∀ c, P_0[i] = some c → ValidPool R_0 G_0 c := buildPools_sound slices_0_ok
def bk_0_init : Array (List (List Nat)) := #[]
lemma bk_0_init_ok : ∀ i (hi : i < bk_0_init.size), ∀ xs ∈ bk_0_init[i], Impossible G_0 (0 - 1) xs.toFinset := by intro i hi; simp [bk_0_init] at hi
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_0
lemma bk_0_0_ok : ∀ i (hi : i < bk_0_0.size), ∀ xs ∈ bk_0_0[i], Impossible G_0 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_1
lemma bk_0_1_ok : ∀ i (hi : i < bk_0_1.size), ∀ xs ∈ bk_0_1[i], Impossible G_0 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_2
lemma bk_0_2_ok : ∀ i (hi : i < bk_0_2.size), ∀ xs ∈ bk_0_2[i], Impossible G_0 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_3
lemma bk_0_3_ok : ∀ i (hi : i < bk_0_3.size), ∀ xs ∈ bk_0_3[i], Impossible G_0 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContains bk_0_3 R_0 = true := by decide +kernel
lemma low_0 : Lower R_0 G_0 4 := lower_of_forest root_0_ok bk_0_3_ok root_0_in
def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(0,3),(0,4),(0,2),(0,1)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0
def G_2 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def R_2 : List Nat := varsOf 19
lemma low_2_ok : carryOK [(0,2),(0,1)] R_2 G_2 R_0 G_0 = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 4 := carry_of low_2_ok low_0
def G_3 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_3 : List Nat := varsOf 21
lemma low_3_ok : carryOK [(0,1)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0
def G_4 : Nat := 0xffffff00ff000000ffffff00ff000000
def R_4 : List Nat := varsOf 56
lemma low_4_ok : carryOK [(2,4),(2,5),(1,3)] R_4 G_4 R_0 G_0 = true := by decide +kernel
lemma low_4 : Lower R_4 G_4 4 := carry_of low_4_ok low_0
def G_5 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
def R_5 : List Nat := varsOf 30
lemma low_5_ok : liftCheck 0 8 R_5 G_5 R_0 G_0 [(VAR 3,14,6)] = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 5 := lift_of low_5_ok low_0
def G_6 : Nat := 0xfcfcc0c0fcfc0000fcfcc0c0fcfc0000
def R_6 : List Nat := varsOf 54
lemma low_6_ok : liftCheck 0 32 R_6 G_6 R_0 G_0 [(VAR 5,38,6)] = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 5 := lift_of low_6_ok low_0
def G_7 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
def R_7 : List Nat := varsOf 23
def pos_7 : List Nat := [3,3,5,5,6,6,17,17,18,18,20,20,3,3,5,5,6,6,17,17,18,18,20,20]
def neg_7 : List Nat := [2,1,4,1,4,2,16,1,16,2,16,4,4,16,2,16,1,16,2,4,1,4,1,2]
def fmask_7 : Nat := fullMask 24
def base_7 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffff0000ffff0000ffff0000ffff0000,0xfc0fc0,0x2a540)]
def steps_7 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_7 : Array Decor := buildWires base_7 steps_7
def autos_7 : Array (List (Nat × Nat)) := #[[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def slicesL_7 : List (Nat × Nat) := [(subcube 2 0,4),(subcube 1 0,4),(subcube 16 0,4),(subcube 4 0,4)]
def slices_7 : Array (Nat × Nat) := slicesL_7.toArray
def ps_7 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_7 : Array (Option BoundPool) := buildPools W_7 R_7 slices_7 ps_7
lemma gp_7 : goodPairs G_7 pos_7 neg_7 := goodPairs_of (by decide +kernel)
lemma base_7_ok : ∀ x ∈ base_7, faithful pos_7 neg_7 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_7_ok : ∀ x ∈ W_7.toList, faithful pos_7 neg_7 x ∧ x.1 < 2^128 := buildWires_faithful base_7_ok
lemma autos_7_ok : ∀ sw ∈ autos_7.toList, swapsValid sw = true ∧ permWord sw G_7 = G_7 := autos_of (by decide +kernel)
lemma sl_7_0_ok : sliceDirectCheck 2 0 0 R_7 G_7 R_3 G_3 = true := by decide +kernel
lemma sl_7_0 : Slice R_7 G_7 (subcube 2 0) 4 := slice_direct sl_7_0_ok low_3
lemma sl_7_1_ok : sliceDirectCheck 1 0 0 R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma sl_7_1 : Slice R_7 G_7 (subcube 1 0) 4 := slice_direct sl_7_1_ok low_0
lemma sl_7_2_ok : sliceDirectCheck 16 0 0 R_7 G_7 R_1 G_1 = true := by decide +kernel
lemma sl_7_2 : Slice R_7 G_7 (subcube 16 0) 4 := slice_direct sl_7_2_ok low_1
lemma sl_7_3_ok : sliceDirectCheck 4 0 0 R_7 G_7 R_2 G_2 = true := by decide +kernel
lemma sl_7_3 : Slice R_7 G_7 (subcube 4 0) 4 := slice_direct sl_7_3_ok low_2
set_option maxRecDepth 200000 in
lemma slices_7_ok : ∀ i (hi : i < slices_7.size), Slice R_7 G_7 slices_7[i].1 slices_7[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_7 G_7 p.1 p.2) (forall_cons sl_7_0 (forall_cons sl_7_1 (forall_cons sl_7_2 (forall_cons sl_7_3 (fun _ h => (List.not_mem_nil h).elim)))))
lemma P_7_ok : ∀ i (hi : i < P_7.size), ∀ c, P_7[i] = some c → ValidPool R_7 G_7 c := buildPools_sound slices_7_ok
def bk_7_init : Array (List (List Nat)) := #[]
lemma bk_7_init_ok : ∀ i (hi : i < bk_7_init.size), ∀ xs ∈ bk_7_init[i], Impossible G_7 (0 - 1) xs.toFinset := by intro i hi; simp [bk_7_init] at hi
def nodes_7_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_0 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_init 0 nodes_7_0 = true := by decide +kernel
def bk_7_0 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_0
lemma bk_7_0_ok : ∀ i (hi : i < bk_7_0.size), ∀ xs ∈ bk_7_0[i], Impossible G_7 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_init_ok chk_7_0
def nodes_7_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_1 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_0 1 nodes_7_1 = true := by decide +kernel
def bk_7_1 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_1
lemma bk_7_1_ok : ∀ i (hi : i < bk_7_1.size), ∀ xs ∈ bk_7_1[i], Impossible G_7 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_0_ok chk_7_1
def nodes_7_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_2 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_1 2 nodes_7_2 = true := by decide +kernel
def bk_7_2 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_2
lemma bk_7_2_ok : ∀ i (hi : i < bk_7_2.size), ∀ xs ∈ bk_7_2[i], Impossible G_7 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_1_ok chk_7_2
def nodes_7_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_3 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_2 3 nodes_7_3 = true := by decide +kernel
def bk_7_3 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_3
lemma bk_7_3_ok : ∀ i (hi : i < bk_7_3.size), ∀ xs ∈ bk_7_3[i], Impossible G_7 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_2_ok chk_7_3
def nodes_7_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_4 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_3 4 nodes_7_4 = true := by decide +kernel
def bk_7_4 : Array (List (List Nat)) := buildBuckets 2 W_7 nodes_7_4
lemma bk_7_4_ok : ∀ i (hi : i < bk_7_4.size), ∀ xs ∈ bk_7_4[i], Impossible G_7 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_3_ok chk_7_4
def nodes_7_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_5 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_4 5 nodes_7_5 = true := by decide +kernel
def bk_7_5 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_5
lemma bk_7_5_ok : ∀ i (hi : i < bk_7_5.size), ∀ xs ∈ bk_7_5[i], Impossible G_7 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_4_ok chk_7_5
def nodes_7_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_6 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_5 6 nodes_7_6 = true := by decide +kernel
def bk_7_6 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_6
lemma bk_7_6_ok : ∀ i (hi : i < bk_7_6.size), ∀ xs ∈ bk_7_6[i], Impossible G_7 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_5_ok chk_7_6
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck R_7 G_7 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContains bk_7_6 R_7 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 7 := lower_of_forest root_7_ok bk_7_6_ok root_7_in
def G_8 : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
def R_8 : List Nat := varsOf 30
def pos_8 : List Nat := [10,10,12,12,14,22,22,22,24,24,26,28,10,10,10,12,12,12,22,24,24,24]
def neg_8 : List Nat := [8,2,8,4,6,20,18,6,16,8,18,20,6,18,20,6,18,20,8,6,18,20]
def fmask_8 : Nat := fullMask 22
def base_8 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x474f3,0x19b4d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x788fc,0x2ad8b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3bff1f,0x40205),(0xffff0000ffff0000ffff0000ffff0000,0x3c0fe0,0x336d60)]
def steps_8 : List (Nat × Nat × Nat) := [(3,0,2),(2,0,1),(2,0,2),(1,0,2),(1,0,1),(0,0,2),(0,0,1),(0,1,7),(3,0,1),(1,5,3),(1,9,1),(3,5,3),(3,1,7),(3,9,1),(3,10,8)]
def W_8 : Array Decor := buildWires base_8 steps_8
def autos_8 : Array (List (Nat × Nat)) := #[[],[(2,4)],[(1,2)],[(1,4),(1,2)],[(1,2),(1,4)],[(1,4)]]
def slicesL_8 : List (Nat × Nat) := []
def slices_8 : Array (Nat × Nat) := slicesL_8.toArray
def ps_8 : List PoolSpec := []
def P_8 : Array (Option BoundPool) := buildPools W_8 R_8 slices_8 ps_8
lemma gp_8 : goodPairs G_8 pos_8 neg_8 := goodPairs_of (by decide +kernel)
lemma base_8_ok : ∀ x ∈ base_8, faithful pos_8 neg_8 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_8_ok : ∀ x ∈ W_8.toList, faithful pos_8 neg_8 x ∧ x.1 < 2^128 := buildWires_faithful base_8_ok
lemma autos_8_ok : ∀ sw ∈ autos_8.toList, swapsValid sw = true ∧ permWord sw G_8 = G_8 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma slices_8_ok : ∀ i (hi : i < slices_8.size), Slice R_8 G_8 slices_8[i].1 slices_8[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_8 G_8 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma P_8_ok : ∀ i (hi : i < P_8.size), ∀ c, P_8[i] = some c → ValidPool R_8 G_8 c := buildPools_sound slices_8_ok
def bk_8_init : Array (List (List Nat)) := #[]
lemma bk_8_init_ok : ∀ i (hi : i < bk_8_init.size), ∀ xs ∈ bk_8_init[i], Impossible G_8 (0 - 1) xs.toFinset := by intro i hi; simp [bk_8_init] at hi
def nodes_8_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_8_0 : checkNodes W_8 G_8 fmask_8 P_8 autos_8 bk_8_init 0 nodes_8_0 = true := by decide +kernel
def bk_8_0 : Array (List (List Nat)) := buildBuckets 1 W_8 nodes_8_0
lemma bk_8_0_ok : ∀ i (hi : i < bk_8_0.size), ∀ xs ∈ bk_8_0[i], Impossible G_8 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_8 W_8_ok P_8_ok autos_8_ok bk_8_init_ok chk_8_0
def nodes_8_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_8_1 : checkNodes W_8 G_8 fmask_8 P_8 autos_8 bk_8_0 1 nodes_8_1 = true := by decide +kernel
def bk_8_1 : Array (List (List Nat)) := buildBuckets 1 W_8 nodes_8_1
lemma bk_8_1_ok : ∀ i (hi : i < bk_8_1.size), ∀ xs ∈ bk_8_1[i], Impossible G_8 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_8 W_8_ok P_8_ok autos_8_ok bk_8_0_ok chk_8_1
def nodes_8_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_8_2 : checkNodes W_8 G_8 fmask_8 P_8 autos_8 bk_8_1 2 nodes_8_2 = true := by decide +kernel
def bk_8_2 : Array (List (List Nat)) := buildBuckets 1 W_8 nodes_8_2
lemma bk_8_2_ok : ∀ i (hi : i < bk_8_2.size), ∀ xs ∈ bk_8_2[i], Impossible G_8 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_8 W_8_ok P_8_ok autos_8_ok bk_8_1_ok chk_8_2
def nodes_8_3 : List NodeSpec := [([6,4,1,3],[],[]),([0,11,2,3],[],[]),([5,12,2,3],[],[0]),([0,1,2,13],[],[]),([0,14,2,3],[],[]),([0,1,15,2],[],[]),([16,0,2,3],[],[]),([17,0,2,3],[],[]),([10,8,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_8_3 : checkNodes W_8 G_8 fmask_8 P_8 autos_8 bk_8_2 3 nodes_8_3 = true := by decide +kernel
def bk_8_3 : Array (List (List Nat)) := buildBuckets 4 W_8 nodes_8_3
lemma bk_8_3_ok : ∀ i (hi : i < bk_8_3.size), ∀ xs ∈ bk_8_3[i], Impossible G_8 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_8 W_8_ok P_8_ok autos_8_ok bk_8_2_ok chk_8_3
def nodes_8_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([6,0,1,2,3],[],[0]),([0,1,2,7,3],[],[0,1]),([0,1,8,2,3],[],[0]),([9,0,1,2,3],[],[0,1]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_8_4 : checkNodes W_8 G_8 fmask_8 P_8 autos_8 bk_8_3 4 nodes_8_4 = true := by decide +kernel
def bk_8_4 : Array (List (List Nat)) := buildBuckets 3 W_8 nodes_8_4
lemma bk_8_4_ok : ∀ i (hi : i < bk_8_4.size), ∀ xs ∈ bk_8_4[i], Impossible G_8 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_8 W_8_ok P_8_ok autos_8_ok bk_8_3_ok chk_8_4
def nodes_8_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_8_5 : checkNodes W_8 G_8 fmask_8 P_8 autos_8 bk_8_4 5 nodes_8_5 = true := by decide +kernel
def bk_8_5 : Array (List (List Nat)) := buildBuckets 1 W_8 nodes_8_5
lemma bk_8_5_ok : ∀ i (hi : i < bk_8_5.size), ∀ xs ∈ bk_8_5[i], Impossible G_8 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_8 W_8_ok P_8_ok autos_8_ok bk_8_4_ok chk_8_5
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_8_ok : forestRootCheck R_8 G_8 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_8_in : bucketContains bk_8_5 R_8 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 6 := lower_of_forest root_8_ok bk_8_5_ok root_8_in
def G_9 : Nat := 0xe800e800e800e800e800e800e800e800
def R_9 : List Nat := varsOf 15
lemma low_9_ok : carryOK [(0,4),(0,2),(0,1)] R_9 G_9 R_5 G_5 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 5 := carry_of low_9_ok low_5
def G_10 : Nat := 0xe8e8e8e800000000e8e8e8e800000000
def R_10 : List Nat := varsOf 39
lemma low_10_ok : carryOK [(3,5),(0,3),(0,4),(0,2),(0,1)] R_10 G_10 R_5 G_5 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 5 := carry_of low_10_ok low_5
def G_11 : Nat := 0xee008800ee008800ee008800ee008800
def R_11 : List Nat := varsOf 27
lemma low_11_ok : carryOK [(0,2),(0,1)] R_11 G_11 R_5 G_5 = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 5 := carry_of low_11_ok low_5
def G_12 : Nat := 0xeeee8888eeee0000eeee8888eeee0000
def R_12 : List Nat := varsOf 51
lemma low_12_ok : carryOK [(0,2),(0,1)] R_12 G_12 R_6 G_6 = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 5 := carry_of low_12_ok low_6
def G_13 : Nat := 0xfa00a000fa00a000fa00a000fa00a000
def R_13 : List Nat := varsOf 29
lemma low_13_ok : carryOK [(0,1)] R_13 G_13 R_5 G_5 = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 5 := carry_of low_13_ok low_5
def G_14 : Nat := 0xfafaa0a0fafa0000fafaa0a0fafa0000
def R_14 : List Nat := varsOf 53
lemma low_14_ok : carryOK [(0,1)] R_14 G_14 R_6 G_6 = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 5 := carry_of low_14_ok low_6
def G_15 : Nat := 0xfe80fe80fe80fe80fe80fe80fe80fe80
def R_15 : List Nat := varsOf 15
lemma low_15_ok : carryOK [(0,4),(0,2),(0,1)] R_15 G_15 R_8 G_8 = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 6 := carry_of low_15_ok low_8
def G_16 : Nat := 0xff88ee00ff88ee00ff88ee00ff88ee00
def R_16 : List Nat := varsOf 27
lemma low_16_ok : carryOK [(0,2),(0,1)] R_16 G_16 R_8 G_8 = true := by decide +kernel
lemma low_16 : Lower R_16 G_16 6 := carry_of low_16_ok low_8
def G_17 : Nat := 0xffa0fa00ffa0fa00ffa0fa00ffa0fa00
def R_17 : List Nat := varsOf 29
lemma low_17_ok : carryOK [(0,1)] R_17 G_17 R_8 G_8 = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 6 := carry_of low_17_ok low_8
def G_18 : Nat := 0xffaaff00ff000000ffaaff00ff000000
def R_18 : List Nat := varsOf 57
lemma low_18_ok : carryOK [(1,2),(2,4),(2,3),(0,1),(0,5)] R_18 G_18 R_6 G_6 = true := by decide +kernel
lemma low_18 : Lower R_18 G_18 5 := carry_of low_18_ok low_6
def G_19 : Nat := 0xffccff00ff000000ffccff00ff000000
def R_19 : List Nat := varsOf 58
lemma low_19_ok : carryOK [(1,2),(2,4),(2,3),(1,5)] R_19 G_19 R_6 G_6 = true := by decide +kernel
lemma low_19 : Lower R_19 G_19 5 := carry_of low_19_ok low_6
def G_20 : Nat := 0xfff0ff00ff000000fff0ff00ff000000
def R_20 : List Nat := varsOf 60
lemma low_20_ok : carryOK [(1,4),(2,5),(1,3)] R_20 G_20 R_6 G_6 = true := by decide +kernel
lemma low_20 : Lower R_20 G_20 5 := carry_of low_20_ok low_6
def G_21 : Nat := 0xe800e80000000000e800e80000000000
def R_21 : List Nat := varsOf 47
lemma low_21_ok : liftCheck 0 8 R_21 G_21 R_10 G_10 [(VAR 3,43,35)] = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 6 := lift_of low_21_ok low_10
def G_22 : Nat := 0xfc00c000fc000000fc00c000fc000000
def R_22 : List Nat := varsOf 62
lemma low_22_ok : liftCheck 0 8 R_22 G_22 R_6 G_6 [(VAR 3,26,18)] = true := by decide +kernel
lemma low_22 : Lower R_22 G_22 6 := lift_of low_22_ok low_6
def G_23 : Nat := 0xfe80e800fe80e800fe80e800fe80e800
def R_23 : List Nat := varsOf 31
def pos_23 : List Nat := [11,11,11,13,13,13,14,14,14,15,23,23,23,23,25,25,25,26,26,26,27,28,28,28,29,30,11,11,11,11,11,11,13,13,13,13,13,13,14,14,14,14,14,14,23,23,23,23,25,25,25,25,25,25,26,26,26,26,26,26,28,28,28,28,28,28]
def neg_23 : List Nat := [10,9,3,12,9,5,12,10,6,7,22,21,19,7,24,17,9,24,18,10,19,24,20,12,21,22,7,12,19,21,22,24,7,10,19,21,22,24,7,9,19,21,22,24,9,10,12,24,7,10,12,19,21,22,7,9,12,19,21,22,7,9,10,19,21,22]
def fmask_23 : Nat := fullMask 66
def base_23 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3ff03ffd11fe3f,0x1b6d913cd3511ba36),(0xcccccccccccccccccccccccccccccccc,0xfc0ffc0fe1e3fc7,0x2da6b2557561c3785),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3f000ffff03e03ff8,0x31d7546596fc02f68),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffff0fffffffc3ff,0x6186f8a288ab40db),(0xffff0000ffff0000ffff0000ffff0000,0x3fffff00003fffc00,0x38e388f3cf376dc00)]
def steps_23 : List (Nat × Nat × Nat) := [(0,0,1),(0,2,4),(1,5,6)]
def W_23 : Array Decor := buildWires base_23 steps_23
def autos_23 : Array (List (Nat × Nat)) := #[[],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def slicesL_23 : List (Nat × Nat) := [(subcube 2 0,5),(subcube 16 0,5),(subcube 0 4,6),(subcube 4 0,5),(subcube 0 16,6),(subcube 0 1,6),(subcube 1 0,5),(subcube 0 2,6),(subcube 0 8,7),(subcube 2 8,4)]
def slices_23 : Array (Nat × Nat) := slicesL_23.toArray
def ps_23 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[(0,2,4)]),(6,[]),(7,[]),(2,[(0,0,1)]),(5,[]),(8,[]),(9,[]),(4,[(0,0,1)])]
def P_23 : Array (Option BoundPool) := buildPools W_23 R_23 slices_23 ps_23
lemma gp_23 : goodPairs G_23 pos_23 neg_23 := goodPairs_of (by decide +kernel)
lemma base_23_ok : ∀ x ∈ base_23, faithful pos_23 neg_23 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_23_ok : ∀ x ∈ W_23.toList, faithful pos_23 neg_23 x ∧ x.1 < 2^128 := buildWires_faithful base_23_ok
lemma autos_23_ok : ∀ sw ∈ autos_23.toList, swapsValid sw = true ∧ permWord sw G_23 = G_23 := autos_of (by decide +kernel)
lemma sl_23_0_ok : sliceDirectCheck 2 0 0 R_23 G_23 R_13 G_13 = true := by decide +kernel
lemma sl_23_0 : Slice R_23 G_23 (subcube 2 0) 5 := slice_direct sl_23_0_ok low_13
lemma sl_23_1_ok : sliceDirectCheck 16 0 0 R_23 G_23 R_9 G_9 = true := by decide +kernel
lemma sl_23_1 : Slice R_23 G_23 (subcube 16 0) 5 := slice_direct sl_23_1_ok low_9
lemma sl_23_2_ok : sliceDirectCheck 0 4 0 R_23 G_23 R_16 G_16 = true := by decide +kernel
lemma sl_23_2 : Slice R_23 G_23 (subcube 0 4) 6 := slice_direct sl_23_2_ok low_16
lemma sl_23_3_ok : sliceDirectCheck 4 0 0 R_23 G_23 R_11 G_11 = true := by decide +kernel
lemma sl_23_3 : Slice R_23 G_23 (subcube 4 0) 5 := slice_direct sl_23_3_ok low_11
lemma sl_23_4_ok : sliceDirectCheck 0 16 0 R_23 G_23 R_15 G_15 = true := by decide +kernel
lemma sl_23_4 : Slice R_23 G_23 (subcube 0 16) 6 := slice_direct sl_23_4_ok low_15
lemma sl_23_5_ok : sliceDirectCheck 0 1 0 R_23 G_23 R_8 G_8 = true := by decide +kernel
lemma sl_23_5 : Slice R_23 G_23 (subcube 0 1) 6 := slice_direct sl_23_5_ok low_8
lemma sl_23_6_ok : sliceDirectCheck 1 0 0 R_23 G_23 R_5 G_5 = true := by decide +kernel
lemma sl_23_6 : Slice R_23 G_23 (subcube 1 0) 5 := slice_direct sl_23_6_ok low_5
lemma sl_23_7_ok : sliceDirectCheck 0 2 0 R_23 G_23 R_17 G_17 = true := by decide +kernel
lemma sl_23_7 : Slice R_23 G_23 (subcube 0 2) 6 := slice_direct sl_23_7_ok low_17
lemma sl_23_8_ok : sliceDirectCheck 0 8 0 R_23 G_23 R_7 G_7 = true := by decide +kernel
lemma sl_23_8 : Slice R_23 G_23 (subcube 0 8) 7 := slice_direct sl_23_8_ok low_7
lemma sl_23_9_ok : sliceDirectCheck 2 8 0 R_23 G_23 R_3 G_3 = true := by decide +kernel
lemma sl_23_9 : Slice R_23 G_23 (subcube 2 8) 4 := slice_direct sl_23_9_ok low_3
set_option maxRecDepth 200000 in
lemma slices_23_ok : ∀ i (hi : i < slices_23.size), Slice R_23 G_23 slices_23[i].1 slices_23[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_23 G_23 p.1 p.2) (forall_cons sl_23_0 (forall_cons sl_23_1 (forall_cons sl_23_2 (forall_cons sl_23_3 (forall_cons sl_23_4 (forall_cons sl_23_5 (forall_cons sl_23_6 (forall_cons sl_23_7 (forall_cons sl_23_8 (forall_cons sl_23_9 (fun _ h => (List.not_mem_nil h).elim)))))))))))
lemma P_23_ok : ∀ i (hi : i < P_23.size), ∀ c, P_23[i] = some c → ValidPool R_23 G_23 c := buildPools_sound slices_23_ok
def bk_23_init : Array (List (List Nat)) := #[]
lemma bk_23_init_ok : ∀ i (hi : i < bk_23_init.size), ∀ xs ∈ bk_23_init[i], Impossible G_23 (0 - 1) xs.toFinset := by intro i hi; simp [bk_23_init] at hi
def nodes_23_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_0 : checkNodes W_23 G_23 fmask_23 P_23 autos_23 bk_23_init 0 nodes_23_0 = true := by decide +kernel
def bk_23_0 : Array (List (List Nat)) := buildBuckets 1 W_23 nodes_23_0
lemma bk_23_0_ok : ∀ i (hi : i < bk_23_0.size), ∀ xs ∈ bk_23_0[i], Impossible G_23 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_init_ok chk_23_0
def nodes_23_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_1 : checkNodes W_23 G_23 fmask_23 P_23 autos_23 bk_23_0 1 nodes_23_1 = true := by decide +kernel
def bk_23_1 : Array (List (List Nat)) := buildBuckets 1 W_23 nodes_23_1
lemma bk_23_1_ok : ∀ i (hi : i < bk_23_1.size), ∀ xs ∈ bk_23_1[i], Impossible G_23 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_0_ok chk_23_1
def nodes_23_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_2 : checkNodes W_23 G_23 fmask_23 P_23 autos_23 bk_23_1 2 nodes_23_2 = true := by decide +kernel
def bk_23_2 : Array (List (List Nat)) := buildBuckets 1 W_23 nodes_23_2
lemma bk_23_2_ok : ∀ i (hi : i < bk_23_2.size), ∀ xs ∈ bk_23_2[i], Impossible G_23 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_1_ok chk_23_2
def nodes_23_3 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_3 : checkNodes W_23 G_23 fmask_23 P_23 autos_23 bk_23_2 3 nodes_23_3 = true := by decide +kernel
def bk_23_3 : Array (List (List Nat)) := buildBuckets 1 W_23 nodes_23_3
lemma bk_23_3_ok : ∀ i (hi : i < bk_23_3.size), ∀ xs ∈ bk_23_3[i], Impossible G_23 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_2_ok chk_23_3
def nodes_23_4 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_4 : checkNodes W_23 G_23 fmask_23 P_23 autos_23 bk_23_3 4 nodes_23_4 = true := by decide +kernel
def bk_23_4 : Array (List (List Nat)) := buildBuckets 1 W_23 nodes_23_4
lemma bk_23_4_ok : ∀ i (hi : i < bk_23_4.size), ∀ xs ∈ bk_23_4[i], Impossible G_23 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_3_ok chk_23_4
def nodes_23_5 : List NodeSpec := [([0,1,2,7,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_5 : checkNodes W_23 G_23 fmask_23 P_23 autos_23 bk_23_4 5 nodes_23_5 = true := by decide +kernel
def bk_23_5 : Array (List (List Nat)) := buildBuckets 1 W_23 nodes_23_5
lemma bk_23_5_ok : ∀ i (hi : i < bk_23_5.size), ∀ xs ∈ bk_23_5[i], Impossible G_23 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_4_ok chk_23_5
def nodes_23_6 : List NodeSpec := [([5,0,1,6,2,3,4],[0,1,2,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_6 : checkNodes W_23 G_23 fmask_23 P_23 autos_23 bk_23_5 6 nodes_23_6 = true := by decide +kernel
def bk_23_6 : Array (List (List Nat)) := buildBuckets 1 W_23 nodes_23_6
lemma bk_23_6_ok : ∀ i (hi : i < bk_23_6.size), ∀ xs ∈ bk_23_6[i], Impossible G_23 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_5_ok chk_23_6
def nodes_23_7 : List NodeSpec := [([5,0,1,2,3,4],[7,9,0,2,3,10,11,4,1,8,12],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_7 : checkNodes W_23 G_23 fmask_23 P_23 autos_23 bk_23_6 7 nodes_23_7 = true := by decide +kernel
def bk_23_7 : Array (List (List Nat)) := buildBuckets 1 W_23 nodes_23_7
lemma bk_23_7_ok : ∀ i (hi : i < bk_23_7.size), ∀ xs ∈ bk_23_7[i], Impossible G_23 7 xs.toFinset :=
  buildBuckets_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_6_ok chk_23_7
def nodes_23_8 : List NodeSpec := [([0,1,2,3,4],[9,7,2,10,4],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_8 : checkNodes W_23 G_23 fmask_23 P_23 autos_23 bk_23_7 8 nodes_23_8 = true := by decide +kernel
def bk_23_8 : Array (List (List Nat)) := buildBuckets 1 W_23 nodes_23_8
lemma bk_23_8_ok : ∀ i (hi : i < bk_23_8.size), ∀ xs ∈ bk_23_8[i], Impossible G_23 8 xs.toFinset :=
  buildBuckets_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_7_ok chk_23_8
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck R_23 G_23 [(VAR 0,11,10),(VAR 1,11,9),(VAR 2,13,9),(VAR 3,11,3),(VAR 4,23,7)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContains bk_23_8 R_23 = true := by decide +kernel
lemma low_23 : Lower R_23 G_23 9 := lower_of_forest root_23_ok bk_23_8_ok root_23_in
def G_24 : Nat := 0xfe80fe80fe00fe00fe80fe80fe00fe00
def R_24 : List Nat := varsOf 47
lemma low_24_ok : liftCheck 0 32 R_24 G_24 R_15 G_15 [(VAR 5,39,7)] = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 7 := lift_of low_24_ok low_15
def G_25 : Nat := 0xfefee8e8fefe0000fefee8e8fefe0000
def R_25 : List Nat := varsOf 55
lemma low_25_ok : liftCheck 0 32 R_25 G_25 R_7 G_7 [(VAR 5,35,3)] = true := by decide +kernel
lemma low_25 : Lower R_25 G_25 8 := lift_of low_25_ok low_7
def G_26 : Nat := 0xffc0fc00ff000000ffc0fc00ff000000
def R_26 : List Nat := varsOf 62
def pos_26 : List Nat := [24,24,26,26,28,28,30,30,42,42,42,44,44,44,46,46,54,54,54,54,56,56,58,60,24,24,24,24,24,24,42,42,42,42,42,44,44,44,44,44,54,54]
def neg_26 : List Nat := [16,8,18,10,20,12,22,14,40,34,10,40,36,12,38,14,52,50,38,22,48,40,50,52,14,22,38,40,50,52,14,22,38,50,52,14,22,38,50,52,14,40]
def fmask_26 : Nat := fullMask 42
def base_26 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x307c04fc7cc,0x17bd74ec6cc),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3f8008ff8f0,0x1bde78df0f0),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffff0ffff,0x3084920adaa),(0xffff0000ffff0000ffff0000ffff0000,0x3003fff00ff,0xd6b2db0055),(0xffffffff00000000ffffffff00000000,0x3ffc0ffff00,0x2e73cf75b00)]
def steps_26 : List (Nat × Nat × Nat) := [(0,0,3),(0,2,3),(3,2,3),(2,0,3),(2,0,2),(2,2,3),(1,2,3),(0,0,2),(3,7,0),(0,0,11),(0,11,4),(3,5,2),(3,0,11),(3,6,4),(0,9,3),(2,0,6),(3,8,2),(3,8,1),(2,9,3),(1,8,2),(2,12,3),(1,9,3),(3,10,0),(1,12,3),(3,12,3),(0,12,3),(3,9,3),(1,5,2),(1,0,6),(3,12,1),(1,10,7),(3,0,15),(3,1,11),(0,1,11),(0,0,15),(0,18,0),(2,1,6),(3,13,1),(3,25,1),(0,32,4),(3,23,4),(0,1,32),(3,31,4),(2,1,31),(2,18,0),(3,23,1),(3,30,4),(3,30,1),(0,1,15),(0,18,1)]
def W_26 : Array Decor := buildWires base_26 steps_26
def autos_26 : Array (List (Nat × Nat)) := #[[],[(1,2)]]
def slicesL_26 : List (Nat × Nat) := [(subcube 0 4,5),(subcube 0 32,6),(subcube 0 2,5),(subcube 0 6,4)]
def slices_26 : Array (Nat × Nat) := slicesL_26.toArray
def ps_26 : List PoolSpec := [(0,[]),(1,[(2,2,3),(3,2,3)]),(2,[]),(1,[(1,2,3),(0,0,11)]),(1,[]),(3,[]),(1,[(1,2,3),(3,0,11)]),(1,[(0,2,3),(2,0,6)]),(1,[(2,0,3),(3,8,1)]),(1,[(0,2,3),(1,0,6)]),(1,[(0,0,2),(3,12,1)]),(1,[(0,0,3)]),(1,[(0,2,3)]),(1,[(3,2,3)]),(1,[(2,0,3)]),(1,[(2,0,2)]),(1,[(2,2,3)]),(1,[(1,2,3)]),(1,[(0,0,2)])]
def P_26 : Array (Option BoundPool) := buildPools W_26 R_26 slices_26 ps_26
lemma gp_26 : goodPairs G_26 pos_26 neg_26 := goodPairs_of (by decide +kernel)
lemma base_26_ok : ∀ x ∈ base_26, faithful pos_26 neg_26 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_26_ok : ∀ x ∈ W_26.toList, faithful pos_26 neg_26 x ∧ x.1 < 2^128 := buildWires_faithful base_26_ok
lemma autos_26_ok : ∀ sw ∈ autos_26.toList, swapsValid sw = true ∧ permWord sw G_26 = G_26 := autos_of (by decide +kernel)
lemma sl_26_0_ok : sliceDirectCheck 0 4 0 R_26 G_26 R_19 G_19 = true := by decide +kernel
lemma sl_26_0 : Slice R_26 G_26 (subcube 0 4) 5 := slice_direct sl_26_0_ok low_19
lemma sl_26_1_ok : sliceDirectCheck 0 32 0 R_26 G_26 R_8 G_8 = true := by decide +kernel
lemma sl_26_1 : Slice R_26 G_26 (subcube 0 32) 6 := slice_direct sl_26_1_ok low_8
lemma sl_26_2_ok : sliceDirectCheck 0 2 0 R_26 G_26 R_20 G_20 = true := by decide +kernel
lemma sl_26_2 : Slice R_26 G_26 (subcube 0 2) 5 := slice_direct sl_26_2_ok low_20
lemma sl_26_3_ok : sliceDirectCheck 0 6 0 R_26 G_26 R_4 G_4 = true := by decide +kernel
lemma sl_26_3 : Slice R_26 G_26 (subcube 0 6) 4 := slice_direct sl_26_3_ok low_4
set_option maxRecDepth 200000 in
lemma slices_26_ok : ∀ i (hi : i < slices_26.size), Slice R_26 G_26 slices_26[i].1 slices_26[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_26 G_26 p.1 p.2) (forall_cons sl_26_0 (forall_cons sl_26_1 (forall_cons sl_26_2 (forall_cons sl_26_3 (fun _ h => (List.not_mem_nil h).elim)))))
lemma P_26_ok : ∀ i (hi : i < P_26.size), ∀ c, P_26[i] = some c → ValidPool R_26 G_26 c := buildPools_sound slices_26_ok
def bk_26_init : Array (List (List Nat)) := #[]
lemma bk_26_init_ok : ∀ i (hi : i < bk_26_init.size), ∀ xs ∈ bk_26_init[i], Impossible G_26 (0 - 1) xs.toFinset := by intro i hi; simp [bk_26_init] at hi
def nodes_26_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_0 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_init 0 nodes_26_0 = true := by decide +kernel
def bk_26_0 : Array (List (List Nat)) := buildBuckets 1 W_26 nodes_26_0
lemma bk_26_0_ok : ∀ i (hi : i < bk_26_0.size), ∀ xs ∈ bk_26_0[i], Impossible G_26 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_26 W_26_ok P_26_ok autos_26_ok bk_26_init_ok chk_26_0
def nodes_26_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_1 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_0 1 nodes_26_1 = true := by decide +kernel
def bk_26_1 : Array (List (List Nat)) := buildBuckets 1 W_26 nodes_26_1
lemma bk_26_1_ok : ∀ i (hi : i < bk_26_1.size), ∀ xs ∈ bk_26_1[i], Impossible G_26 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_26 W_26_ok P_26_ok autos_26_ok bk_26_0_ok chk_26_1
def nodes_26_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_2 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_1 2 nodes_26_2 = true := by decide +kernel
def bk_26_2 : Array (List (List Nat)) := buildBuckets 1 W_26 nodes_26_2
lemma bk_26_2_ok : ∀ i (hi : i < bk_26_2.size), ∀ xs ∈ bk_26_2[i], Impossible G_26 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_26 W_26_ok P_26_ok autos_26_ok bk_26_1_ok chk_26_2
def nodes_26_3 : List NodeSpec := [([39,53,2,3],[],[]),([40,54,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_3 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_2 3 nodes_26_3 = true := by decide +kernel
def bk_26_3 : Array (List (List Nat)) := buildBuckets 1 W_26 nodes_26_3
lemma bk_26_3_ok : ∀ i (hi : i < bk_26_3.size), ∀ xs ∈ bk_26_3[i], Impossible G_26 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_26 W_26_ok P_26_ok autos_26_ok bk_26_2_ok chk_26_3
def nd_26_4_0 : List NodeSpec := [([7,35,0,1,4],[],[]),([10,35,0,1,4],[],[]),([36,1,2,3,15],[],[]),([14,1,2,3,15],[],[]),([37,14,2,3,4],[],[]),([14,38,2,3,4],[],[]),([39,1,2,3,15],[],[0]),([10,14,1,2,4],[],[]),([0,1,6,2,15],[],[]),([14,1,6,2,4],[],[]),([40,18,1,2,3],[],[0]),([41,2,33,3,4],[],[]),([20,18,1,2,3],[],[]),([8,1,2,31,4],[],[]),([18,1,2,33,3],[],[]),([18,0,1,2,3],[],[]),([10,0,1,24,4],[],[]),([7,0,1,3,15],[],[]),([0,22,6,2,4],[],[]),([42,0,2,3,4],[],[]),([0,43,2,3,4],[],[]),([0,1,2,44,3],[],[]),([0,1,2,3,15],[],[]),([0,1,2,3,45],[],[]),([0,46,2,3,4],[],[]),([47,0,1,2,3],[],[]),([5,1,2,28,4],[],[]),([20,41,2,3,4],[],[]),([0,1,6,3,15],[],[]),([48,0,2,3,4],[],[]),([10,7,0,1,4],[],[]),([49,18,1,2,3],[],[]),([0,50,2,3,4],[],[]),([10,0,22,2,4],[],[]),([17,1,2,3,15],[],[]),([9,1,21,3,4],[],[]),([12,1,32,3,4],[],[]),([20,1,2,3,4],[],[]),([35,0,1,2,4],[],[]),([51,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_4_0 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_3 4 nd_26_4_0 = true := by decide +kernel
def nd_26_4_1 : List NodeSpec := [([10,0,1,2,15],[],[]),([14,1,2,3,4],[],[]),([35,0,1,3,4],[],[]),([52,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_4_1 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_3 4 nd_26_4_1 = true := by decide +kernel
def nodes_26_4 : List NodeSpec := nd_26_4_0 ++ nd_26_4_1
lemma chk_26_4 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_3 4 nodes_26_4 = true := by
  unfold nodes_26_4 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_26_4_0, chk_26_4_1⟩
def bk_26_4 : Array (List (List Nat)) := buildBuckets 15 W_26 nodes_26_4
lemma bk_26_4_ok : ∀ i (hi : i < bk_26_4.size), ∀ xs ∈ bk_26_4[i], Impossible G_26 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_26 W_26_ok P_26_ok autos_26_ok bk_26_3_ok chk_26_4
def nd_26_5_0 : List NodeSpec := [([13,0,1,2,3,4],[0],[0]),([10,7,0,1,3,4],[],[0]),([10,7,0,1,2,4],[],[0]),([10,7,0,1,4],[1],[0]),([14,1,2,3,11,4],[2,3],[0]),([0,1,2,3,11,4],[2,0,4],[0,1]),([0,1,2,3,15,11],[4],[0,1]),([0,1,2,3,15],[],[0,1]),([8,5,1,2,3,4],[4,5],[]),([7,0,1,3,11,4],[4],[0]),([16,0,1,2,3,4],[],[]),([17,1,2,3,11,4],[5,6],[0,1]),([14,1,2,3,4],[3],[0]),([0,1,6,3,11,4],[],[0]),([0,1,6,2,11,4],[],[0,1]),([18,0,1,6,2,3],[4],[0,1]),([10,0,1,6,3,4],[4],[0]),([19,0,1,2,3,4],[],[]),([20,1,6,2,3,4],[2,7],[1,0]),([18,0,1,2,3],[],[0,1]),([20,0,1,2,3,4],[],[]),([10,0,1,2,11,4],[4],[0,1]),([20,1,2,3,4],[7],[]),([8,10,0,1,2,4],[2],[0]),([8,0,1,6,2,4],[2],[0]),([0,1,21,2,3,4],[],[0]),([8,9,1,2,3,4],[5],[0]),([8,0,22,2,3,4],[0,5],[]),([5,0,1,6,2,4],[2],[]),([10,0,1,2,3,4],[],[0]),([23,0,1,2,3,4],[0,4],[0]),([0,1,2,24,3,4],[2],[0]),([25,0,1,2,3,4],[0],[0]),([0,1,2,3,26,4],[],[]),([7,0,1,2,3,4],[],[0]),([0,22,2,3,4],[8],[0]),([27,0,1,2,3,4],[],[]),([10,5,0,1,2,4],[2],[]),([0,1,6,2,3,4],[2,0,4],[0,1]),([0,1,2,3,28,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_5_0 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_4 5 nd_26_5_0 = true := by decide +kernel
def nd_26_5_1 : List NodeSpec := [([14,0,1,2,3,4],[],[]),([12,5,1,2,3,4],[5],[0]),([29,0,1,2,3,4],[],[]),([7,0,1,6,2,4],[4],[0]),([30,0,1,2,3,4],[0,4],[0]),([0,1,2,31,3,4],[0,4],[0]),([0,1,2,32,3,4],[0,2,4],[0]),([1,6,2,33,3,4],[5,9],[0]),([9,12,1,2,3,4],[4,5],[]),([34,12,0,2,3,4],[0],[]),([34,0,2,3,4],[10],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_5_1 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_4 5 nd_26_5_1 = true := by decide +kernel
def nodes_26_5 : List NodeSpec := nd_26_5_0 ++ nd_26_5_1
lemma chk_26_5 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_4 5 nodes_26_5 = true := by
  unfold nodes_26_5 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_26_5_0, chk_26_5_1⟩
def bk_26_5 : Array (List (List Nat)) := buildBuckets 18 W_26 nodes_26_5
lemma bk_26_5_ok : ∀ i (hi : i < bk_26_5.size), ∀ xs ∈ bk_26_5[i], Impossible G_26 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_26 W_26_ok P_26_ok autos_26_ok bk_26_4_ok chk_26_5
def nodes_26_6 : List NodeSpec := [([5,0,1,2,3,4],[2,5,11],[0]),([0,1,6,2,3,4],[2,12,0],[0,1]),([7,0,1,2,3,4],[2,0,13],[0,1]),([8,0,1,2,3,4],[2,5,14],[0]),([9,0,1,2,3,4],[2,5,15],[0]),([10,0,1,2,3,4],[2,0,16],[0,1]),([0,1,2,3,11,4],[2,17,0],[0,1]),([12,0,1,2,3,4],[2,5,18],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_6 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_5 6 nodes_26_6 = true := by decide +kernel
def bk_26_6 : Array (List (List Nat)) := buildBuckets 3 W_26 nodes_26_6
lemma bk_26_6_ok : ∀ i (hi : i < bk_26_6.size), ∀ xs ∈ bk_26_6[i], Impossible G_26 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_26 W_26_ok P_26_ok autos_26_ok bk_26_5_ok chk_26_6
def nodes_26_7 : List NodeSpec := [([0,1,2,3,4],[5,4],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_26_7 : checkNodes W_26 G_26 fmask_26 P_26 autos_26 bk_26_6 7 nodes_26_7 = true := by decide +kernel
def bk_26_7 : Array (List (List Nat)) := buildBuckets 1 W_26 nodes_26_7
lemma bk_26_7_ok : ∀ i (hi : i < bk_26_7.size), ∀ xs ∈ bk_26_7[i], Impossible G_26 7 xs.toFinset :=
  buildBuckets_sound (by decide) gp_26 W_26_ok P_26_ok autos_26_ok bk_26_6_ok chk_26_7
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_26_ok : forestRootCheck R_26 G_26 [(VAR 1,42,40),(VAR 2,44,40),(VAR 3,24,16),(VAR 4,24,8),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_26_in : bucketContains bk_26_7 R_26 = true := by decide +kernel
lemma low_26 : Lower R_26 G_26 8 := lower_of_forest root_26_ok bk_26_7_ok root_26_in
def G_27 : Nat := 0xee008800ee000000ee008800ee000000
def R_27 : List Nat := varsOf 59
lemma low_27_ok : carryOK [(0,2),(0,1)] R_27 G_27 R_22 G_22 = true := by decide +kernel
lemma low_27 : Lower R_27 G_27 6 := carry_of low_27_ok low_22
def G_28 : Nat := 0xfa00a000fa000000fa00a000fa000000
def R_28 : List Nat := varsOf 61
lemma low_28_ok : carryOK [(0,1)] R_28 G_28 R_22 G_22 = true := by decide +kernel
lemma low_28 : Lower R_28 G_28 6 := carry_of low_28_ok low_22
def G_29 : Nat := 0xff88ee00ff000000ff88ee00ff000000
def R_29 : List Nat := varsOf 59
lemma low_29_ok : carryOK [(0,2),(0,1)] R_29 G_29 R_26 G_26 = true := by decide +kernel
lemma low_29 : Lower R_29 G_29 8 := carry_of low_29_ok low_26
def G_30 : Nat := 0xffa0fa00ff000000ffa0fa00ff000000
def R_30 : List Nat := varsOf 61
lemma low_30_ok : carryOK [(0,1)] R_30 G_30 R_26 G_26 = true := by decide +kernel
lemma low_30 : Lower R_30 G_30 8 := carry_of low_30_ok low_26
def G_31 : Nat := 0xfe80e800fe000000fe80e800fe000000
def R_31 : List Nat := varsOf 63
def pos_31 : List Nat := [25,25,25,26,26,26,27,27,28,28,28,29,29,30,30,31,31,43,43,43,43,45,45,45,45,46,46,46,46,47,47,55,55,55,55,55,57,57,57,58,58,58,59,60,60,60,61,62,25,25,25,25,25,25,25,25,25,25,26,26,26,26,26,26,26,26,26,26,28,28,28,28,28,28,28,28,28,28,43,43,43,43,43,43,43,43,45,45,45,45,45,45,45,45,46,46,46,46,46,46,46,46,55,55,55,55,55]
def neg_31 : List Nat := [24,17,9,24,18,10,19,11,24,20,12,21,13,22,14,23,15,42,41,35,11,44,41,37,13,44,42,38,14,39,15,54,53,51,39,23,56,49,41,56,50,42,51,56,52,44,53,54,15,23,39,41,42,44,51,53,54,56,15,23,39,41,42,44,51,53,54,56,15,23,39,41,42,44,51,53,54,56,15,23,39,44,51,53,54,56,15,23,39,42,51,53,54,56,15,23,39,41,51,53,54,56,15,41,42,44,56]
def fmask_31 : Nat := fullMask 107
def base_31 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7c03fffc00003ff447fe1ff98c7,0xcfcdcdccf33ccf446f61dd98c6),(0xcccccccccccccccccccccccccccccccc,0x7ffc03fc00ffc00878ffe1fe0f8,0x155d7d5d5755d57870efc1be0f0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7ffffc03ff00000f80fffe1ff00,0x259d9dbda769da7f00dfba1fe00),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffffffffffffffff07fffffff,0x7e262626398e6392ad0577755ad),(0xffff0000ffff0000ffff0000ffff0000,0x7c000003fffffffffff8001ffff,0x43cbcbcbc2f0bc2ddbb8000ab5b),(0xffffffff00000000ffffffff00000000,0x7ffffffc0000000fffffffe0000,0x7bf3f3f3fcff3fcfff7aeee0000)]
def steps_31 : List (Nat × Nat × Nat) := [(0,0,4),(2,3,4),(2,0,4),(0,0,3),(0,3,4),(0,0,1),(3,10,5),(2,0,10),(3,8,1),(3,8,3),(3,6,3),(3,6,1),(2,2,4),(2,1,4),(3,11,3),(3,9,4),(1,9,4),(3,7,0),(3,11,4),(3,11,2),(0,1,4),(0,9,4),(3,9,1),(0,11,4),(0,2,3),(0,2,4),(0,11,3),(0,11,2),(0,12,0),(2,1,10),(3,17,2),(1,9,26),(3,27,5),(3,27,1),(1,19,9),(3,7,2),(3,9,2),(1,11,10),(3,30,4),(3,31,3),(2,0,31),(2,11,31),(2,2,10),(3,24,5),(0,30,4),(3,18,3),(3,6,2),(1,8,10),(3,32,2),(0,12,1),(1,28,31),(2,12,11),(3,50,5),(1,18,32),(2,1,31),(1,9,31),(1,18,28),(1,32,31)]
def W_31 : Array Decor := buildWires base_31 steps_31
def autos_31 : Array (List (Nat × Nat)) := #[[],[(1,2)],[(0,1),(0,2)],[(0,2),(0,1)],[(0,1)]]
def slicesL_31 : List (Nat × Nat) := [(subcube 0 1,8),(subcube 0 48,6),(subcube 0 40,7),(subcube 0 4,8),(subcube 0 5,5),(subcube 16 0,6),(subcube 4 0,6),(subcube 4 8,5),(subcube 0 2,8),(subcube 1 40,4),(subcube 16 32,5),(subcube 2 40,4),(subcube 4 40,4),(subcube 0 16,7),(subcube 2 8,5),(subcube 1 0,6),(subcube 0 3,5),(subcube 0 7,4),(subcube 16 8,5),(subcube 16 40,4),(subcube 1 32,5),(subcube 2 0,6),(subcube 0 8,8),(subcube 1 8,5),(subcube 0 6,5),(subcube 0 33,6),(subcube 0 32,9),(subcube 4 32,5),(subcube 2 32,5)]
def slices_31 : Array (Nat × Nat) := slicesL_31.toArray
def ps_31 : List PoolSpec := [(0,[(0,3,4),(3,10,5),(0,12,1)]),(1,[]),(2,[]),(0,[(0,3,4),(3,10,5),(2,12,11)]),(0,[(0,2,3),(0,30,4),(3,50,5)]),(0,[(0,3,4),(1,11,10),(3,10,5)]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(8,[(0,3,4),(3,10,5)]),(11,[]),(3,[(0,3,4),(3,10,5)]),(12,[]),(0,[(0,3,4),(3,10,5)]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(18,[]),(0,[(0,1,4),(1,9,26)]),(19,[]),(20,[]),(3,[(0,0,3),(0,9,4),(3,27,5)]),(8,[(0,0,3),(0,9,4),(3,27,5)]),(21,[]),(13,[(0,0,3)]),(22,[]),(0,[]),(3,[(2,3,4)]),(0,[(2,3,4),(3,7,2)]),(0,[(0,3,4),(2,1,10)]),(8,[(0,3,4)]),(3,[(0,0,3),(3,9,1)]),(23,[]),(0,[(0,2,4),(2,3,4)]),(0,[(0,3,4),(1,11,10)]),(0,[(0,2,3),(3,30,4)]),(0,[(0,2,4),(3,31,3)]),(24,[]),(0,[(0,2,3),(0,2,4)]),(13,[(0,0,1)]),(3,[(0,3,4)]),(0,[(0,3,4),(2,2,10)]),(0,[(0,2,3),(0,30,4)]),(25,[]),(0,[(2,2,4),(3,18,3)]),(0,[(2,2,4),(0,3,4)]),(0,[(0,2,4),(0,3,4)]),(26,[]),(0,[(0,3,4)]),(8,[(0,3,4),(2,0,10)]),(3,[(0,3,4),(2,0,10)]),(3,[(2,0,4),(3,8,1)]),(3,[(0,0,4),(0,3,4)]),(8,[(0,0,4),(0,3,4)]),(3,[(2,0,4),(3,8,3)]),(8,[(2,0,4),(3,8,3)]),(3,[(0,0,4),(3,6,3)]),(8,[(0,0,4),(3,6,3)]),(0,[(3,6,1)]),(8,[(0,0,4)]),(26,[(0,0,1),(2,2,4)]),(0,[(2,2,4)]),(8,[(0,0,3)]),(0,[(2,1,4)]),(8,[(0,0,3),(3,9,4)]),(3,[(0,0,3),(3,9,4)]),(0,[(3,9,4)]),(3,[(0,0,4),(2,3,4)]),(8,[(0,0,4),(2,3,4)]),(8,[(0,0,3),(1,9,4)]),(3,[(0,0,3),(1,9,4)]),(0,[(1,9,4)]),(3,[(2,3,4),(3,7,0)]),(8,[(2,3,4),(3,7,0)]),(27,[]),(0,[(0,1,4)]),(3,[(0,0,3),(0,9,4)]),(8,[(0,0,3),(0,9,4)]),(0,[(3,9,1)]),(28,[]),(0,[(0,2,3)]),(3,[(2,0,4),(0,3,4)]),(8,[(2,0,4),(0,3,4)]),(13,[(2,0,10)]),(13,[(3,6,1)]),(26,[(0,0,1),(0,2,4)]),(0,[(0,2,4)]),(3,[(0,0,3),(0,0,4)]),(8,[(0,0,3),(0,0,4)]),(0,[(2,3,4)]),(3,[(0,0,4)]),(26,[(0,0,4)]),(8,[(2,3,4)]),(3,[(2,0,4)]),(8,[(2,0,4)]),(3,[(0,0,3)]),(26,[(0,0,1)])]
def P_31 : Array (Option BoundPool) := buildPools W_31 R_31 slices_31 ps_31
lemma gp_31 : goodPairs G_31 pos_31 neg_31 := goodPairs_of (by decide +kernel)
lemma base_31_ok : ∀ x ∈ base_31, faithful pos_31 neg_31 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_31_ok : ∀ x ∈ W_31.toList, faithful pos_31 neg_31 x ∧ x.1 < 2^128 := buildWires_faithful base_31_ok
lemma autos_31_ok : ∀ sw ∈ autos_31.toList, swapsValid sw = true ∧ permWord sw G_31 = G_31 := autos_of (by decide +kernel)
lemma sl_31_0_ok : sliceDirectCheck 0 1 0 R_31 G_31 R_26 G_26 = true := by decide +kernel
lemma sl_31_0 : Slice R_31 G_31 (subcube 0 1) 8 := slice_direct sl_31_0_ok low_26
lemma sl_31_1_ok : sliceDirectCheck 0 48 0 R_31 G_31 R_15 G_15 = true := by decide +kernel
lemma sl_31_1 : Slice R_31 G_31 (subcube 0 48) 6 := slice_direct sl_31_1_ok low_15
lemma sl_31_2_ok : sliceDirectCheck 0 40 0 R_31 G_31 R_7 G_7 = true := by decide +kernel
lemma sl_31_2 : Slice R_31 G_31 (subcube 0 40) 7 := slice_direct sl_31_2_ok low_7
lemma sl_31_3_ok : sliceDirectCheck 0 4 0 R_31 G_31 R_29 G_29 = true := by decide +kernel
lemma sl_31_3 : Slice R_31 G_31 (subcube 0 4) 8 := slice_direct sl_31_3_ok low_29
lemma sl_31_4_ok : sliceDirectCheck 0 5 0 R_31 G_31 R_19 G_19 = true := by decide +kernel
lemma sl_31_4 : Slice R_31 G_31 (subcube 0 5) 5 := slice_direct sl_31_4_ok low_19
lemma sl_31_5_ok : sliceDirectCheck 16 0 0 R_31 G_31 R_21 G_21 = true := by decide +kernel
lemma sl_31_5 : Slice R_31 G_31 (subcube 16 0) 6 := slice_direct sl_31_5_ok low_21
lemma sl_31_6_ok : sliceDirectCheck 4 0 0 R_31 G_31 R_27 G_27 = true := by decide +kernel
lemma sl_31_6 : Slice R_31 G_31 (subcube 4 0) 6 := slice_direct sl_31_6_ok low_27
lemma sl_31_7_ok : sliceDirectCheck 4 8 0 R_31 G_31 R_12 G_12 = true := by decide +kernel
lemma sl_31_7 : Slice R_31 G_31 (subcube 4 8) 5 := slice_direct sl_31_7_ok low_12
lemma sl_31_8_ok : sliceDirectCheck 0 2 0 R_31 G_31 R_30 G_30 = true := by decide +kernel
lemma sl_31_8 : Slice R_31 G_31 (subcube 0 2) 8 := slice_direct sl_31_8_ok low_30
lemma sl_31_9_ok : sliceDirectCheck 1 40 0 R_31 G_31 R_0 G_0 = true := by decide +kernel
lemma sl_31_9 : Slice R_31 G_31 (subcube 1 40) 4 := slice_direct sl_31_9_ok low_0
lemma sl_31_10_ok : sliceDirectCheck 16 32 0 R_31 G_31 R_9 G_9 = true := by decide +kernel
lemma sl_31_10 : Slice R_31 G_31 (subcube 16 32) 5 := slice_direct sl_31_10_ok low_9
lemma sl_31_11_ok : sliceDirectCheck 2 40 0 R_31 G_31 R_3 G_3 = true := by decide +kernel
lemma sl_31_11 : Slice R_31 G_31 (subcube 2 40) 4 := slice_direct sl_31_11_ok low_3
lemma sl_31_12_ok : sliceDirectCheck 4 40 0 R_31 G_31 R_2 G_2 = true := by decide +kernel
lemma sl_31_12 : Slice R_31 G_31 (subcube 4 40) 4 := slice_direct sl_31_12_ok low_2
lemma sl_31_13_ok : sliceDirectCheck 0 16 0 R_31 G_31 R_24 G_24 = true := by decide +kernel
lemma sl_31_13 : Slice R_31 G_31 (subcube 0 16) 7 := slice_direct sl_31_13_ok low_24
lemma sl_31_14_ok : sliceDirectCheck 2 8 0 R_31 G_31 R_14 G_14 = true := by decide +kernel
lemma sl_31_14 : Slice R_31 G_31 (subcube 2 8) 5 := slice_direct sl_31_14_ok low_14
lemma sl_31_15_ok : sliceDirectCheck 1 0 0 R_31 G_31 R_22 G_22 = true := by decide +kernel
lemma sl_31_15 : Slice R_31 G_31 (subcube 1 0) 6 := slice_direct sl_31_15_ok low_22
lemma sl_31_16_ok : sliceDirectCheck 0 3 0 R_31 G_31 R_20 G_20 = true := by decide +kernel
lemma sl_31_16 : Slice R_31 G_31 (subcube 0 3) 5 := slice_direct sl_31_16_ok low_20
lemma sl_31_17_ok : sliceDirectCheck 0 7 0 R_31 G_31 R_4 G_4 = true := by decide +kernel
lemma sl_31_17 : Slice R_31 G_31 (subcube 0 7) 4 := slice_direct sl_31_17_ok low_4
lemma sl_31_18_ok : sliceDirectCheck 16 8 0 R_31 G_31 R_10 G_10 = true := by decide +kernel
lemma sl_31_18 : Slice R_31 G_31 (subcube 16 8) 5 := slice_direct sl_31_18_ok low_10
lemma sl_31_19_ok : sliceDirectCheck 16 40 0 R_31 G_31 R_1 G_1 = true := by decide +kernel
lemma sl_31_19 : Slice R_31 G_31 (subcube 16 40) 4 := slice_direct sl_31_19_ok low_1
lemma sl_31_20_ok : sliceDirectCheck 1 32 0 R_31 G_31 R_5 G_5 = true := by decide +kernel
lemma sl_31_20 : Slice R_31 G_31 (subcube 1 32) 5 := slice_direct sl_31_20_ok low_5
lemma sl_31_21_ok : sliceDirectCheck 2 0 0 R_31 G_31 R_28 G_28 = true := by decide +kernel
lemma sl_31_21 : Slice R_31 G_31 (subcube 2 0) 6 := slice_direct sl_31_21_ok low_28
lemma sl_31_22_ok : sliceDirectCheck 0 8 0 R_31 G_31 R_25 G_25 = true := by decide +kernel
lemma sl_31_22 : Slice R_31 G_31 (subcube 0 8) 8 := slice_direct sl_31_22_ok low_25
lemma sl_31_23_ok : sliceDirectCheck 1 8 0 R_31 G_31 R_6 G_6 = true := by decide +kernel
lemma sl_31_23 : Slice R_31 G_31 (subcube 1 8) 5 := slice_direct sl_31_23_ok low_6
lemma sl_31_24_ok : sliceDirectCheck 0 6 0 R_31 G_31 R_18 G_18 = true := by decide +kernel
lemma sl_31_24 : Slice R_31 G_31 (subcube 0 6) 5 := slice_direct sl_31_24_ok low_18
lemma sl_31_25_ok : sliceDirectCheck 0 33 0 R_31 G_31 R_8 G_8 = true := by decide +kernel
lemma sl_31_25 : Slice R_31 G_31 (subcube 0 33) 6 := slice_direct sl_31_25_ok low_8
lemma sl_31_26_ok : sliceDirectCheck 0 32 0 R_31 G_31 R_23 G_23 = true := by decide +kernel
lemma sl_31_26 : Slice R_31 G_31 (subcube 0 32) 9 := slice_direct sl_31_26_ok low_23
lemma sl_31_27_ok : sliceDirectCheck 4 32 0 R_31 G_31 R_11 G_11 = true := by decide +kernel
lemma sl_31_27 : Slice R_31 G_31 (subcube 4 32) 5 := slice_direct sl_31_27_ok low_11
lemma sl_31_28_ok : sliceDirectCheck 2 32 0 R_31 G_31 R_13 G_13 = true := by decide +kernel
lemma sl_31_28 : Slice R_31 G_31 (subcube 2 32) 5 := slice_direct sl_31_28_ok low_13
set_option maxRecDepth 200000 in
lemma slices_31_ok : ∀ i (hi : i < slices_31.size), Slice R_31 G_31 slices_31[i].1 slices_31[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_31 G_31 p.1 p.2) (forall_cons sl_31_0 (forall_cons sl_31_1 (forall_cons sl_31_2 (forall_cons sl_31_3 (forall_cons sl_31_4 (forall_cons sl_31_5 (forall_cons sl_31_6 (forall_cons sl_31_7 (forall_cons sl_31_8 (forall_cons sl_31_9 (forall_cons sl_31_10 (forall_cons sl_31_11 (forall_cons sl_31_12 (forall_cons sl_31_13 (forall_cons sl_31_14 (forall_cons sl_31_15 (forall_cons sl_31_16 (forall_cons sl_31_17 (forall_cons sl_31_18 (forall_cons sl_31_19 (forall_cons sl_31_20 (forall_cons sl_31_21 (forall_cons sl_31_22 (forall_cons sl_31_23 (forall_cons sl_31_24 (forall_cons sl_31_25 (forall_cons sl_31_26 (forall_cons sl_31_27 (forall_cons sl_31_28 (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))
lemma P_31_ok : ∀ i (hi : i < P_31.size), ∀ c, P_31[i] = some c → ValidPool R_31 G_31 c := buildPools_sound slices_31_ok
def bk_31_init : Array (List (List Nat)) := #[]
lemma bk_31_init_ok : ∀ i (hi : i < bk_31_init.size), ∀ xs ∈ bk_31_init[i], Impossible G_31 (0 - 1) xs.toFinset := by intro i hi; simp [bk_31_init] at hi
def nodes_31_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_0 : checkNodes W_31 G_31 fmask_31 P_31 autos_31 bk_31_init 0 nodes_31_0 = true := by decide +kernel
def bk_31_0 : Array (List (List Nat)) := buildBuckets 1 W_31 nodes_31_0
lemma bk_31_0_ok : ∀ i (hi : i < bk_31_0.size), ∀ xs ∈ bk_31_0[i], Impossible G_31 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_init_ok chk_31_0
def nodes_31_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_1 : checkNodes W_31 G_31 fmask_31 P_31 autos_31 bk_31_0 1 nodes_31_1 = true := by decide +kernel
def bk_31_1 : Array (List (List Nat)) := buildBuckets 1 W_31 nodes_31_1
lemma bk_31_1_ok : ∀ i (hi : i < bk_31_1.size), ∀ xs ∈ bk_31_1[i], Impossible G_31 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_0_ok chk_31_1
def nodes_31_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_2 : checkNodes W_31 G_31 fmask_31 P_31 autos_31 bk_31_1 2 nodes_31_2 = true := by decide +kernel
def bk_31_2 : Array (List (List Nat)) := buildBuckets 1 W_31 nodes_31_2
lemma bk_31_2_ok : ∀ i (hi : i < bk_31_2.size), ∀ xs ∈ bk_31_2[i], Impossible G_31 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_1_ok chk_31_2
def nodes_31_3 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_3 : checkNodes W_31 G_31 fmask_31 P_31 autos_31 bk_31_2 3 nodes_31_3 = true := by decide +kernel
def bk_31_3 : Array (List (List Nat)) := buildBuckets 1 W_31 nodes_31_3
lemma bk_31_3_ok : ∀ i (hi : i < bk_31_3.size), ∀ xs ∈ bk_31_3[i], Impossible G_31 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_2_ok chk_31_3
def nodes_31_4 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_4 : checkNodes W_31 G_31 fmask_31 P_31 autos_31 bk_31_3 4 nodes_31_4 = true := by decide +kernel
def bk_31_4 : Array (List (List Nat)) := buildBuckets 1 W_31 nodes_31_4
lemma bk_31_4_ok : ∀ i (hi : i < bk_31_4.size), ∀ xs ∈ bk_31_4[i], Impossible G_31 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_3_ok chk_31_4
def nodes_31_5 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_5 : checkNodes W_31 G_31 fmask_31 P_31 autos_31 bk_31_4 5 nodes_31_5 = true := by decide +kernel
def bk_31_5 : Array (List (List Nat)) := buildBuckets 1 W_31 nodes_31_5
lemma bk_31_5_ok : ∀ i (hi : i < bk_31_5.size), ∀ xs ∈ bk_31_5[i], Impossible G_31 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_4_ok chk_31_5
def nodes_31_6 : List NodeSpec := [([34,55,0,1,2,3,4],[0],[]),([0,1,2,56,3,4,5],[],[]),([57,12,0,1,2,3,4],[1,2,3],[]),([58,11,0,1,2,3,4],[4],[]),([12,0,1,2,3,43,4],[5,2],[]),([59,0,1,2,3,4,5],[6],[]),([46,60,11,2,3,4,5],[7,8,9],[]),([11,1,2,61,3,4,5],[10,11],[]),([62,0,1,2,3,4,5],[],[]),([0,1,2,63,3,4,5],[6],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_6 : checkNodes W_31 G_31 fmask_31 P_31 autos_31 bk_31_5 6 nodes_31_6 = true := by decide +kernel
def bk_31_6 : Array (List (List Nat)) := buildBuckets 4 W_31 nodes_31_6
lemma bk_31_6_ok : ∀ i (hi : i < bk_31_6.size), ∀ xs ∈ bk_31_6[i], Impossible G_31 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_5_ok chk_31_6
def nodes_31_7 : List NodeSpec := [([34,12,0,1,2,3,4],[12,13,14,15,16,17,18],[0,1]),([13,12,0,1,2,3,4],[13,15,14,17,16,1,18,12],[]),([8,12,0,1,2,10,3],[1,13,15,17,12],[]),([8,35,0,1,2,10,3,5],[19,20,8],[]),([6,0,36,1,2,3,4,5],[21,22,23,9],[]),([9,0,1,37,2,3,4,5],[24],[]),([0,1,37,2,3,4,5],[20,25,24,26,9,6],[1]),([38,0,1,2,3,4],[21,27,28,29,24],[2]),([39,0,2,3,4,5],[30,21,24,27],[]),([28,21,0,1,2,3,4,5],[30,22,31,8],[]),([28,0,1,2,3,4,22,5],[19,24,21,30,22],[]),([40,0,1,2,3,4,5],[32,33,30,11,9,6,21,15],[]),([18,32,0,1,2,3,4,5],[19,30,6,9,23],[0]),([11,0,1,41,2,3,4,5],[30,22,34,9,35,21],[]),([13,35,0,1,2,3,4,5],[30,36,11,37,21],[]),([28,42,0,1,2,3,4,5],[30,7,11,9,22,38],[]),([12,11,0,1,2,3,4],[15,13,12,16,17,1,18],[0]),([7,11,0,1,31,2,3,5],[7,8,39,34,10,40,20],[]),([28,0,1,31,2,3,4,5],[30,8,22,23],[0]),([0,1,2,10,3,43,4,5],[41,30,15],[0]),([44,11,0,1,2,3,4,5],[30,22,42],[]),([45,11,0,1,2,3,4,5],[30,24,22,21,43],[]),([46,11,1,31,2,3,4,5],[8,44,33,9,23],[0]),([47,0,1,31,2,3,4,5],[22,6,19,23],[]),([11,0,1,30,31,3,4,5],[23,9,39,45,20,46],[]),([48,11,0,1,2,3,4,5],[30,22,47,9,48],[]),([18,11,9,1,2,3,4,5],[22,21,24,44,23],[]),([49,0,1,2,3,4],[27,22,13,24],[]),([9,40,0,1,2,3,4,5],[19,33,32],[]),([11,0,1,50,2,3,4,5],[30,22,49,21,50],[0]),([11,0,1,2,51,3,4,5],[30,10,22,51],[]),([18,28,0,1,2,3,4,5],[19,30,22,23],[0]),([17,52,0,1,2,3,4,5],[30,7,11,9,22],[2]),([11,9,1,31,2,3,4,5],[24,10,44,21,22,20,23],[0]),([0,1,2,10,53,3,5],[8,39,20,10,19,1],[]),([18,11,0,1,2,10,3,5],[19,39,52],[]),([32,0,1,31,2,3,4,5],[30,8,6,9,23],[0]),([12,11,0,1,2,10,3,4],[50,8,15,18],[0]),([11,0,1,31,2,10,3,5],[8,39,47,10,53,20,7],[]),([54,0,1,3,4,5],[21,30,9,39,27],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_7 : checkNodes W_31 G_31 fmask_31 P_31 autos_31 bk_31_6 7 nodes_31_7 = true := by decide +kernel
def bk_31_7 : Array (List (List Nat)) := buildBuckets 14 W_31 nodes_31_7
lemma bk_31_7_ok : ∀ i (hi : i < bk_31_7.size), ∀ xs ∈ bk_31_7[i], Impossible G_31 7 xs.toFinset :=
  buildBuckets_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_6_ok chk_31_7
def nodes_31_8 : List NodeSpec := [([12,0,1,2,10,3,4],[13,54,18,14,16,2],[0,1,2,3]),([12,0,1,2,3,4],[13,18,14,16,2,1],[0,4,3,2]),([13,0,1,2,10,3,4,5],[8,39,37,20,47,10,33,2,13,55,56,57,27],[0,4,1,3]),([0,14,1,2,3,4,5],[30,33,21,22,6,9,32,20,54,1,58],[]),([6,0,1,2,10,3,5],[19,8,20,10,33,13,39,59,60],[2]),([0,1,2,15,3,4,5],[21,39,19,61,62,30,1,9],[2]),([16,0,1,2,3,4,5],[19,21,33,24,30,11,9,6,26,39,63,64],[2]),([17,6,0,1,2,3,4,5],[11,22,19,21,7,24,27,23,65,66],[2,0]),([18,11,0,1,2,3,4,5],[19,30,22,23,46,39,50,67,24,68],[0,4]),([19,9,0,1,2,3,4,5],[19,21,20,33,7,10,22,2,15,11,69,44,8,70,24],[0,1]),([20,0,1,2,3,4,5],[11,21,33,39,9,6,8,19,22,23,15],[]),([21,9,0,1,2,3,4,5],[19,24,21,22,20,7,10,2,27,71,72,73],[0,1]),([21,0,1,2,3,4,5],[32,21,33,8,11,30,6,9,54,13,73,72,71,24],[2]),([7,6,0,1,2,3,5],[19,24,20,10,1,39,74,75],[2]),([9,0,1,2,3,4,22,5],[21,76,77,39,24,1,27,78,20,10],[0,1]),([23,0,1,2,3,4,5],[19,30,21,11,6,9,33,24,54,1,79,80],[2]),([24,0,1,2,3,4,5],[11,21,33,8,6,9,32,24,54,13,22],[0]),([25,0,1,2,3,4,5],[11,21,6,9,33,32,10,19,8,54,81,7,30,22,23],[]),([9,0,26,1,2,3,4,5],[24,21,30,11,44,22,26,20,82,7,10,69],[0,1]),([27,0,1,2,3,4,5],[21,11,30,6,9,24,54,27,83,84],[0,1,2]),([28,9,0,1,2,3,4,5],[11,22,32,21,33,20,7,10,31,24,2,27,23,85,38,69],[0]),([28,0,1,2,3,4,5],[32,30,33,6,9,19,8,54,86,21,22,38,20,69],[0]),([11,0,1,2,10,3,4,5],[39,20,47,10,22,8,19,2,15,55,7,46],[0]),([29,0,1,2,3,4,5],[30,21,6,9,32,24,54,27],[]),([11,0,1,30,2,3,4,5],[39,7,22,23,87,46,15],[0]),([8,0,1,2,10,3,5],[19,8,20,10,1,39,88,89],[0,2,1]),([11,9,1,2,3,4,5],[21,11,33,10,24,27,20,23],[0]),([13,0,1,2,3,4,5],[21,11,30,6,9,33,19,32,54,27,55,57,56,39,8,90],[2]),([17,0,1,2,3,4,5],[19,30,33,6,9,32,20,54,86,21,22,66,8,23,91],[]),([11,0,1,31,2,3,4,5],[44,7,30,8,22,23,6,9,24,19,92,93,21,46,39],[0,4]),([9,6,1,2,3,4,5],[21,32,33,19,27,20,10,94,95,24],[2]),([7,11,0,1,2,3,4,5],[19,30,24,39,11,46,7,50,15,34,10,96],[0]),([32,0,1,2,3,4,5],[30,21,6,9,39,19,8,54,27,23],[0]),([33,0,1,2,3,4,5],[30,21,9,32,39,19,8,54,27],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_8 : checkNodes W_31 G_31 fmask_31 P_31 autos_31 bk_31_7 8 nodes_31_8 = true := by decide +kernel
def bk_31_8 : Array (List (List Nat)) := buildBuckets 12 W_31 nodes_31_8
lemma bk_31_8_ok : ∀ i (hi : i < bk_31_8.size), ∀ xs ∈ bk_31_8[i], Impossible G_31 8 xs.toFinset :=
  buildBuckets_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_7_ok chk_31_8
def nodes_31_9 : List NodeSpec := [([6,0,1,2,3,4,5],[19,21,11,66,6,97,32,24,33,98],[0,1,2,4,3]),([7,0,1,2,3,4,5],[19,33,11,6,32,54,2,96,99,34],[0,4,3,2]),([8,0,1,2,3,4,5],[19,33,11,6,32,54,1,100,101,39],[0,1,2,4,3]),([9,0,1,2,3,4,5],[32,21,11,69,6,102,33,19,2],[0,1,2]),([0,1,2,10,3,4,5],[55,37,47,8,32,19,2],[0,1,2,3]),([11,0,1,2,3,4,5],[11,33,30,6,22,32,19,103,39,23],[0,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_9 : checkNodes W_31 G_31 fmask_31 P_31 autos_31 bk_31_8 9 nodes_31_9 = true := by decide +kernel
def bk_31_9 : Array (List (List Nat)) := buildBuckets 3 W_31 nodes_31_9
lemma bk_31_9_ok : ∀ i (hi : i < bk_31_9.size), ∀ xs ∈ bk_31_9[i], Impossible G_31 9 xs.toFinset :=
  buildBuckets_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_8_ok chk_31_9
def nodes_31_10 : List NodeSpec := [([0,1,2,3,4,5],[33,11,6,32,54],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_10 : checkNodes W_31 G_31 fmask_31 P_31 autos_31 bk_31_9 10 nodes_31_10 = true := by decide +kernel
def bk_31_10 : Array (List (List Nat)) := buildBuckets 1 W_31 nodes_31_10
lemma bk_31_10_ok : ∀ i (hi : i < bk_31_10.size), ∀ xs ∈ bk_31_10[i], Impossible G_31 10 xs.toFinset :=
  buildBuckets_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_9_ok chk_31_10
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_31_ok : forestRootCheck R_31 G_31 [(VAR 0,25,24),(VAR 1,26,24),(VAR 2,28,24),(VAR 3,25,17),(VAR 4,25,9),(VAR 5,43,11)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_31_in : bucketContains bk_31_10 R_31 = true := by decide +kernel
lemma low_31 : Lower R_31 G_31 11 := lower_of_forest root_31_ok bk_31_10_ok root_31_in
def wit : List PEqualNP.CircuitLowerBounds.Gate := [
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 11]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 16]⟩
]
def wo : Nat := 17
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by intro g hg; simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4269860864 * 2 ^ 32 + 4261412864) ||| ((4269860864 * 2 ^ 32 + 4261412864) <<< 64)).testBit r.val := by decide +kernel
lemma root_eq : G_31 = ((4269860864 * 2 ^ 32 + 4261412864) ||| ((4269860864 * 2 ^ 32 + 4261412864) <<< 64)) := by decide
lemma low_root : Lower (varsOf 63) ((4269860864 * 2 ^ 32 + 4261412864) ||| ((4269860864 * 2 ^ 32 + 4261412864) <<< 64)) 11 := root_eq ▸ low_31
end PEqualNP.Outside.L_meta_12068
theorem PEqualNP.Outside.L_meta_12068 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_12068.table2_of_lower (4269860864 * 2 ^ 32 + 4261412864) (by decide) (by decide) (by decide) (by decide)
    11 PEqualNP.Outside.L_meta_12068.low_root
    PEqualNP.Outside.L_meta_12068.wit PEqualNP.Outside.L_meta_12068.wo (by decide)
    PEqualNP.Outside.L_meta_12068.wit_mono PEqualNP.Outside.L_meta_12068.wit_eval s hcs
