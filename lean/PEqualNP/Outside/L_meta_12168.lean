import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_12168
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
abbrev FastPool := BoundPool × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else some (c, miss, vals.countP (isConstM c.dom))
def fastPoolCut (fp : FastPool) (k : Nat) (a b d : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let totC := fp.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && isConstM c.dom a then 1 else 0
    let dropB := if !kb && isConstM c.dom b then 1 else 0
    let z := bin d a b
    let cRest := totC - dropA - dropB + (if isConstM c.dom z then 1 else 0)
    let zIn := availM c.dom c.pm z
    let extra := if zIn then 0 else 1
    decide (k + c.paid + extra < c.lb + cRest) && (zIn || choiceOK c.dom c.pm (d, a, b))
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
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 d ka kb = true) :
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
        have hne_ab : a ≠ b := fun e => hab (congrArg Prod.fst e)
        have hnot_in : ∀ (x : Decor) (kx : Bool), kx = false → x ∈ ws → x.1 ∉ (delTwo ws a b ka kb).map Prod.fst → True := fun _ _ _ _ _ => trivial
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            exact List.Nodup.not_mem_erase hnd_ws hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · have hu_eq : u = a := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa)
          exact hna' hka hu_eq
        · have hu_eq : u = b := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb)
          exact hnb' hkb hu_eq
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut
      simp only [choiceVal, h_all_avail, Bool.true_and, Bool.and_true, List.countP_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hcut ⊢
      rw [hcnt]
      rcases hcut with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          cases hcz : isConstM c.dom (bin d a.1 b.1) <;>
          simp only [hz, hcz, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
            Bool.and_eq_true, Bool.false_eq_true, ite_true, ite_false] at h1 ⊢ <;> omega
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          simp only [hz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h2 ⊢ <;>
          exact h2
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
  go false false && go true false && go false true && go true true
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
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hfr_b : (ws.any (fun v => v.1 == z.1)) = false := by
    rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
    have hvz : v.1 = bin d a.1 b.1 := beq_iff_eq.mp heq
    exact hfr (hvz ▸ List.mem_map_of_mem hv)
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
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = false := Bool.eq_false_iff.mpr hfp
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
      simp only [testPairBT, Bool.and_eq_true] at ht
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
  decide vals.Nodup && !(vals.contains T) &&
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
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
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
def G_0 : Nat := 0xffffff00ff000000ffffff00ff000000
def R_0 : List Nat := varsOf 56
def pos_0 : List Nat := [24,24,40,40,48,48,24,40,48]
def neg_0 : List Nat := [16,8,32,8,32,16,32,16,8]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in
def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(2,5),(1,4),(0,3)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0
def G_2 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def R_2 : List Nat := varsOf 19
lemma low_2_ok : carryOK [(2,5),(1,2),(0,2),(1,4),(0,3)] R_2 G_2 R_0 G_0 = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 4 := carry_of low_2_ok low_0
def G_3 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def R_3 : List Nat := varsOf 35
lemma low_3_ok : carryOK [(1,2),(0,2),(1,4),(0,3)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0
def G_4 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_4 : List Nat := varsOf 21
lemma low_4_ok : carryOK [(2,5),(2,4),(0,1),(0,3)] R_4 G_4 R_0 G_0 = true := by decide +kernel
lemma low_4 : Lower R_4 G_4 4 := carry_of low_4_ok low_0
def G_5 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def R_5 : List Nat := varsOf 37
lemma low_5_ok : carryOK [(2,4),(0,1),(0,3)] R_5 G_5 R_0 G_0 = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 4 := carry_of low_5_ok low_0
def G_6 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_6 : List Nat := varsOf 22
lemma low_6_ok : carryOK [(2,5),(2,4),(1,3)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0
def G_7 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_7 : List Nat := varsOf 38
lemma low_7_ok : carryOK [(2,4),(1,3)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0
def G_8 : Nat := 0xf0f0f000f0000000f0f0f000f0000000
def R_8 : List Nat := varsOf 60
lemma low_8_ok : liftCheck 0 4 R_8 G_8 R_0 G_0 [(VAR 2,28,24)] = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 5 := lift_of low_8_ok low_0
def G_9 : Nat := 0xfcfcfcfcfcfcc0c0fcfcfcfcfcfcc0c0
def R_9 : List Nat := varsOf 54
lemma low_9_ok : liftCheck 16 0 R_9 G_9 R_7 G_7 [(VAR 4,18,2)] = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 5 := lift_of low_9_ok low_7
def G_10 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def R_10 : List Nat := varsOf 39
def pos_10 : List Nat := [3,3,5,5,6,6,33,33,34,34,36,36,3,3,5,5,6,6,33,33,34,34,36,36]
def neg_10 : List Nat := [2,1,4,1,4,2,32,1,32,2,32,4,4,32,2,32,1,32,2,4,1,4,1,2]
def fmask_10 : Nat := fullMask 24
def base_10 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_10 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_10 : BT Decor := buildWiresBT 4 base_10 steps_10
def autosL_10 : List (List (Nat × Nat)) := [[],[(2,5)],[(0,1)],[(2,5),(0,1)],[(1,2)],[(1,5),(1,2)],[(0,1),(0,2)],[(1,5),(0,1),(0,2)],[(1,5),(0,2)]]
def autos_10 : BT (List (Nat × Nat)) := btOfList 4 autosL_10
def slicesL_10 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 1 0,4),some (subcubeFast 32 0,4),some (subcubeFast 4 0,4)]
def slices_10 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_10
def ps_10 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_10 : BT (Option BoundPool) := buildPoolsBT 2 W_10 R_10 slices_10 ps_10
lemma gp_10 : goodPairs G_10 pos_10 neg_10 := goodPairs_of (by decide +kernel)
lemma base_10_ok : ∀ x ∈ base_10, faithful pos_10 neg_10 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_10_ok : btAll (fun x => faithful pos_10 neg_10 x ∧ x.1 < 2^128) W_10 := buildWiresBT_faithful base_10_ok
set_option maxRecDepth 500000 in
lemma autos_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_10 = G_10) autos_10 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_10_0_ok : sliceDirectCheck 2 0 0 R_10 G_10 R_5 G_5 = true := by decide +kernel
lemma sl_10_0 : Slice R_10 G_10 (subcubeFast 2 0) 4 := slice_fast_direct sl_10_0_ok low_5
lemma sl_10_1_ok : sliceDirectCheck 1 0 0 R_10 G_10 R_7 G_7 = true := by decide +kernel
lemma sl_10_1 : Slice R_10 G_10 (subcubeFast 1 0) 4 := slice_fast_direct sl_10_1_ok low_7
lemma sl_10_2_ok : sliceDirectCheck 32 0 0 R_10 G_10 R_1 G_1 = true := by decide +kernel
lemma sl_10_2 : Slice R_10 G_10 (subcubeFast 32 0) 4 := slice_fast_direct sl_10_2_ok low_1
lemma sl_10_3_ok : sliceDirectCheck 4 0 0 R_10 G_10 R_3 G_3 = true := by decide +kernel
lemma sl_10_3 : Slice R_10 G_10 (subcubeFast 4 0) 4 := slice_fast_direct sl_10_3_ok low_3
set_option maxRecDepth 500000 in
lemma slices_10_ok : btAll (fun o => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) slices_10 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_10_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_10 G_10 c) P_10 := buildPoolsBT_sound slices_10_ok
def bk_10_init : BT (List (List Nat)) := BT.empty
lemma bk_10_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 (0 - 1) xs.toFinset) bk_10_init := trivial
def nodes_10_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_0 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_init 0 nodes_10_0 = true := by decide +kernel
def bk_10_0 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_0
set_option maxRecDepth 500000 in
lemma bk_10_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 0 xs.toFinset) bk_10_0 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_init_ok chk_10_0
def nodes_10_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_1 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_0 1 nodes_10_1 = true := by decide +kernel
def bk_10_1 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_1
set_option maxRecDepth 500000 in
lemma bk_10_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 1 xs.toFinset) bk_10_1 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_0_ok chk_10_1
def nodes_10_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_2 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_1 2 nodes_10_2 = true := by decide +kernel
def bk_10_2 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_2
set_option maxRecDepth 500000 in
lemma bk_10_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 2 xs.toFinset) bk_10_2 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_1_ok chk_10_2
def nodes_10_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_3 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_2 3 nodes_10_3 = true := by decide +kernel
def bk_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_3
set_option maxRecDepth 500000 in
lemma bk_10_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 3 xs.toFinset) bk_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_2_ok chk_10_3
def nodes_10_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_4 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_3 4 nodes_10_4 = true := by decide +kernel
def bk_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_4
set_option maxRecDepth 500000 in
lemma bk_10_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 4 xs.toFinset) bk_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_3_ok chk_10_4
def nodes_10_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_5 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_4 5 nodes_10_5 = true := by decide +kernel
def bk_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_5
set_option maxRecDepth 500000 in
lemma bk_10_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 5 xs.toFinset) bk_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_4_ok chk_10_5
def nodes_10_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_6 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_5 6 nodes_10_6 = true := by decide +kernel
def bk_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_6
set_option maxRecDepth 500000 in
lemma bk_10_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 6 xs.toFinset) bk_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_5_ok chk_10_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck R_10 G_10 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT bk_10_6 R_10 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_10 : Lower R_10 G_10 7 := lower_of_forestBT root_10_ok bk_10_6_ok root_10_in
def G_11 : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
def R_11 : List Nat := varsOf 30
def pos_11 : List Nat := [10,10,12,12,14,22,22,22,24,24,26,28,10,10,10,12,12,12,22,24,24,24]
def neg_11 : List Nat := [8,2,8,4,6,20,18,6,16,8,18,20,6,18,20,6,18,20,8,6,18,20]
def fmask_11 : Nat := fullMask 22
def base_11 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x474f3,0x19b4d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x788fc,0x2ad8b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3bff1f,0x40205),(0xffff0000ffff0000ffff0000ffff0000,0x3c0fe0,0x336d60)]
def steps_11 : List (Nat × Nat × Nat) := [(3,0,2),(2,0,1),(2,0,2),(1,0,2),(1,0,1),(0,0,2),(0,0,1),(0,1,7),(3,0,1),(1,5,3),(1,9,1),(3,5,3),(3,1,7),(3,9,1),(3,10,8)]
def W_11 : BT Decor := buildWiresBT 5 base_11 steps_11
def autosL_11 : List (List (Nat × Nat)) := [[],[(2,4)],[(1,2)],[(1,4),(1,2)],[(1,2),(1,4)],[(1,4)]]
def autos_11 : BT (List (Nat × Nat)) := btOfList 3 autosL_11
def slicesL_11 : List (Option (Nat × Nat)) := []
def slices_11 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_11
def ps_11 : List PoolSpec := []
def P_11 : BT (Option BoundPool) := buildPoolsBT 1 W_11 R_11 slices_11 ps_11
lemma gp_11 : goodPairs G_11 pos_11 neg_11 := goodPairs_of (by decide +kernel)
lemma base_11_ok : ∀ x ∈ base_11, faithful pos_11 neg_11 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_11_ok : btAll (fun x => faithful pos_11 neg_11 x ∧ x.1 < 2^128) W_11 := buildWiresBT_faithful base_11_ok
set_option maxRecDepth 500000 in
lemma autos_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_11 = G_11) autos_11 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_11_ok : btAll (fun o => ∀ p, o = some p → Slice R_11 G_11 p.1 p.2) slices_11 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_11 G_11 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_11_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_11 G_11 c) P_11 := buildPoolsBT_sound slices_11_ok
def bk_11_init : BT (List (List Nat)) := BT.empty
lemma bk_11_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 (0 - 1) xs.toFinset) bk_11_init := trivial
def nodes_11_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_0 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_init 0 nodes_11_0 = true := by decide +kernel
def bk_11_0 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_0
set_option maxRecDepth 500000 in
lemma bk_11_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 0 xs.toFinset) bk_11_0 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_init_ok chk_11_0
def nodes_11_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_1 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_0 1 nodes_11_1 = true := by decide +kernel
def bk_11_1 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_1
set_option maxRecDepth 500000 in
lemma bk_11_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 1 xs.toFinset) bk_11_1 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_0_ok chk_11_1
def nodes_11_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_2 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_1 2 nodes_11_2 = true := by decide +kernel
def bk_11_2 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_2
set_option maxRecDepth 500000 in
lemma bk_11_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 2 xs.toFinset) bk_11_2 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_1_ok chk_11_2
def nodes_11_3 : List NodeSpec := [([6,4,1,3],[],[]),([0,11,2,3],[],[]),([5,12,2,3],[],[0]),([0,1,2,13],[],[]),([0,14,2,3],[],[]),([0,1,15,2],[],[]),([16,0,2,3],[],[]),([17,0,2,3],[],[]),([10,8,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_3 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_2 3 nodes_11_3 = true := by decide +kernel
def bk_11_3 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_3
set_option maxRecDepth 500000 in
lemma bk_11_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 3 xs.toFinset) bk_11_3 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_2_ok chk_11_3
def nodes_11_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([6,0,1,2,3],[],[0]),([0,1,2,7,3],[],[0,1]),([0,1,8,2,3],[],[0]),([9,0,1,2,3],[],[0,1]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_4 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_3 4 nodes_11_4 = true := by decide +kernel
def bk_11_4 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_4
set_option maxRecDepth 500000 in
lemma bk_11_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 4 xs.toFinset) bk_11_4 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_3_ok chk_11_4
def nodes_11_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_5 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_4 5 nodes_11_5 = true := by decide +kernel
def bk_11_5 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_5
set_option maxRecDepth 500000 in
lemma bk_11_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 5 xs.toFinset) bk_11_5 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_4_ok chk_11_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck R_11 G_11 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT bk_11_5 R_11 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_11 : Lower R_11 G_11 6 := lower_of_forestBT root_11_ok bk_11_5_ok root_11_in
def G_12 : Nat := 0xffffff00ff00f000ffffff00ff00f000
def R_12 : List Nat := varsOf 60
lemma low_12_ok : liftCheck 4 0 R_12 G_12 R_0 G_0 [(VAR 2,12,8)] = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 5 := lift_of low_12_ok low_0
def G_13 : Nat := 0xaaaaaa00aa000000aaaaaa00aa000000
def R_13 : List Nat := varsOf 57
lemma low_13_ok : carryOK [(0,1),(0,2)] R_13 G_13 R_8 G_8 = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 5 := carry_of low_13_ok low_8
def G_14 : Nat := 0xcccccc00cc000000cccccc00cc000000
def R_14 : List Nat := varsOf 58
lemma low_14_ok : carryOK [(1,2)] R_14 G_14 R_8 G_8 = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 5 := carry_of low_14_ok low_8
def G_15 : Nat := 0xe800e800e800e800e800e800e800e800
def R_15 : List Nat := varsOf 15
lemma low_15_ok : carryOK [(0,1),(0,2),(2,5),(1,4),(0,3)] R_15 G_15 R_8 G_8 = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 5 := carry_of low_15_ok low_8
def G_16 : Nat := 0xee008800ee008800ee008800ee008800
def R_16 : List Nat := varsOf 27
lemma low_16_ok : carryOK [(1,5),(0,2),(1,4),(0,3)] R_16 G_16 R_8 G_8 = true := by decide +kernel
lemma low_16 : Lower R_16 G_16 5 := carry_of low_16_ok low_8
def G_17 : Nat := 0xee00ee0088008800ee00ee0088008800
def R_17 : List Nat := varsOf 43
lemma low_17_ok : carryOK [(0,2),(1,4),(0,3)] R_17 G_17 R_8 G_8 = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 5 := carry_of low_17_ok low_8
def G_18 : Nat := 0xeeeeeeeeeeee8888eeeeeeeeeeee8888
def R_18 : List Nat := varsOf 51
lemma low_18_ok : carryOK [(0,2),(0,1)] R_18 G_18 R_9 G_9 = true := by decide +kernel
lemma low_18 : Lower R_18 G_18 5 := carry_of low_18_ok low_9
def G_19 : Nat := 0xfa00a000fa00a000fa00a000fa00a000
def R_19 : List Nat := varsOf 29
lemma low_19_ok : carryOK [(1,5),(1,2),(2,4),(0,1),(0,3)] R_19 G_19 R_8 G_8 = true := by decide +kernel
lemma low_19 : Lower R_19 G_19 5 := carry_of low_19_ok low_8
def G_20 : Nat := 0xfa00fa00a000a000fa00fa00a000a000
def R_20 : List Nat := varsOf 45
lemma low_20_ok : carryOK [(1,2),(2,4),(0,1),(0,3)] R_20 G_20 R_8 G_8 = true := by decide +kernel
lemma low_20 : Lower R_20 G_20 5 := carry_of low_20_ok low_8
def G_21 : Nat := 0xfafafafafafaa0a0fafafafafafaa0a0
def R_21 : List Nat := varsOf 53
lemma low_21_ok : carryOK [(0,1)] R_21 G_21 R_9 G_9 = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 5 := carry_of low_21_ok low_9
def G_22 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
def R_22 : List Nat := varsOf 30
lemma low_22_ok : carryOK [(1,5),(1,2),(2,4),(1,3)] R_22 G_22 R_8 G_8 = true := by decide +kernel
lemma low_22 : Lower R_22 G_22 5 := carry_of low_22_ok low_8
def G_23 : Nat := 0xfc00fc00c000c000fc00fc00c000c000
def R_23 : List Nat := varsOf 46
lemma low_23_ok : carryOK [(1,2),(2,4),(1,3)] R_23 G_23 R_8 G_8 = true := by decide +kernel
lemma low_23 : Lower R_23 G_23 5 := carry_of low_23_ok low_8
def G_24 : Nat := 0xfe80fe80fe80fe80fe80fe80fe80fe80
def R_24 : List Nat := varsOf 15
lemma low_24_ok : carryOK [(0,4),(0,2),(0,1)] R_24 G_24 R_11 G_11 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 6 := carry_of low_24_ok low_11
def G_25 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
def R_25 : List Nat := varsOf 23
lemma low_25_ok : carryOK [(4,5)] R_25 G_25 R_10 G_10 = true := by decide +kernel
lemma low_25 : Lower R_25 G_25 7 := carry_of low_25_ok low_10
def G_26 : Nat := 0xfefefefe80808080fefefefe80808080
def R_26 : List Nat := varsOf 39
lemma low_26_ok : carryOK [(3,5),(0,3),(0,4),(0,2),(0,1)] R_26 G_26 R_11 G_11 = true := by decide +kernel
lemma low_26 : Lower R_26 G_26 6 := carry_of low_26_ok low_11
def G_27 : Nat := 0xff88ee00ff88ee00ff88ee00ff88ee00
def R_27 : List Nat := varsOf 27
lemma low_27_ok : carryOK [(0,2),(0,1)] R_27 G_27 R_11 G_11 = true := by decide +kernel
lemma low_27 : Lower R_27 G_27 6 := carry_of low_27_ok low_11
def G_28 : Nat := 0xffa0fa00ffa0fa00ffa0fa00ffa0fa00
def R_28 : List Nat := varsOf 29
lemma low_28_ok : carryOK [(0,1)] R_28 G_28 R_11 G_11 = true := by decide +kernel
lemma low_28 : Lower R_28 G_28 6 := carry_of low_28_ok low_11
def G_29 : Nat := 0xffffff00ff00aa00ffffff00ff00aa00
def R_29 : List Nat := varsOf 57
lemma low_29_ok : carryOK [(0,1),(0,2)] R_29 G_29 R_12 G_12 = true := by decide +kernel
lemma low_29 : Lower R_29 G_29 5 := carry_of low_29_ok low_12
def G_30 : Nat := 0xffffff00ff00cc00ffffff00ff00cc00
def R_30 : List Nat := varsOf 58
lemma low_30_ok : carryOK [(1,2)] R_30 G_30 R_12 G_12 = true := by decide +kernel
lemma low_30 : Lower R_30 G_30 5 := carry_of low_30_ok low_12
def G_31 : Nat := 0xfcfcfc00fc00c000fcfcfc00fc00c000
def R_31 : List Nat := varsOf 62
def pos_31 : List Nat := [14,14,14,26,26,26,28,28,28,30,42,42,42,44,44,44,46,50,50,50,52,52,52,54,54,58,60,14,14,14,26,26,26,26,28,28,28,28,42,42,42,42,44,44,44,44,50,50,50,50,50,52,52,52,52,52]
def neg_31 : List Nat := [12,10,6,24,18,10,24,20,12,22,40,34,10,40,36,12,38,48,34,18,48,36,20,38,22,56,56,22,38,56,12,22,38,56,10,22,38,56,12,22,38,56,10,22,38,56,10,12,22,38,56,10,12,22,38,56]
def fmask_31 : Nat := fullMask 56
def base_31 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x7c3c3fb8f1e3f,0x6b5d9d998d1a36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf83c3c3df1e3c7,0x7399d9d9e1c385),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffffe01ffff,0x9ce6666600b56b),(0xffff0000ffff0000ffff0000ffff0000,0xffc03fc7fe03f8,0xa52aaaaf5a02d8),(0xffffffff00000000ffffffff00000000,0xffffc007fffc00,0xc6333336b76c00)]
def steps_31 : List (Nat × Nat × Nat) := [(1,3,4)]
def W_31 : BT Decor := buildWiresBT 3 base_31 steps_31
def autosL_31 : List (List (Nat × Nat)) := [[]]
def autos_31 : BT (List (Nat × Nat)) := btOfList 1 autosL_31
def slicesL_31 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 32 8,4),some (subcubeFast 16 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 8,4),some (subcubeFast 32 0,5)]
def slices_31 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_31
def ps_31 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])]
def P_31 : BT (Option BoundPool) := buildPoolsBT 4 W_31 R_31 slices_31 ps_31
lemma gp_31 : goodPairs G_31 pos_31 neg_31 := goodPairs_of (by decide +kernel)
lemma base_31_ok : ∀ x ∈ base_31, faithful pos_31 neg_31 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_31_ok : btAll (fun x => faithful pos_31 neg_31 x ∧ x.1 < 2^128) W_31 := buildWiresBT_faithful base_31_ok
set_option maxRecDepth 500000 in
lemma autos_31_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_31 = G_31) autos_31 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_31_0_ok : sliceDirectCheck 2 0 0 R_31 G_31 R_8 G_8 = true := by decide +kernel
lemma sl_31_0 : Slice R_31 G_31 (subcubeFast 2 0) 5 := slice_fast_direct sl_31_0_ok low_8
lemma sl_31_1_ok : sliceDirectCheck 0 2 0 R_31 G_31 R_12 G_12 = true := by decide +kernel
lemma sl_31_1 : Slice R_31 G_31 (subcubeFast 0 2) 5 := slice_fast_direct sl_31_1_ok low_12
lemma sl_31_2_ok : sliceDirectCheck 4 0 0 R_31 G_31 R_14 G_14 = true := by decide +kernel
lemma sl_31_2 : Slice R_31 G_31 (subcubeFast 4 0) 5 := slice_fast_direct sl_31_2_ok low_14
lemma sl_31_3_ok : sliceDirectCheck 0 4 0 R_31 G_31 R_30 G_30 = true := by decide +kernel
lemma sl_31_3 : Slice R_31 G_31 (subcubeFast 0 4) 5 := slice_fast_direct sl_31_3_ok low_30
lemma sl_31_4_ok : sliceDirectCheck 32 8 0 R_31 G_31 R_6 G_6 = true := by decide +kernel
lemma sl_31_4 : Slice R_31 G_31 (subcubeFast 32 8) 4 := slice_fast_direct sl_31_4_ok low_6
lemma sl_31_5_ok : sliceDirectCheck 16 0 0 R_31 G_31 R_23 G_23 = true := by decide +kernel
lemma sl_31_5 : Slice R_31 G_31 (subcubeFast 16 0) 5 := slice_fast_direct sl_31_5_ok low_23
lemma sl_31_6_ok : sliceDirectCheck 0 8 0 R_31 G_31 R_9 G_9 = true := by decide +kernel
lemma sl_31_6 : Slice R_31 G_31 (subcubeFast 0 8) 5 := slice_fast_direct sl_31_6_ok low_9
lemma sl_31_7_ok : sliceDirectCheck 16 8 0 R_31 G_31 R_7 G_7 = true := by decide +kernel
lemma sl_31_7 : Slice R_31 G_31 (subcubeFast 16 8) 4 := slice_fast_direct sl_31_7_ok low_7
lemma sl_31_8_ok : sliceDirectCheck 32 0 0 R_31 G_31 R_22 G_22 = true := by decide +kernel
lemma sl_31_8 : Slice R_31 G_31 (subcubeFast 32 0) 5 := slice_fast_direct sl_31_8_ok low_22
set_option maxRecDepth 500000 in
lemma slices_31_ok : btAll (fun o => ∀ p, o = some p → Slice R_31 G_31 p.1 p.2) slices_31 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_31 G_31 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_31_0) (forall_cons (fun _ h => by cases h; exact sl_31_1) (forall_cons (fun _ h => by cases h; exact sl_31_2) (forall_cons (fun _ h => by cases h; exact sl_31_3) (forall_cons (fun _ h => by cases h; exact sl_31_4) (forall_cons (fun _ h => by cases h; exact sl_31_5) (forall_cons (fun _ h => by cases h; exact sl_31_6) (forall_cons (fun _ h => by cases h; exact sl_31_7) (forall_cons (fun _ h => by cases h; exact sl_31_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
set_option maxRecDepth 500000 in
lemma P_31_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_31 G_31 c) P_31 := buildPoolsBT_sound slices_31_ok
def bk_31_init : BT (List (List Nat)) := BT.empty
lemma bk_31_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_31 (0 - 1) xs.toFinset) bk_31_init := trivial
def nodes_31_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_0 : checkNodesBT W_31 G_31 fmask_31 P_31 autos_31 bk_31_init 0 nodes_31_0 = true := by decide +kernel
def bk_31_0 : BT (List (List Nat)) := buildBucketsBT W_31 nodes_31_0
set_option maxRecDepth 500000 in
lemma bk_31_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_31 0 xs.toFinset) bk_31_0 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_init_ok chk_31_0
def nodes_31_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_1 : checkNodesBT W_31 G_31 fmask_31 P_31 autos_31 bk_31_0 1 nodes_31_1 = true := by decide +kernel
def bk_31_1 : BT (List (List Nat)) := buildBucketsBT W_31 nodes_31_1
set_option maxRecDepth 500000 in
lemma bk_31_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_31 1 xs.toFinset) bk_31_1 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_0_ok chk_31_1
def nodes_31_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_2 : checkNodesBT W_31 G_31 fmask_31 P_31 autos_31 bk_31_1 2 nodes_31_2 = true := by decide +kernel
def bk_31_2 : BT (List (List Nat)) := buildBucketsBT W_31 nodes_31_2
set_option maxRecDepth 500000 in
lemma bk_31_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_31 2 xs.toFinset) bk_31_2 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_1_ok chk_31_2
def nodes_31_3 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_3 : checkNodesBT W_31 G_31 fmask_31 P_31 autos_31 bk_31_2 3 nodes_31_3 = true := by decide +kernel
def bk_31_3 : BT (List (List Nat)) := buildBucketsBT W_31 nodes_31_3
set_option maxRecDepth 500000 in
lemma bk_31_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_31 3 xs.toFinset) bk_31_3 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_2_ok chk_31_3
def nodes_31_4 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_4 : checkNodesBT W_31 G_31 fmask_31 P_31 autos_31 bk_31_3 4 nodes_31_4 = true := by decide +kernel
def bk_31_4 : BT (List (List Nat)) := buildBucketsBT W_31 nodes_31_4
set_option maxRecDepth 500000 in
lemma bk_31_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_31 4 xs.toFinset) bk_31_4 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_3_ok chk_31_4
def nodes_31_5 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_5 : checkNodesBT W_31 G_31 fmask_31 P_31 autos_31 bk_31_4 5 nodes_31_5 = true := by decide +kernel
def bk_31_5 : BT (List (List Nat)) := buildBucketsBT W_31 nodes_31_5
set_option maxRecDepth 500000 in
lemma bk_31_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_31 5 xs.toFinset) bk_31_5 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_4_ok chk_31_5
def nodes_31_6 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_6 : checkNodesBT W_31 G_31 fmask_31 P_31 autos_31 bk_31_5 6 nodes_31_6 = true := by decide +kernel
def bk_31_6 : BT (List (List Nat)) := buildBucketsBT W_31 nodes_31_6
set_option maxRecDepth 500000 in
lemma bk_31_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_31 6 xs.toFinset) bk_31_6 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_5_ok chk_31_6
def nodes_31_7 : List NodeSpec := [([0,1,2,3,4],[2,1,3,0,5,6,7,8,4],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_31_7 : checkNodesBT W_31 G_31 fmask_31 P_31 autos_31 bk_31_6 7 nodes_31_7 = true := by decide +kernel
def bk_31_7 : BT (List (List Nat)) := buildBucketsBT W_31 nodes_31_7
set_option maxRecDepth 500000 in
lemma bk_31_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_31 7 xs.toFinset) bk_31_7 :=
  buildBucketsBT_sound (by decide) gp_31 W_31_ok P_31_ok autos_31_ok bk_31_6_ok chk_31_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_31_ok : forestRootCheck R_31 G_31 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,26,10),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_31_in : bucketContainsBT bk_31_7 R_31 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_31 : Lower R_31 G_31 8 := lower_of_forestBT root_31_ok bk_31_7_ok root_31_in
def G_32 : Nat := 0xfe00fe00e800e800fe00fe00e800e800
def R_32 : List Nat := varsOf 47
lemma low_32_ok : liftCheck 0 8 R_32 G_32 R_10 G_10 [(VAR 3,11,3)] = true := by decide +kernel
lemma low_32 : Lower R_32 G_32 8 := lift_of low_32_ok low_10
def G_33 : Nat := 0xfe80e800fe80e800fe80e800fe80e800
def R_33 : List Nat := varsOf 31
def pos_33 : List Nat := [11,11,11,13,13,13,14,14,14,15,23,23,23,23,25,25,25,26,26,26,27,28,28,28,29,30,11,11,11,11,11,11,13,13,13,13,13,13,14,14,14,14,14,14,23,23,23,23,25,25,25,25,25,25,26,26,26,26,26,26,28,28,28,28,28,28]
def neg_33 : List Nat := [10,9,3,12,9,5,12,10,6,7,22,21,19,7,24,17,9,24,18,10,19,24,20,12,21,22,7,12,19,21,22,24,7,10,19,21,22,24,7,9,19,21,22,24,9,10,12,24,7,10,12,19,21,22,7,9,12,19,21,22,7,9,10,19,21,22]
def fmask_33 : Nat := fullMask 66
def base_33 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3ff03ffd11fe3f,0x1b6d913cd3511ba36),(0xcccccccccccccccccccccccccccccccc,0xfc0ffc0fe1e3fc7,0x2da6b2557561c3785),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3f000ffff03e03ff8,0x31d7546596fc02f68),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffff0fffffffc3ff,0x6186f8a288ab40db),(0xffff0000ffff0000ffff0000ffff0000,0x3fffff00003fffc00,0x38e388f3cf376dc00)]
def steps_33 : List (Nat × Nat × Nat) := [(0,0,1),(0,2,4),(1,5,6)]
def W_33 : BT Decor := buildWiresBT 3 base_33 steps_33
def autosL_33 : List (List (Nat × Nat)) := [[],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def autos_33 : BT (List (Nat × Nat)) := btOfList 3 autosL_33
def slicesL_33 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,5),some (subcubeFast 16 0,5),some (subcubeFast 0 4,6),some (subcubeFast 4 0,5),some (subcubeFast 0 16,6),some (subcubeFast 0 1,6),some (subcubeFast 1 0,5),some (subcubeFast 0 2,6),some (subcubeFast 0 8,7),some (subcubeFast 2 8,4)]
def slices_33 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_33
def ps_33 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[(0,2,4)]),(6,[]),(7,[]),(2,[(0,0,1)]),(5,[]),(8,[]),(9,[]),(4,[(0,0,1)])]
def P_33 : BT (Option BoundPool) := buildPoolsBT 4 W_33 R_33 slices_33 ps_33
lemma gp_33 : goodPairs G_33 pos_33 neg_33 := goodPairs_of (by decide +kernel)
lemma base_33_ok : ∀ x ∈ base_33, faithful pos_33 neg_33 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_33_ok : btAll (fun x => faithful pos_33 neg_33 x ∧ x.1 < 2^128) W_33 := buildWiresBT_faithful base_33_ok
set_option maxRecDepth 500000 in
lemma autos_33_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_33 = G_33) autos_33 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_33_0_ok : sliceDirectCheck 2 0 0 R_33 G_33 R_19 G_19 = true := by decide +kernel
lemma sl_33_0 : Slice R_33 G_33 (subcubeFast 2 0) 5 := slice_fast_direct sl_33_0_ok low_19
lemma sl_33_1_ok : sliceDirectCheck 16 0 0 R_33 G_33 R_15 G_15 = true := by decide +kernel
lemma sl_33_1 : Slice R_33 G_33 (subcubeFast 16 0) 5 := slice_fast_direct sl_33_1_ok low_15
lemma sl_33_2_ok : sliceDirectCheck 0 4 0 R_33 G_33 R_27 G_27 = true := by decide +kernel
lemma sl_33_2 : Slice R_33 G_33 (subcubeFast 0 4) 6 := slice_fast_direct sl_33_2_ok low_27
lemma sl_33_3_ok : sliceDirectCheck 4 0 0 R_33 G_33 R_16 G_16 = true := by decide +kernel
lemma sl_33_3 : Slice R_33 G_33 (subcubeFast 4 0) 5 := slice_fast_direct sl_33_3_ok low_16
lemma sl_33_4_ok : sliceDirectCheck 0 16 0 R_33 G_33 R_24 G_24 = true := by decide +kernel
lemma sl_33_4 : Slice R_33 G_33 (subcubeFast 0 16) 6 := slice_fast_direct sl_33_4_ok low_24
lemma sl_33_5_ok : sliceDirectCheck 0 1 0 R_33 G_33 R_11 G_11 = true := by decide +kernel
lemma sl_33_5 : Slice R_33 G_33 (subcubeFast 0 1) 6 := slice_fast_direct sl_33_5_ok low_11
lemma sl_33_6_ok : sliceDirectCheck 1 0 0 R_33 G_33 R_22 G_22 = true := by decide +kernel
lemma sl_33_6 : Slice R_33 G_33 (subcubeFast 1 0) 5 := slice_fast_direct sl_33_6_ok low_22
lemma sl_33_7_ok : sliceDirectCheck 0 2 0 R_33 G_33 R_28 G_28 = true := by decide +kernel
lemma sl_33_7 : Slice R_33 G_33 (subcubeFast 0 2) 6 := slice_fast_direct sl_33_7_ok low_28
lemma sl_33_8_ok : sliceDirectCheck 0 8 0 R_33 G_33 R_25 G_25 = true := by decide +kernel
lemma sl_33_8 : Slice R_33 G_33 (subcubeFast 0 8) 7 := slice_fast_direct sl_33_8_ok low_25
lemma sl_33_9_ok : sliceDirectCheck 2 8 0 R_33 G_33 R_4 G_4 = true := by decide +kernel
lemma sl_33_9 : Slice R_33 G_33 (subcubeFast 2 8) 4 := slice_fast_direct sl_33_9_ok low_4
set_option maxRecDepth 500000 in
lemma slices_33_ok : btAll (fun o => ∀ p, o = some p → Slice R_33 G_33 p.1 p.2) slices_33 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_33 G_33 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_33_0) (forall_cons (fun _ h => by cases h; exact sl_33_1) (forall_cons (fun _ h => by cases h; exact sl_33_2) (forall_cons (fun _ h => by cases h; exact sl_33_3) (forall_cons (fun _ h => by cases h; exact sl_33_4) (forall_cons (fun _ h => by cases h; exact sl_33_5) (forall_cons (fun _ h => by cases h; exact sl_33_6) (forall_cons (fun _ h => by cases h; exact sl_33_7) (forall_cons (fun _ h => by cases h; exact sl_33_8) (forall_cons (fun _ h => by cases h; exact sl_33_9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 500000 in
lemma P_33_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_33 G_33 c) P_33 := buildPoolsBT_sound slices_33_ok
def bk_33_init : BT (List (List Nat)) := BT.empty
lemma bk_33_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_33 (0 - 1) xs.toFinset) bk_33_init := trivial
def nodes_33_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_33_0 : checkNodesBT W_33 G_33 fmask_33 P_33 autos_33 bk_33_init 0 nodes_33_0 = true := by decide +kernel
def bk_33_0 : BT (List (List Nat)) := buildBucketsBT W_33 nodes_33_0
set_option maxRecDepth 500000 in
lemma bk_33_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_33 0 xs.toFinset) bk_33_0 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok P_33_ok autos_33_ok bk_33_init_ok chk_33_0
def nodes_33_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_33_1 : checkNodesBT W_33 G_33 fmask_33 P_33 autos_33 bk_33_0 1 nodes_33_1 = true := by decide +kernel
def bk_33_1 : BT (List (List Nat)) := buildBucketsBT W_33 nodes_33_1
set_option maxRecDepth 500000 in
lemma bk_33_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_33 1 xs.toFinset) bk_33_1 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok P_33_ok autos_33_ok bk_33_0_ok chk_33_1
def nodes_33_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_33_2 : checkNodesBT W_33 G_33 fmask_33 P_33 autos_33 bk_33_1 2 nodes_33_2 = true := by decide +kernel
def bk_33_2 : BT (List (List Nat)) := buildBucketsBT W_33 nodes_33_2
set_option maxRecDepth 500000 in
lemma bk_33_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_33 2 xs.toFinset) bk_33_2 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok P_33_ok autos_33_ok bk_33_1_ok chk_33_2
def nodes_33_3 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_33_3 : checkNodesBT W_33 G_33 fmask_33 P_33 autos_33 bk_33_2 3 nodes_33_3 = true := by decide +kernel
def bk_33_3 : BT (List (List Nat)) := buildBucketsBT W_33 nodes_33_3
set_option maxRecDepth 500000 in
lemma bk_33_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_33 3 xs.toFinset) bk_33_3 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok P_33_ok autos_33_ok bk_33_2_ok chk_33_3
def nodes_33_4 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_33_4 : checkNodesBT W_33 G_33 fmask_33 P_33 autos_33 bk_33_3 4 nodes_33_4 = true := by decide +kernel
def bk_33_4 : BT (List (List Nat)) := buildBucketsBT W_33 nodes_33_4
set_option maxRecDepth 500000 in
lemma bk_33_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_33 4 xs.toFinset) bk_33_4 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok P_33_ok autos_33_ok bk_33_3_ok chk_33_4
def nodes_33_5 : List NodeSpec := [([0,1,2,7,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_33_5 : checkNodesBT W_33 G_33 fmask_33 P_33 autos_33 bk_33_4 5 nodes_33_5 = true := by decide +kernel
def bk_33_5 : BT (List (List Nat)) := buildBucketsBT W_33 nodes_33_5
set_option maxRecDepth 500000 in
lemma bk_33_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_33 5 xs.toFinset) bk_33_5 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok P_33_ok autos_33_ok bk_33_4_ok chk_33_5
def nodes_33_6 : List NodeSpec := [([5,0,1,6,2,3,4],[0,1,2,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_33_6 : checkNodesBT W_33 G_33 fmask_33 P_33 autos_33 bk_33_5 6 nodes_33_6 = true := by decide +kernel
def bk_33_6 : BT (List (List Nat)) := buildBucketsBT W_33 nodes_33_6
set_option maxRecDepth 500000 in
lemma bk_33_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_33 6 xs.toFinset) bk_33_6 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok P_33_ok autos_33_ok bk_33_5_ok chk_33_6
def nodes_33_7 : List NodeSpec := [([5,0,1,2,3,4],[7,9,0,2,3,10,11,4,1,8,12],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_33_7 : checkNodesBT W_33 G_33 fmask_33 P_33 autos_33 bk_33_6 7 nodes_33_7 = true := by decide +kernel
def bk_33_7 : BT (List (List Nat)) := buildBucketsBT W_33 nodes_33_7
set_option maxRecDepth 500000 in
lemma bk_33_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_33 7 xs.toFinset) bk_33_7 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok P_33_ok autos_33_ok bk_33_6_ok chk_33_7
def nodes_33_8 : List NodeSpec := [([0,1,2,3,4],[9,7,2,10,4],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_33_8 : checkNodesBT W_33 G_33 fmask_33 P_33 autos_33 bk_33_7 8 nodes_33_8 = true := by decide +kernel
def bk_33_8 : BT (List (List Nat)) := buildBucketsBT W_33 nodes_33_8
set_option maxRecDepth 500000 in
lemma bk_33_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_33 8 xs.toFinset) bk_33_8 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok P_33_ok autos_33_ok bk_33_7_ok chk_33_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_33_ok : forestRootCheck R_33 G_33 [(VAR 0,11,10),(VAR 1,11,9),(VAR 2,13,9),(VAR 3,11,3),(VAR 4,23,7)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_33_in : bucketContainsBT bk_33_8 R_33 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_33 : Lower R_33 G_33 9 := lower_of_forestBT root_33_ok bk_33_8_ok root_33_in
def G_34 : Nat := 0xfefe000080800000fefe000080800000
def R_34 : List Nat := varsOf 55
lemma low_34_ok : liftCheck 0 16 R_34 G_34 R_26 G_26 [(VAR 4,23,7)] = true := by decide +kernel
lemma low_34 : Lower R_34 G_34 7 := lift_of low_34_ok low_26
def G_35 : Nat := 0xfefefefefe80fe80fefefefefe80fe80
def R_35 : List Nat := varsOf 47
lemma low_35_ok : liftCheck 8 0 R_35 G_35 R_26 G_26 [(VAR 3,9,1)] = true := by decide +kernel
lemma low_35 : Lower R_35 G_35 7 := lift_of low_35_ok low_26
def G_36 : Nat := 0xfefefefefefee8e8fefefefefefee8e8
def R_36 : List Nat := varsOf 55
lemma low_36_ok : liftCheck 16 0 R_36 G_36 R_10 G_10 [(VAR 4,17,1)] = true := by decide +kernel
lemma low_36 : Lower R_36 G_36 8 := lift_of low_36_ok low_10
def G_37 : Nat := 0xffffff00ffc0fc00ffffff00ffc0fc00
def R_37 : List Nat := varsOf 62
def pos_37 : List Nat := [10,10,12,12,14,22,22,22,24,24,26,28,40,40,42,44,46,48,48,50,50,52,52,54,10,10,10,12,12,12,22,22,24,24,24,40,40,40,48,48,48,48]
def neg_37 : List Nat := [8,2,8,4,6,20,18,6,16,8,18,20,32,8,34,36,38,32,16,34,18,36,20,38,18,20,38,18,20,38,8,38,18,20,38,18,20,38,8,18,20,38]
def fmask_37 : Nat := fullMask 42
def base_37 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xc79944f3,0x2adad9944d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf8e188fc,0x336b6e188b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f3f01ff1f,0x4040002205),(0xffff0000ffff0000ffff0000ffff0000,0x3c7c0fe0fe0,0x19b1b540d60),(0xffffffff00000000ffffffff00000000,0x3f800fff000,0x224a4abd000)]
def steps_37 : List (Nat × Nat × Nat) := [(3,2,3),(2,2,3),(1,2,3),(1,0,3),(0,2,3),(3,0,3),(3,0,2),(1,0,2),(1,5,0),(2,7,4),(0,11,3),(3,0,7),(0,0,7),(3,10,2),(1,9,4),(2,0,9),(1,0,9),(0,2,8),(1,10,1),(3,11,3),(1,6,0),(1,10,2),(3,1,12),(3,2,8),(3,12,3),(2,12,3),(1,11,3),(1,12,3),(2,11,3),(0,12,3),(1,6,5),(2,14,0),(2,25,1),(3,1,7),(1,0,19),(2,1,9),(1,1,9),(2,0,19),(3,1,32),(0,14,0),(1,15,1),(1,22,4),(1,1,22),(2,31,4),(3,1,31),(1,15,4),(1,29,1),(2,32,4),(2,14,1),(1,1,19)]
def W_37 : BT Decor := buildWiresBT 6 base_37 steps_37
def autosL_37 : List (List (Nat × Nat)) := [[],[(1,2)]]
def autos_37 : BT (List (Nat × Nat)) := btOfList 1 autosL_37
def slicesL_37 : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,6),some (subcubeFast 4 0,5),some (subcubeFast 6 0,4),some (subcubeFast 2 0,5)]
def slices_37 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_37
def ps_37 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(0,[(1,2,3),(3,0,7)]),(3,[]),(0,[(1,2,3),(0,0,7)]),(0,[(0,2,3),(2,0,9)]),(0,[(0,2,3),(1,0,9)]),(0,[(2,2,3),(3,2,3)]),(0,[(3,0,3),(1,10,1)]),(0,[(1,0,2),(3,1,12)]),(0,[(3,2,3)]),(0,[(2,2,3)]),(0,[(1,2,3)]),(0,[(1,0,3)]),(0,[(0,2,3)]),(0,[(3,0,3)]),(0,[(3,0,2)]),(0,[(1,0,2)])]
def P_37 : BT (Option BoundPool) := buildPoolsBT 5 W_37 R_37 slices_37 ps_37
lemma gp_37 : goodPairs G_37 pos_37 neg_37 := goodPairs_of (by decide +kernel)
lemma base_37_ok : ∀ x ∈ base_37, faithful pos_37 neg_37 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_37_ok : btAll (fun x => faithful pos_37 neg_37 x ∧ x.1 < 2^128) W_37 := buildWiresBT_faithful base_37_ok
set_option maxRecDepth 500000 in
lemma autos_37_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_37 = G_37) autos_37 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_37_0_ok : sliceDirectCheck 32 0 0 R_37 G_37 R_11 G_11 = true := by decide +kernel
lemma sl_37_0 : Slice R_37 G_37 (subcubeFast 32 0) 6 := slice_fast_direct sl_37_0_ok low_11
lemma sl_37_1_ok : sliceDirectCheck 4 0 0 R_37 G_37 R_30 G_30 = true := by decide +kernel
lemma sl_37_1 : Slice R_37 G_37 (subcubeFast 4 0) 5 := slice_fast_direct sl_37_1_ok low_30
lemma sl_37_2_ok : sliceDirectCheck 6 0 0 R_37 G_37 R_0 G_0 = true := by decide +kernel
lemma sl_37_2 : Slice R_37 G_37 (subcubeFast 6 0) 4 := slice_fast_direct sl_37_2_ok low_0
lemma sl_37_3_ok : sliceDirectCheck 2 0 0 R_37 G_37 R_12 G_12 = true := by decide +kernel
lemma sl_37_3 : Slice R_37 G_37 (subcubeFast 2 0) 5 := slice_fast_direct sl_37_3_ok low_12
set_option maxRecDepth 500000 in
lemma slices_37_ok : btAll (fun o => ∀ p, o = some p → Slice R_37 G_37 p.1 p.2) slices_37 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_37 G_37 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_37_0) (forall_cons (fun _ h => by cases h; exact sl_37_1) (forall_cons (fun _ h => by cases h; exact sl_37_2) (forall_cons (fun _ h => by cases h; exact sl_37_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_37_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_37 G_37 c) P_37 := buildPoolsBT_sound slices_37_ok
def bk_37_init : BT (List (List Nat)) := BT.empty
lemma bk_37_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 (0 - 1) xs.toFinset) bk_37_init := trivial
def nodes_37_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_0 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_init 0 nodes_37_0 = true := by decide +kernel
def bk_37_0 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_0
set_option maxRecDepth 500000 in
lemma bk_37_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 0 xs.toFinset) bk_37_0 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_init_ok chk_37_0
def nodes_37_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_1 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_0 1 nodes_37_1 = true := by decide +kernel
def bk_37_1 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_1
set_option maxRecDepth 500000 in
lemma bk_37_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 1 xs.toFinset) bk_37_1 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_0_ok chk_37_1
def nodes_37_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_2 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_1 2 nodes_37_2 = true := by decide +kernel
def bk_37_2 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_2
set_option maxRecDepth 500000 in
lemma bk_37_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 2 xs.toFinset) bk_37_2 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_1_ok chk_37_2
def nodes_37_3 : List NodeSpec := [([53,36,2,3],[],[]),([2,3,39,54],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_3 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_2 3 nodes_37_3 = true := by decide +kernel
def bk_37_3 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_3
set_option maxRecDepth 500000 in
lemma bk_37_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 3 xs.toFinset) bk_37_3 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_2_ok chk_37_3
def nodes_37_4 : List NodeSpec := [([6,35,0,1,4],[],[]),([0,1,2,3,19],[],[]),([36,14,1,2,3],[],[0]),([14,16,1,2,3],[],[]),([37,0,2,3,4],[],[]),([38,16,2,3,4],[],[]),([38,17,2,3,4],[],[]),([0,1,2,7,19],[],[]),([1,2,3,19,39],[],[0]),([35,0,1,2,4],[],[]),([0,1,3,7,19],[],[]),([5,0,1,2,19],[],[]),([6,0,1,3,19],[],[]),([20,1,2,3,19],[],[]),([40,2,21,3,4],[],[]),([14,17,1,2,3],[],[]),([35,0,1,3,4],[],[]),([2,21,41,3,4],[],[]),([5,1,2,21,4],[],[]),([1,2,21,7,4],[],[]),([14,0,1,2,3],[],[]),([42,1,2,3,19],[],[]),([43,0,2,3,4],[],[]),([5,18,0,1,4],[],[]),([44,14,1,2,3],[],[]),([16,1,2,3,4],[],[]),([0,45,2,3,4],[],[]),([0,1,2,3,46],[],[]),([5,0,23,2,4],[],[]),([10,1,2,31,4],[],[]),([0,2,47,3,4],[],[]),([5,35,0,1,4],[],[]),([11,1,26,3,4],[],[]),([48,0,1,2,3],[],[]),([6,5,0,1,4],[],[]),([49,0,2,3,4],[],[]),([0,1,2,3,50],[],[]),([0,51,2,3,4],[],[]),([1,2,34,8,4],[],[]),([52,0,1,2,3],[],[]),([1,2,21,3,19],[],[]),([1,2,21,3,4],[],[]),([0,23,2,7,4],[],[]),([1,22,12,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_4 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_3 4 nodes_37_4 = true := by decide +kernel
def bk_37_4 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_4
set_option maxRecDepth 500000 in
lemma bk_37_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 4 xs.toFinset) bk_37_4 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_3_ok chk_37_4
def nodes_37_5 : List NodeSpec := [([0,13,1,2,3,4],[],[]),([6,5,0,1,3,4],[],[0]),([6,5,0,1,2,4],[],[0]),([14,0,1,2,3,7],[0],[0,1]),([15,0,1,2,3,4],[1,0],[0]),([11,10,1,2,3,4],[2],[0]),([14,0,1,2,3],[],[0,1]),([6,0,1,2,3,4],[],[0]),([16,1,2,3,4],[3],[]),([0,1,2,3,7,4],[4,1,0],[0,1]),([17,1,2,3,7,4],[2,5],[0]),([0,1,9,3,7,4],[],[0]),([18,0,1,2,3,4],[4],[0]),([0,1,9,2,7,4],[],[0,1]),([0,1,9,2,3,19],[0],[0,1]),([11,1,2,12,3,4],[0,2],[]),([0,1,2,3,19],[],[0,1]),([5,0,1,2,3,4],[],[0]),([6,0,1,9,3,4],[0],[0]),([0,1,2,8,7,4],[4],[]),([20,1,9,2,3,4],[2,6],[0,1]),([16,0,1,2,3,4],[],[]),([0,1,2,21,3,4],[],[]),([1,2,21,3,4],[7],[0]),([6,5,0,1,4],[8],[0]),([0,1,22,2,3,4],[1,4,0],[0]),([0,1,9,2,3,4],[4,1,0],[0,1]),([10,1,2,3,8,4],[2],[]),([5,0,1,2,8,4],[4],[]),([5,10,0,1,2,4],[4],[0]),([16,1,2,3,7,4],[4,3],[1,0]),([0,23,2,3,4],[9],[0]),([5,0,1,9,2,4],[0],[0,1]),([0,24,1,2,3,4],[],[]),([0,25,1,2,3,4],[1],[0]),([10,0,23,2,3,4],[1,2],[]),([0,1,2,26,3,4],[],[0]),([27,0,2,12,3,4],[1],[]),([6,0,1,2,7,4],[0],[0]),([28,0,1,2,3,4],[],[]),([29,0,1,2,3,4],[1],[0]),([27,0,2,3,4],[10],[]),([30,0,1,2,3,4],[],[]),([10,0,1,2,7,4],[4],[0]),([0,1,2,3,31,4],[1,0],[0]),([5,0,1,3,7,4],[0],[0]),([0,1,2,3,32,4],[1,0],[0]),([1,9,2,21,3,4],[4,7],[0]),([1,2,12,3,8,4],[2],[0]),([33,0,1,2,3,4],[],[]),([0,1,2,34,3,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_5 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_4 5 nodes_37_5 = true := by decide +kernel
def bk_37_5 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_5
set_option maxRecDepth 500000 in
lemma bk_37_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 5 xs.toFinset) bk_37_5 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_4_ok chk_37_5
def nodes_37_6 : List NodeSpec := [([5,0,1,2,3,4],[4,1,0,11],[0,1]),([6,0,1,2,3,4],[4,1,0,12],[0,1]),([0,1,2,3,7,4],[4,13,1],[0,1]),([0,1,2,3,8,4],[4,2,14],[0]),([0,1,9,2,3,4],[4,15,1],[0,1]),([10,0,1,2,3,4],[4,1,2,0,16],[0]),([11,0,1,2,3,4],[4,1,2,0,17],[0]),([0,1,2,12,3,4],[2,18],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_6 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_5 6 nodes_37_6 = true := by decide +kernel
def bk_37_6 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_6
set_option maxRecDepth 500000 in
lemma bk_37_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 6 xs.toFinset) bk_37_6 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_5_ok chk_37_6
def nodes_37_7 : List NodeSpec := [([0,1,2,3,4],[4,2,0],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_7 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_6 7 nodes_37_7 = true := by decide +kernel
def bk_37_7 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_7
set_option maxRecDepth 500000 in
lemma bk_37_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 7 xs.toFinset) bk_37_7 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_6_ok chk_37_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_ok : forestRootCheck R_37 G_37 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_in : bucketContainsBT bk_37_7 R_37 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_37 : Lower R_37 G_37 8 := lower_of_forestBT root_37_ok bk_37_7_ok root_37_in
def G_38 : Nat := 0xeeeeee00ee008800eeeeee00ee008800
def R_38 : List Nat := varsOf 59
lemma low_38_ok : carryOK [(0,2),(0,1)] R_38 G_38 R_31 G_31 = true := by decide +kernel
lemma low_38 : Lower R_38 G_38 8 := carry_of low_38_ok low_31
def G_39 : Nat := 0xfafafa00fa00a000fafafa00fa00a000
def R_39 : List Nat := varsOf 61
lemma low_39_ok : carryOK [(0,1)] R_39 G_39 R_31 G_31 = true := by decide +kernel
lemma low_39 : Lower R_39 G_39 8 := carry_of low_39_ok low_31
def G_40 : Nat := 0xffffff00ff88ee00ffffff00ff88ee00
def R_40 : List Nat := varsOf 59
lemma low_40_ok : carryOK [(0,2),(0,1)] R_40 G_40 R_37 G_37 = true := by decide +kernel
lemma low_40 : Lower R_40 G_40 8 := carry_of low_40_ok low_37
def G_41 : Nat := 0xffffff00ffa0fa00ffffff00ffa0fa00
def R_41 : List Nat := varsOf 61
lemma low_41_ok : carryOK [(0,1)] R_41 G_41 R_37 G_37 = true := by decide +kernel
lemma low_41 : Lower R_41 G_41 8 := carry_of low_41_ok low_37
def G_42 : Nat := 0xfefefe00fe80e800fefefe00fe80e800
def R_42 : List Nat := varsOf 63
def pos_42 : List Nat := [11,11,11,13,13,13,14,14,14,15,23,23,23,23,25,25,25,26,26,26,27,28,28,28,29,30,41,41,41,42,42,42,43,44,44,44,45,46,47,49,49,49,50,50,50,51,51,52,52,52,53,53,54,54,55,57,58,60,11,11,11,11,11,11,13,13,13,13,13,13,14,14,14,14,14,14,23,23,23,23,23,25,25,25,25,25,25,25,26,26,26,26,26,26,26,28,28,28,28,28,28,28,41,41,41,41,41,41,41,42,42,42,42,42,42,42,44,44,44,44,44,44,44,49,49,49,49,49]
def neg_42 : List Nat := [10,9,3,12,9,5,12,10,6,7,22,21,19,7,24,17,9,24,18,10,19,24,20,12,21,22,40,33,9,40,34,10,35,40,36,12,37,38,39,48,33,17,48,34,18,35,19,48,36,20,37,21,38,22,39,56,56,56,12,19,21,22,39,56,10,19,21,22,39,56,9,19,21,22,39,56,9,10,12,39,56,10,12,19,21,22,39,56,9,12,19,21,22,39,56,9,10,19,21,22,39,56,10,12,19,21,22,39,56,9,12,19,21,22,39,56,9,10,19,21,22,39,56,9,10,12,19,21]
def fmask_42 : Nat := fullMask 128
def base_42 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf8001fc000fff03ffccc63d11d11fe3f,0xcad5ab16ad5895d6584c63511911ba36),(0xcccccccccccccccccccccccccccccccc,0xfe0007f01ffc0fd707c61e21e3fc7,0x53668d5b346aa69b68707861c21c3785),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7f0003f8001ffff027f807e03e03ff8,0xa3874e9c3a74c71c747f007c03c02f68),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x7fffffffffe0fffff80007fffffc3ff,0x3c3870e1c38778618780000ab4ab40db),(0xffff0000ffff0000ffff0000ffff0000,0xf800003ffffff00003ffff8003fffc00,0xc5cb972e5cb90baebbaad6800376dc00),(0xffffffff00000000ffffffff00000000,0xffffffc00000000003fffffffc000000,0x60c183060c18c30c3d5adf76c000000)]
def steps_42 : List (Nat × Nat × Nat) := [(2,4,5),(1,4,5),(1,3,5),(3,3,4),(2,3,4),(2,3,5),(2,0,5),(1,0,5),(0,0,4),(3,0,4),(1,0,1),(3,0,3),(2,0,3),(0,3,4),(0,0,3),(2,0,1),(2,0,4),(1,3,4),(1,0,4),(1,0,3),(0,0,1),(2,23,5),(3,0,23),(1,19,5),(2,2,5),(1,1,5),(3,4,13),(2,1,5),(1,15,5),(2,24,5),(0,3,13),(3,22,3),(1,14,5),(2,16,5),(0,2,4),(2,10,5),(0,3,24),(1,17,5),(1,20,5),(1,22,5),(1,2,5),(3,2,4),(2,2,4),(1,2,4),(3,2,3),(2,2,3),(3,0,7),(1,2,3),(3,0,1),(0,0,23),(1,21,5),(1,21,4),(1,17,4),(3,12,3),(0,0,7),(0,2,3),(1,26,4),(0,16,3),(3,26,3),(3,21,3),(1,26,5),(1,12,4),(2,16,4),(1,20,4),(0,3,7),(1,0,29),(3,0,29),(2,0,29),(0,0,29),(3,19,13),(3,22,31),(1,42,5),(0,24,31),(2,1,38),(1,1,38),(3,17,31),(3,20,31),(3,2,7),(0,2,7),(3,21,7),(3,21,8),(3,2,23),(0,2,23),(3,21,23),(1,21,19),(0,3,46),(1,48,5),(3,48,3),(1,48,21),(3,21,46),(2,49,5),(1,40,5),(1,50,5),(1,51,21),(1,37,5),(3,26,7),(3,21,53),(1,1,44),(1,61,4),(1,21,61),(1,65,5),(0,16,49),(1,30,4),(1,21,40),(1,50,4),(1,61,5),(0,16,7),(0,16,23),(3,30,3),(3,26,23),(3,4,46),(0,16,8),(1,47,21),(0,16,46),(3,26,46),(1,47,5),(3,47,16),(0,16,53),(2,16,19),(2,16,61),(3,26,49),(1,47,26),(3,21,49),(2,1,44),(3,26,8),(0,3,49),(1,26,19),(1,48,26),(1,26,40),(1,50,26),(1,51,26),(1,2,66),(2,16,40),(3,14,31),(3,51,16),(3,15,31),(1,4,66),(1,50,21),(1,64,5),(3,26,16),(2,2,66),(1,63,5),(2,4,66),(3,48,16),(3,26,53),(1,26,61),(3,50,16),(1,73,5),(2,1,29),(3,74,1),(1,74,1),(1,1,29),(3,1,77),(1,83,21),(1,21,84),(1,21,29),(0,2,29),(1,93,5),(2,1,77),(3,2,29),(1,131,5),(1,145,2),(3,83,16),(2,16,29),(2,2,29),(3,145,2),(1,124,5),(1,40,66),(1,122,5),(2,2,147),(1,26,84),(1,26,29),(0,1,77),(1,2,29),(0,145,4),(1,116,26),(0,145,2),(1,107,5),(1,26,91),(1,26,131),(3,26,110),(0,2,147),(2,16,84),(3,145,4),(1,1,77),(1,26,111),(3,19,46),(1,83,26),(2,145,5),(1,47,66),(2,16,111),(1,145,4),(2,145,4),(3,145,3),(2,145,3),(0,145,3),(1,145,5),(2,145,2),(1,48,66),(1,26,70),(1,148,5),(2,49,66),(1,145,3),(2,16,97),(0,1,2),(3,2,190),(0,2,190),(1,178,2),(1,198,5),(1,165,21),(0,16,179),(1,201,5),(3,5,190),(3,165,16),(2,16,162),(1,165,26),(1,170,26),(3,26,179),(1,164,5),(3,26,163),(2,185,5),(3,178,2),(3,180,2),(1,189,5),(3,145,7),(0,145,7),(3,145,23),(3,182,3),(0,145,23),(3,170,16),(3,4,202),(1,199,5),(1,180,5),(1,199,4),(3,26,166),(2,167,5),(1,200,2),(1,21,162),(1,201,4),(3,198,3),(1,170,21),(3,194,3),(0,3,197),(2,1,2),(0,167,3),(1,26,162),(3,21,179),(1,182,5),(1,182,4),(1,131,66),(2,167,4),(0,3,202),(1,180,2),(2,197,5),(3,200,2),(1,1,2),(3,74,71),(1,194,4),(1,192,26),(1,74,210),(2,262,1),(3,262,1),(3,145,29),(0,145,29),(3,231,2),(1,262,1),(3,19,202),(1,248,5),(1,231,2),(0,167,7),(0,167,23),(2,167,19),(1,250,5),(3,182,8),(0,261,71),(2,145,29),(1,182,19),(0,167,8),(3,178,190),(1,145,29),(3,182,7),(3,182,23),(1,194,19),(0,262,1),(3,1,2),(3,182,167),(1,233,5),(1,245,5),(2,145,162),(3,210,261),(3,269,2),(1,269,2),(1,145,162),(0,291,23)]
def W_42 : BT Decor := buildWiresBT 9 base_42 steps_42
def autosL_42 : List (List (Nat × Nat)) := [[],[(0,1)],[(1,2)],[(0,1),(0,2)],[(0,2)],[(0,2),(0,1)]]
def autos_42 : BT (List (Nat × Nat)) := btOfList 3 autosL_42
def slicesL_42 : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,9),some (subcubeFast 6 1,4),some (subcubeFast 6 0,5),some (subcubeFast 17 0,5),some (subcubeFast 8 16,6),some (subcubeFast 2 4,5),some (subcubeFast 32 2,6),some (subcubeFast 2 8,5),some (subcubeFast 4 2,5),some (subcubeFast 3 0,5),some (subcubeFast 8 0,7),some (subcubeFast 0 16,7),some (subcubeFast 3 4,4),some (subcubeFast 17 8,4),some (subcubeFast 33 0,5),some (subcubeFast 34 8,4),some (subcubeFast 0 2,8),some (subcubeFast 2 0,8),some (subcubeFast 32 1,6),some (subcubeFast 32 4,6),some (subcubeFast 48 0,5),some (subcubeFast 1 2,5),some (subcubeFast 16 8,7),some (subcubeFast 32 16,6),some (subcubeFast 18 0,5),some (subcubeFast 0 1,8),some (subcubeFast 2 1,5),some (subcubeFast 20 0,5),some (subcubeFast 0 8,8),some (subcubeFast 0 4,8),some (subcubeFast 1 0,8),some (subcubeFast 33 8,4),some (subcubeFast 1 4,5),some (subcubeFast 4 0,8),some (subcubeFast 36 8,4),some (subcubeFast 4 8,5),some (subcubeFast 5 0,5),some (subcubeFast 16 0,8),some (subcubeFast 20 8,4),some (subcubeFast 32 8,7),some (subcubeFast 36 0,5),some (subcubeFast 1 8,5),some (subcubeFast 4 1,5),some (subcubeFast 48 8,4),some (subcubeFast 34 0,5),some (subcubeFast 5 2,4),some (subcubeFast 18 8,4)]
def slices_42 : BT (Option (Nat × Nat)) := btOfList 6 slicesL_42
def ps_42 : List PoolSpec := [(0,[(0,0,1),(1,0,1),(3,26,16),(0,145,2),(1,145,2),(3,182,167)]),(1,[]),(2,[]),(3,[]),(4,[(0,0,1),(1,0,1),(3,26,16)]),(5,[]),(6,[]),(0,[(0,0,1),(1,0,1),(3,26,16),(2,145,2),(3,145,2)]),(7,[]),(8,[]),(9,[]),(10,[(0,0,1),(1,0,1),(3,26,16)]),(11,[(0,0,1),(1,0,1),(3,26,16)]),(0,[(0,0,1),(1,0,1),(3,26,16),(0,145,2),(1,145,2)]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(4,[(0,0,1),(1,0,1)]),(17,[]),(18,[]),(0,[(0,0,1),(1,0,1),(3,26,16),(2,145,4)]),(19,[]),(20,[]),(4,[(2,0,1),(3,0,1)]),(0,[(0,0,1),(1,0,1),(3,26,16),(2,145,2)]),(21,[]),(0,[(0,0,1),(1,0,1),(3,26,16),(0,145,2)]),(0,[]),(10,[]),(22,[]),(23,[]),(24,[]),(0,[(0,0,1),(1,0,1),(3,26,16),(1,145,2)]),(23,[(0,0,1),(1,0,1)]),(25,[(1,4,5),(0,3,7),(1,26,70)]),(25,[(1,26,5),(0,3,4),(1,19,66)]),(25,[(0,3,4),(1,19,5)]),(25,[(0,3,4),(1,19,5),(1,26,29)]),(26,[]),(25,[]),(23,[(0,0,1),(1,0,1),(3,26,16)]),(19,[(0,0,1),(1,0,1),(3,26,16)]),(0,[(0,0,1),(1,0,1),(3,26,16),(1,30,4)]),(0,[(0,0,1),(1,0,1),(3,26,16),(3,4,46)]),(27,[]),(0,[(0,0,1),(1,0,1),(3,26,16),(2,2,4)]),(0,[(0,0,1),(1,0,1),(3,26,16),(1,2,4)]),(0,[(0,0,1),(1,0,1),(3,26,16),(3,4,202)]),(0,[(0,0,1),(1,0,1),(3,26,16),(3,145,2)]),(25,[(1,26,5),(0,3,4),(1,19,5)]),(0,[(0,0,1),(1,0,1),(3,26,16),(0,145,2),(1,182,4)]),(28,[]),(29,[]),(30,[]),(16,[(0,3,4),(1,19,5)]),(0,[(0,0,1),(1,0,1),(3,26,16),(1,145,4)]),(25,[(0,3,4),(1,19,5),(2,2,29)]),(29,[(0,3,4),(1,19,5)]),(0,[(0,0,1),(1,0,1),(3,26,16),(1,194,4)]),(31,[]),(25,[(0,3,4),(1,19,5),(2,1,29)]),(4,[(2,1,29)]),(16,[(2,0,5),(0,3,4),(1,19,5)]),(25,[(0,3,4),(1,19,5),(1,1,29)]),(4,[(1,1,29)]),(16,[(1,0,4),(0,3,24),(1,42,5)]),(32,[]),(11,[]),(33,[]),(11,[(2,0,1),(1,21,84)]),(29,[(0,3,4),(1,19,5),(1,0,29)]),(29,[(1,0,4),(0,3,24),(1,42,5)]),(34,[]),(4,[(2,0,1)]),(29,[(3,48,3),(1,93,5)]),(35,[]),(11,[(2,0,1),(3,0,1)]),(19,[(2,0,1),(3,0,1)]),(10,[(2,0,1),(3,0,1)]),(0,[(2,0,1),(3,0,1),(1,30,4)]),(25,[(1,26,5),(1,4,66)]),(36,[]),(4,[]),(28,[(1,0,1),(1,19,5),(2,16,29)]),(37,[(1,0,1),(2,16,29)]),(37,[]),(25,[(1,2,4),(0,3,49),(1,131,5)]),(16,[(1,2,4),(0,3,49),(1,131,5)]),(25,[(0,3,4)]),(29,[(0,3,4)]),(19,[(1,0,1)]),(25,[(1,26,5),(0,3,4)]),(4,[(0,0,1)]),(16,[(0,3,4),(1,19,5),(2,0,29)]),(19,[(0,3,4)]),(38,[]),(23,[(0,0,1)]),(25,[(0,3,4),(1,19,5),(1,2,29)]),(4,[(1,0,1)]),(25,[(1,4,5),(0,3,7)]),(10,[(0,0,1),(1,0,1)]),(11,[(0,0,1),(1,0,1)]),(25,[(2,3,4),(2,3,5)]),(25,[(2,3,4),(3,3,4)]),(25,[(2,3,4)]),(29,[(2,3,4)]),(39,[(1,0,1)]),(25,[(2,3,4),(2,10,5)]),(25,[(1,3,4),(2,23,5)]),(25,[(0,3,4),(1,26,19)]),(29,[(1,0,5),(0,3,4),(1,19,5)]),(19,[(0,0,1),(1,0,1)]),(40,[]),(0,[(0,0,1),(1,0,1),(3,2,4)]),(25,[(1,26,5),(2,4,66)]),(0,[(0,0,1),(1,0,1),(2,2,4),(1,48,26)]),(0,[(0,0,1),(1,0,1),(0,2,4)]),(25,[(1,2,5),(0,3,4),(1,19,5)]),(23,[(2,0,1),(3,0,1)]),(29,[(2,0,5),(0,3,4),(1,19,5)]),(0,[(0,0,1),(1,0,1),(3,4,46)]),(25,[(1,3,4),(3,26,23)]),(41,[]),(25,[(1,2,5),(0,3,4),(3,19,46)]),(0,[(2,0,1),(3,0,1),(1,2,4)]),(0,[(0,0,1),(1,0,1),(2,2,4)]),(0,[(2,0,1),(3,0,1),(3,4,46)]),(0,[(0,0,1),(1,0,1),(1,2,4)]),(25,[(1,26,5),(2,3,4)]),(39,[]),(37,[(1,0,1),(2,16,5)]),(29,[(0,3,4),(1,19,5),(2,0,29)]),(0,[(2,0,1),(3,0,1),(2,2,4)]),(4,[(1,0,29)]),(0,[(0,0,1),(1,0,1),(1,30,4)]),(42,[]),(43,[]),(10,[(1,0,29)]),(37,[(1,0,29)]),(28,[(1,19,5),(1,0,29)]),(37,[(1,0,5)]),(44,[]),(45,[]),(16,[(1,0,4),(0,3,24)]),(29,[(1,0,4),(0,3,24)]),(10,[(1,1,5)]),(4,[(1,1,5)]),(22,[(1,20,5),(1,1,5)]),(11,[(2,0,1)]),(17,[(1,4,5)]),(29,[(2,3,4),(2,10,5)]),(29,[(1,3,4),(2,23,5)]),(16,[(1,3,4),(2,23,5)]),(19,[(2,3,4)]),(10,[(2,0,1)]),(0,[(1,0,1),(2,2,4),(3,2,4)]),(22,[(1,0,1)]),(19,[(2,0,1)]),(0,[(2,0,1),(2,2,4)]),(29,[(3,48,3)]),(0,[(2,0,1),(2,2,4),(1,48,21)]),(0,[(2,0,1),(1,2,4)]),(25,[(1,2,5),(0,3,46)]),(16,[(1,2,5),(0,3,46)]),(11,[(1,0,1)]),(0,[(1,0,1),(0,3,46)]),(25,[(1,4,5),(3,26,7)]),(4,[(1,1,44)]),(22,[(1,20,5),(1,1,44)]),(29,[(1,61,4)]),(23,[(2,0,1)]),(23,[(1,0,1)]),(10,[(1,0,1)]),(0,[(1,0,1),(2,2,4)]),(29,[(2,3,4),(3,3,4)]),(16,[(2,3,4),(3,3,4)]),(0,[(2,0,1),(3,2,4)]),(16,[(2,3,4)]),(16,[(0,3,4)]),(0,[(2,0,1),(1,30,4)]),(29,[(1,0,5),(2,3,4)]),(0,[(1,0,1),(0,2,3)]),(0,[(1,0,1),(0,3,7)]),(29,[(1,4,5),(0,3,7)]),(37,[(1,0,1)]),(25,[(1,3,4)]),(16,[(1,3,4)]),(0,[(1,0,1),(0,3,4)]),(28,[(1,0,1),(1,19,5)]),(0,[(1,0,1),(3,30,3)]),(25,[(1,2,5),(3,4,46)]),(16,[(1,2,5),(3,4,46)]),(0,[(1,0,1),(3,4,46)]),(25,[(1,2,5),(2,3,4)]),(0,[(1,0,1),(3,2,4)]),(25,[(3,2,4),(1,47,5)]),(16,[(3,2,4),(1,47,5)]),(0,[(1,0,1),(3,2,4),(3,47,16)]),(0,[(1,0,1),(0,2,4)]),(25,[(3,2,3),(1,50,4)]),(16,[(3,2,3),(1,50,4)]),(0,[(1,0,1),(0,3,4),(2,16,19)]),(33,[(1,47,5)]),(0,[(0,0,1),(3,2,4)]),(19,[(0,0,1)]),(0,[(1,0,1),(3,2,3)]),(28,[(1,0,1),(2,16,61)]),(0,[(1,0,1),(0,2,3),(2,16,61)]),(22,[(1,0,1),(2,16,61)]),(11,[(0,0,1)]),(22,[(1,0,1),(2,16,5)]),(4,[(2,1,44)]),(46,[]),(0,[(1,0,1),(2,3,4)]),(29,[(2,0,5),(2,3,4)]),(10,[(0,0,1)]),(29,[(2,3,4),(2,3,5)]),(25,[(1,2,4),(0,3,49)]),(16,[(1,2,4),(0,3,49)]),(33,[(1,4,5)]),(37,[(1,2,5)]),(0,[(0,0,1),(3,4,46)]),(0,[(0,0,1),(2,2,4),(1,48,26)]),(0,[(0,0,1),(1,2,4)]),(0,[(1,0,1),(1,2,4)]),(0,[(0,0,1),(0,2,4)]),(0,[(1,0,1),(0,2,4),(2,16,40)]),(0,[(0,0,1),(2,2,4)]),(29,[(2,0,5),(0,3,4)]),(25,[(3,3,4)]),(25,[(1,3,4),(3,2,23)]),(16,[(1,3,4),(3,2,23)]),(16,[(3,0,4)]),(37,[(1,1,5)]),(0,[(0,0,1),(1,30,4)]),(29,[(1,0,5),(0,3,4)]),(10,[(2,1,5)]),(30,[(1,4,5)]),(0,[(1,0,1),(1,30,4)]),(37,[(1,0,1),(3,48,16)]),(0,[(1,0,1),(2,2,4),(3,48,16)]),(22,[(1,0,1),(3,48,16)]),(25,[(1,2,5),(0,3,4)]),(0,[(2,0,1),(3,4,46)]),(28,[(1,0,1)]),(22,[(1,1,5)]),(29,[(3,0,4)]),(0,[(0,0,4)]),(16,[(3,0,3)]),(29,[(3,0,3)]),(29,[(3,3,4)]),(16,[(3,3,4)]),(29,[(1,3,4)]),(22,[(1,20,5)]),(0,[(0,0,1)]),(25,[(1,2,3)]),(16,[(1,2,3)]),(25,[(3,2,3)]),(16,[(3,2,3)]),(25,[(3,2,4)]),(16,[(3,2,4)]),(25,[(1,2,4)]),(16,[(1,2,4)]),(16,[(1,0,4)]),(29,[(1,0,4)])]
def P_42 : BT (Option BoundPool) := buildPoolsBT 9 W_42 R_42 slices_42 ps_42
lemma gp_42 : goodPairs G_42 pos_42 neg_42 := goodPairs_of (by decide +kernel)
lemma base_42_ok : ∀ x ∈ base_42, faithful pos_42 neg_42 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_42_ok : btAll (fun x => faithful pos_42 neg_42 x ∧ x.1 < 2^128) W_42 := buildWiresBT_faithful base_42_ok
set_option maxRecDepth 500000 in
lemma autos_42_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_42 = G_42) autos_42 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_42_0_ok : sliceDirectCheck 32 0 0 R_42 G_42 R_33 G_33 = true := by decide +kernel
lemma sl_42_0 : Slice R_42 G_42 (subcubeFast 32 0) 9 := slice_fast_direct sl_42_0_ok low_33
lemma sl_42_1_ok : sliceDirectCheck 6 1 0 R_42 G_42 R_0 G_0 = true := by decide +kernel
lemma sl_42_1 : Slice R_42 G_42 (subcubeFast 6 1) 4 := slice_fast_direct sl_42_1_ok low_0
lemma sl_42_2_ok : sliceDirectCheck 6 0 0 R_42 G_42 R_13 G_13 = true := by decide +kernel
lemma sl_42_2 : Slice R_42 G_42 (subcubeFast 6 0) 5 := slice_fast_direct sl_42_2_ok low_13
lemma sl_42_3_ok : sliceDirectCheck 17 0 0 R_42 G_42 R_23 G_23 = true := by decide +kernel
lemma sl_42_3 : Slice R_42 G_42 (subcubeFast 17 0) 5 := slice_fast_direct sl_42_3_ok low_23
lemma sl_42_4_ok : sliceDirectCheck 8 16 0 R_42 G_42 R_26 G_26 = true := by decide +kernel
lemma sl_42_4 : Slice R_42 G_42 (subcubeFast 8 16) 6 := slice_fast_direct sl_42_4_ok low_26
lemma sl_42_5_ok : sliceDirectCheck 2 4 0 R_42 G_42 R_29 G_29 = true := by decide +kernel
lemma sl_42_5 : Slice R_42 G_42 (subcubeFast 2 4) 5 := slice_fast_direct sl_42_5_ok low_29
lemma sl_42_6_ok : sliceDirectCheck 32 2 0 R_42 G_42 R_28 G_28 = true := by decide +kernel
lemma sl_42_6 : Slice R_42 G_42 (subcubeFast 32 2) 6 := slice_fast_direct sl_42_6_ok low_28
lemma sl_42_7_ok : sliceDirectCheck 2 8 0 R_42 G_42 R_21 G_21 = true := by decide +kernel
lemma sl_42_7 : Slice R_42 G_42 (subcubeFast 2 8) 5 := slice_fast_direct sl_42_7_ok low_21
lemma sl_42_8_ok : sliceDirectCheck 4 2 0 R_42 G_42 R_29 G_29 = true := by decide +kernel
lemma sl_42_8 : Slice R_42 G_42 (subcubeFast 4 2) 5 := slice_fast_direct sl_42_8_ok low_29
lemma sl_42_9_ok : sliceDirectCheck 3 0 0 R_42 G_42 R_8 G_8 = true := by decide +kernel
lemma sl_42_9 : Slice R_42 G_42 (subcubeFast 3 0) 5 := slice_fast_direct sl_42_9_ok low_8
lemma sl_42_10_ok : sliceDirectCheck 8 0 0 R_42 G_42 R_34 G_34 = true := by decide +kernel
lemma sl_42_10 : Slice R_42 G_42 (subcubeFast 8 0) 7 := slice_fast_direct sl_42_10_ok low_34
lemma sl_42_11_ok : sliceDirectCheck 0 16 0 R_42 G_42 R_35 G_35 = true := by decide +kernel
lemma sl_42_11 : Slice R_42 G_42 (subcubeFast 0 16) 7 := slice_fast_direct sl_42_11_ok low_35
lemma sl_42_12_ok : sliceDirectCheck 3 4 0 R_42 G_42 R_0 G_0 = true := by decide +kernel
lemma sl_42_12 : Slice R_42 G_42 (subcubeFast 3 4) 4 := slice_fast_direct sl_42_12_ok low_0
lemma sl_42_13_ok : sliceDirectCheck 17 8 0 R_42 G_42 R_7 G_7 = true := by decide +kernel
lemma sl_42_13 : Slice R_42 G_42 (subcubeFast 17 8) 4 := slice_fast_direct sl_42_13_ok low_7
lemma sl_42_14_ok : sliceDirectCheck 33 0 0 R_42 G_42 R_22 G_22 = true := by decide +kernel
lemma sl_42_14 : Slice R_42 G_42 (subcubeFast 33 0) 5 := slice_fast_direct sl_42_14_ok low_22
lemma sl_42_15_ok : sliceDirectCheck 34 8 0 R_42 G_42 R_4 G_4 = true := by decide +kernel
lemma sl_42_15 : Slice R_42 G_42 (subcubeFast 34 8) 4 := slice_fast_direct sl_42_15_ok low_4
lemma sl_42_16_ok : sliceDirectCheck 0 2 0 R_42 G_42 R_41 G_41 = true := by decide +kernel
lemma sl_42_16 : Slice R_42 G_42 (subcubeFast 0 2) 8 := slice_fast_direct sl_42_16_ok low_41
lemma sl_42_17_ok : sliceDirectCheck 2 0 0 R_42 G_42 R_39 G_39 = true := by decide +kernel
lemma sl_42_17 : Slice R_42 G_42 (subcubeFast 2 0) 8 := slice_fast_direct sl_42_17_ok low_39
lemma sl_42_18_ok : sliceDirectCheck 32 1 0 R_42 G_42 R_11 G_11 = true := by decide +kernel
lemma sl_42_18 : Slice R_42 G_42 (subcubeFast 32 1) 6 := slice_fast_direct sl_42_18_ok low_11
lemma sl_42_19_ok : sliceDirectCheck 32 4 0 R_42 G_42 R_27 G_27 = true := by decide +kernel
lemma sl_42_19 : Slice R_42 G_42 (subcubeFast 32 4) 6 := slice_fast_direct sl_42_19_ok low_27
lemma sl_42_20_ok : sliceDirectCheck 48 0 0 R_42 G_42 R_15 G_15 = true := by decide +kernel
lemma sl_42_20 : Slice R_42 G_42 (subcubeFast 48 0) 5 := slice_fast_direct sl_42_20_ok low_15
lemma sl_42_21_ok : sliceDirectCheck 1 2 0 R_42 G_42 R_12 G_12 = true := by decide +kernel
lemma sl_42_21 : Slice R_42 G_42 (subcubeFast 1 2) 5 := slice_fast_direct sl_42_21_ok low_12
lemma sl_42_22_ok : sliceDirectCheck 16 8 0 R_42 G_42 R_10 G_10 = true := by decide +kernel
lemma sl_42_22 : Slice R_42 G_42 (subcubeFast 16 8) 7 := slice_fast_direct sl_42_22_ok low_10
lemma sl_42_23_ok : sliceDirectCheck 32 16 0 R_42 G_42 R_24 G_24 = true := by decide +kernel
lemma sl_42_23 : Slice R_42 G_42 (subcubeFast 32 16) 6 := slice_fast_direct sl_42_23_ok low_24
lemma sl_42_24_ok : sliceDirectCheck 18 0 0 R_42 G_42 R_20 G_20 = true := by decide +kernel
lemma sl_42_24 : Slice R_42 G_42 (subcubeFast 18 0) 5 := slice_fast_direct sl_42_24_ok low_20
lemma sl_42_25_ok : sliceDirectCheck 0 1 0 R_42 G_42 R_37 G_37 = true := by decide +kernel
lemma sl_42_25 : Slice R_42 G_42 (subcubeFast 0 1) 8 := slice_fast_direct sl_42_25_ok low_37
lemma sl_42_26_ok : sliceDirectCheck 2 1 0 R_42 G_42 R_12 G_12 = true := by decide +kernel
lemma sl_42_26 : Slice R_42 G_42 (subcubeFast 2 1) 5 := slice_fast_direct sl_42_26_ok low_12
lemma sl_42_27_ok : sliceDirectCheck 20 0 0 R_42 G_42 R_17 G_17 = true := by decide +kernel
lemma sl_42_27 : Slice R_42 G_42 (subcubeFast 20 0) 5 := slice_fast_direct sl_42_27_ok low_17
lemma sl_42_28_ok : sliceDirectCheck 0 8 0 R_42 G_42 R_36 G_36 = true := by decide +kernel
lemma sl_42_28 : Slice R_42 G_42 (subcubeFast 0 8) 8 := slice_fast_direct sl_42_28_ok low_36
lemma sl_42_29_ok : sliceDirectCheck 0 4 0 R_42 G_42 R_40 G_40 = true := by decide +kernel
lemma sl_42_29 : Slice R_42 G_42 (subcubeFast 0 4) 8 := slice_fast_direct sl_42_29_ok low_40
lemma sl_42_30_ok : sliceDirectCheck 1 0 0 R_42 G_42 R_31 G_31 = true := by decide +kernel
lemma sl_42_30 : Slice R_42 G_42 (subcubeFast 1 0) 8 := slice_fast_direct sl_42_30_ok low_31
lemma sl_42_31_ok : sliceDirectCheck 33 8 0 R_42 G_42 R_6 G_6 = true := by decide +kernel
lemma sl_42_31 : Slice R_42 G_42 (subcubeFast 33 8) 4 := slice_fast_direct sl_42_31_ok low_6
lemma sl_42_32_ok : sliceDirectCheck 1 4 0 R_42 G_42 R_30 G_30 = true := by decide +kernel
lemma sl_42_32 : Slice R_42 G_42 (subcubeFast 1 4) 5 := slice_fast_direct sl_42_32_ok low_30
lemma sl_42_33_ok : sliceDirectCheck 4 0 0 R_42 G_42 R_38 G_38 = true := by decide +kernel
lemma sl_42_33 : Slice R_42 G_42 (subcubeFast 4 0) 8 := slice_fast_direct sl_42_33_ok low_38
lemma sl_42_34_ok : sliceDirectCheck 36 8 0 R_42 G_42 R_2 G_2 = true := by decide +kernel
lemma sl_42_34 : Slice R_42 G_42 (subcubeFast 36 8) 4 := slice_fast_direct sl_42_34_ok low_2
lemma sl_42_35_ok : sliceDirectCheck 4 8 0 R_42 G_42 R_18 G_18 = true := by decide +kernel
lemma sl_42_35 : Slice R_42 G_42 (subcubeFast 4 8) 5 := slice_fast_direct sl_42_35_ok low_18
lemma sl_42_36_ok : sliceDirectCheck 5 0 0 R_42 G_42 R_14 G_14 = true := by decide +kernel
lemma sl_42_36 : Slice R_42 G_42 (subcubeFast 5 0) 5 := slice_fast_direct sl_42_36_ok low_14
lemma sl_42_37_ok : sliceDirectCheck 16 0 0 R_42 G_42 R_32 G_32 = true := by decide +kernel
lemma sl_42_37 : Slice R_42 G_42 (subcubeFast 16 0) 8 := slice_fast_direct sl_42_37_ok low_32
lemma sl_42_38_ok : sliceDirectCheck 20 8 0 R_42 G_42 R_3 G_3 = true := by decide +kernel
lemma sl_42_38 : Slice R_42 G_42 (subcubeFast 20 8) 4 := slice_fast_direct sl_42_38_ok low_3
lemma sl_42_39_ok : sliceDirectCheck 32 8 0 R_42 G_42 R_25 G_25 = true := by decide +kernel
lemma sl_42_39 : Slice R_42 G_42 (subcubeFast 32 8) 7 := slice_fast_direct sl_42_39_ok low_25
lemma sl_42_40_ok : sliceDirectCheck 36 0 0 R_42 G_42 R_16 G_16 = true := by decide +kernel
lemma sl_42_40 : Slice R_42 G_42 (subcubeFast 36 0) 5 := slice_fast_direct sl_42_40_ok low_16
lemma sl_42_41_ok : sliceDirectCheck 1 8 0 R_42 G_42 R_9 G_9 = true := by decide +kernel
lemma sl_42_41 : Slice R_42 G_42 (subcubeFast 1 8) 5 := slice_fast_direct sl_42_41_ok low_9
lemma sl_42_42_ok : sliceDirectCheck 4 1 0 R_42 G_42 R_30 G_30 = true := by decide +kernel
lemma sl_42_42 : Slice R_42 G_42 (subcubeFast 4 1) 5 := slice_fast_direct sl_42_42_ok low_30
lemma sl_42_43_ok : sliceDirectCheck 48 8 0 R_42 G_42 R_1 G_1 = true := by decide +kernel
lemma sl_42_43 : Slice R_42 G_42 (subcubeFast 48 8) 4 := slice_fast_direct sl_42_43_ok low_1
lemma sl_42_44_ok : sliceDirectCheck 34 0 0 R_42 G_42 R_19 G_19 = true := by decide +kernel
lemma sl_42_44 : Slice R_42 G_42 (subcubeFast 34 0) 5 := slice_fast_direct sl_42_44_ok low_19
lemma sl_42_45_ok : sliceDirectCheck 5 2 0 R_42 G_42 R_0 G_0 = true := by decide +kernel
lemma sl_42_45 : Slice R_42 G_42 (subcubeFast 5 2) 4 := slice_fast_direct sl_42_45_ok low_0
lemma sl_42_46_ok : sliceDirectCheck 18 8 0 R_42 G_42 R_5 G_5 = true := by decide +kernel
lemma sl_42_46 : Slice R_42 G_42 (subcubeFast 18 8) 4 := slice_fast_direct sl_42_46_ok low_5
set_option maxRecDepth 500000 in
lemma slices_42_ok : btAll (fun o => ∀ p, o = some p → Slice R_42 G_42 p.1 p.2) slices_42 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_42 G_42 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_42_0) (forall_cons (fun _ h => by cases h; exact sl_42_1) (forall_cons (fun _ h => by cases h; exact sl_42_2) (forall_cons (fun _ h => by cases h; exact sl_42_3) (forall_cons (fun _ h => by cases h; exact sl_42_4) (forall_cons (fun _ h => by cases h; exact sl_42_5) (forall_cons (fun _ h => by cases h; exact sl_42_6) (forall_cons (fun _ h => by cases h; exact sl_42_7) (forall_cons (fun _ h => by cases h; exact sl_42_8) (forall_cons (fun _ h => by cases h; exact sl_42_9) (forall_cons (fun _ h => by cases h; exact sl_42_10) (forall_cons (fun _ h => by cases h; exact sl_42_11) (forall_cons (fun _ h => by cases h; exact sl_42_12) (forall_cons (fun _ h => by cases h; exact sl_42_13) (forall_cons (fun _ h => by cases h; exact sl_42_14) (forall_cons (fun _ h => by cases h; exact sl_42_15) (forall_cons (fun _ h => by cases h; exact sl_42_16) (forall_cons (fun _ h => by cases h; exact sl_42_17) (forall_cons (fun _ h => by cases h; exact sl_42_18) (forall_cons (fun _ h => by cases h; exact sl_42_19) (forall_cons (fun _ h => by cases h; exact sl_42_20) (forall_cons (fun _ h => by cases h; exact sl_42_21) (forall_cons (fun _ h => by cases h; exact sl_42_22) (forall_cons (fun _ h => by cases h; exact sl_42_23) (forall_cons (fun _ h => by cases h; exact sl_42_24) (forall_cons (fun _ h => by cases h; exact sl_42_25) (forall_cons (fun _ h => by cases h; exact sl_42_26) (forall_cons (fun _ h => by cases h; exact sl_42_27) (forall_cons (fun _ h => by cases h; exact sl_42_28) (forall_cons (fun _ h => by cases h; exact sl_42_29) (forall_cons (fun _ h => by cases h; exact sl_42_30) (forall_cons (fun _ h => by cases h; exact sl_42_31) (forall_cons (fun _ h => by cases h; exact sl_42_32) (forall_cons (fun _ h => by cases h; exact sl_42_33) (forall_cons (fun _ h => by cases h; exact sl_42_34) (forall_cons (fun _ h => by cases h; exact sl_42_35) (forall_cons (fun _ h => by cases h; exact sl_42_36) (forall_cons (fun _ h => by cases h; exact sl_42_37) (forall_cons (fun _ h => by cases h; exact sl_42_38) (forall_cons (fun _ h => by cases h; exact sl_42_39) (forall_cons (fun _ h => by cases h; exact sl_42_40) (forall_cons (fun _ h => by cases h; exact sl_42_41) (forall_cons (fun _ h => by cases h; exact sl_42_42) (forall_cons (fun _ h => by cases h; exact sl_42_43) (forall_cons (fun _ h => by cases h; exact sl_42_44) (forall_cons (fun _ h => by cases h; exact sl_42_45) (forall_cons (fun _ h => by cases h; exact sl_42_46) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
lemma P_42_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_42 G_42 c) P_42 := buildPoolsBT_sound slices_42_ok
def bk_42_init : BT (List (List Nat)) := BT.empty
lemma bk_42_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 (0 - 1) xs.toFinset) bk_42_init := trivial
def nodes_42_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_0 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_init 0 nodes_42_0 = true := by decide +kernel
def bk_42_0 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_0
set_option maxRecDepth 500000 in
lemma bk_42_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 0 xs.toFinset) bk_42_0 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_init_ok chk_42_0
def nodes_42_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_1 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_0 1 nodes_42_1 = true := by decide +kernel
def bk_42_1 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_1
set_option maxRecDepth 500000 in
lemma bk_42_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 1 xs.toFinset) bk_42_1 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_0_ok chk_42_1
def nodes_42_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_2 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_1 2 nodes_42_2 = true := by decide +kernel
def bk_42_2 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_2
set_option maxRecDepth 500000 in
lemma bk_42_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 2 xs.toFinset) bk_42_2 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_1_ok chk_42_2
def nodes_42_3 : List NodeSpec := [([295,262,3,4],[],[]),([10,9,291,5],[],[]),([265,280,3,4],[],[]),([27,291,3,4],[],[]),([299,3,4,5],[],[]),([291,3,4,29],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_3 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_2 3 nodes_42_3 = true := by decide +kernel
def bk_42_3 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_3
set_option maxRecDepth 500000 in
lemma bk_42_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 3 xs.toFinset) bk_42_3 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_2_ok chk_42_3
def nodes_42_4 : List NodeSpec := [([74,210,280,3,4],[],[0]),([262,210,261,3,4],[],[0]),([216,2,3,4,177],[],[]),([170,165,145,3,4],[],[]),([294,2,3,4,29],[],[]),([295,74,3,4,71],[],[0]),([145,296,3,4,29],[],[]),([269,2,3,4,285],[],[]),([145,297,3,4,29],[],[]),([289,271,2,3,4],[],[]),([10,9,203,171,5],[],[0]),([27,203,171,3,4],[],[0]),([27,182,167,3,4],[],[0]),([182,276,3,4,5],[],[0]),([287,167,3,4,5],[],[0]),([167,3,282,4,5],[],[]),([291,19,3,4,5],[0],[0]),([6,291,3,4,5],[],[]),([11,291,3,4,5],[0],[]),([265,261,3,4,71],[],[0]),([249,290,262,3,4],[],[0]),([2,298,3,4,29],[],[]),([182,167,3,4,29],[],[0]),([291,3,4,5,8],[0],[]),([9,291,3,4,5],[],[0]),([291,3,4,5,7],[],[]),([167,3,4,253,8],[],[]),([203,171,3,4,29],[],[0]),([10,9,182,167,5],[],[0]),([6,167,3,4,253],[],[]),([10,291,3,4,5],[],[0]),([291,3,4,23,5],[1,0],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_4 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_3 4 nodes_42_4 = true := by decide +kernel
def bk_42_4 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_4
set_option maxRecDepth 500000 in
lemma bk_42_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 4 xs.toFinset) bk_42_4 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_3_ok chk_42_4
def nodes_42_5 : List NodeSpec := [([74,210,261,3,4,71],[],[0]),([1,265,2,3,4,71],[],[0]),([249,262,1,2,3,4],[],[0]),([266,262,1,2,3,4],[],[]),([0,213,3,4,5,190],[2],[]),([0,213,3,4,31,77],[],[]),([170,165,21,54,3,4],[],[0]),([221,16,2,3,4,29],[],[]),([262,210,1,2,3,4],[],[0]),([262,267,1,2,3,4],[],[]),([170,165,26,16,3,4],[],[0]),([16,2,251,3,4,29],[],[0]),([226,16,2,3,4,5],[],[]),([145,2,3,4,29,179],[3,4],[]),([145,162,2,3,4,29],[],[0]),([145,268,2,3,4,29],[],[]),([269,145,2,3,4,29],[],[0]),([30,145,2,3,4,29],[5],[]),([262,1,2,261,3,4],[],[0]),([145,270,3,4,5,7],[],[]),([145,2,3,4,46,29],[3,4],[]),([165,16,2,3,4,177],[],[]),([194,145,2,3,4,29],[4,3],[]),([262,1,271,2,3,4],[],[0]),([272,145,2,3,4,5],[6],[]),([145,2,3,4,5,273],[],[]),([145,274,3,4,5,7],[],[]),([10,9,145,171,2,5],[],[0]),([192,145,2,3,4,5],[6],[]),([27,145,171,2,3,4],[],[0]),([145,171,2,3,4,29],[],[0]),([203,171,3,4,5,7],[],[0]),([203,171,3,4,5,8],[5,1,7],[0]),([9,182,167,3,4,5],[],[0]),([145,2,275,3,4,5],[5],[]),([27,145,2,167,3,4],[],[0]),([145,2,276,3,4,5],[8],[0]),([6,145,2,3,4,253],[9],[0]),([145,2,3,4,253,8],[10,11],[0]),([145,2,167,3,4,29],[],[0]),([26,216,2,3,4,29],[],[0]),([10,9,145,2,167,5],[],[0]),([10,9,203,145,2,5],[],[0]),([182,145,2,3,4,29],[],[0]),([277,145,2,3,4,5],[],[]),([241,6,145,2,3,4],[5,12],[]),([6,203,171,3,4,5],[],[0]),([241,145,2,3,4,8],[11,5],[]),([27,203,145,2,3,4],[],[0]),([145,2,3,4,5,278],[],[]),([145,279,2,3,4,5],[],[]),([182,167,19,3,4,5],[9,13],[0]),([9,203,171,3,4,5],[],[0]),([74,1,2,280,3,4],[],[0]),([16,2,3,4,66,166],[10],[]),([281,145,2,3,4,29],[4,3],[]),([145,2,3,4,5,163],[],[]),([145,2,3,282,4,5],[],[0]),([182,167,3,4,5,7],[],[0]),([6,182,167,3,4,5],[],[0]),([145,2,283,3,4,5],[],[]),([284,0,2,3,4,5],[],[]),([170,145,2,3,4,29],[],[0]),([11,182,167,3,4,5],[13],[0]),([145,2,3,4,29,285],[],[0]),([145,286,2,3,4,5],[],[]),([145,287,2,3,4,5],[8],[0]),([145,2,288,3,4,5],[6],[]),([11,203,171,3,4,5],[7],[0]),([145,2,3,4,5,166],[],[]),([203,145,2,3,4,29],[],[0]),([10,182,167,3,4,5],[],[0]),([220,26,2,3,4,29],[],[0]),([182,167,3,4,23,5],[9,5,13],[0]),([203,171,19,3,4,5],[7],[0]),([16,2,3,4,66,163],[],[]),([167,3,4,5,253],[1,13],[0]),([10,203,171,3,4,5],[],[0]),([203,171,3,4,23,5],[5,1,14,7],[0]),([289,262,1,2,3,4],[],[0]),([16,2,3,4,177,179],[3],[0]),([27,182,145,2,3,4],[],[0]),([249,290,74,3,4,71],[],[0]),([54,2,243,3,4,29],[],[0]),([291,3,4,5],[1,0],[0]),([10,9,182,145,2,5],[],[0]),([145,2,3,4,5,292],[],[]),([145,2,3,4,202,29],[10],[]),([182,167,3,4,5,8],[13],[0]),([165,145,2,3,4,29],[],[0]),([192,16,2,3,4,66],[],[]),([145,2,3,4,5,293],[],[]),([16,2,3,4,46,177],[3],[]),([16,2,3,4,5,255],[10],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_5 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_4 5 nodes_42_5 = true := by decide +kernel
def bk_42_5 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_5
set_option maxRecDepth 500000 in
lemma bk_42_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 5 xs.toFinset) bk_42_5 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_4_ok chk_42_5
def nd_42_6_0 : List NodeSpec := [([74,210,1,2,3,4,71],[3],[0]),([211,0,1,3,4,5,77],[],[]),([16,2,3,4,206,66],[10,5,15,16],[]),([145,2,3,4,5,98],[5,14,17,4,3],[]),([0,1,212,3,4,5,77],[2,18],[]),([16,2,3,132,4,5,46],[3,19],[0]),([0,1,213,3,4,5,77],[20],[0]),([6,145,171,2,3,4,5],[3,14,9],[0]),([0,178,2,3,4,31,77],[21],[0]),([198,189,2,3,5],[10,3,15,1],[]),([145,2,3,4,5,214],[10,14,22,4,8],[]),([215,0,1,2,3,4,29],[],[]),([21,1,2,3,4,13,166],[23],[]),([0,1,216,2,3,4,29],[24],[0]),([0,1,2,3,4,56,166],[18],[]),([165,21,54,2,3,4,29],[],[0]),([21,54,2,3,4,29,179],[3,25],[0]),([0,178,2,3,4,5,190],[2],[0]),([203,145,2,19,3,4,5],[5,1,10,26],[0]),([30,21,54,2,3,4,29],[5],[0]),([182,145,2,3,4,5,8],[6,9,8,10,27,28],[0]),([145,2,3,4,5,217],[10,14,17,4,3],[]),([192,21,54,2,3,4,5],[6],[0]),([21,54,2,3,4,46,29],[3,25],[0]),([218,0,1,2,3,4,77],[29,18],[]),([21,54,2,3,4,5,163],[],[0]),([16,2,3,4,66,97],[10,6,8,5],[]),([0,1,2,3,4,172,29],[30,31,32],[]),([30,10,145,2,3,4,5],[9,15,12,17],[]),([1,16,2,3,4,153,29],[33,10],[]),([0,1,219,2,3,4,29],[],[]),([220,0,1,2,3,4,29],[3,33],[0]),([221,0,1,2,3,4,29],[],[0]),([170,165,26,0,1,3,4],[],[0]),([145,2,167,19,3,4,5],[27,10,5,9,3,34],[0]),([222,0,1,2,3,4,29],[],[]),([223,0,1,2,3,4,29],[],[]),([0,1,2,3,4,224,77],[30],[]),([6,16,2,3,4,66,137],[3,2,16,35],[]),([225,0,1,2,3,4,5],[],[]),([226,0,1,2,3,4,5],[],[0]),([16,2,3,205,4,5],[36,15],[]),([16,2,3,4,5,177],[17,37,3],[0]),([188,26,2,3,4,5,7],[],[]),([165,26,16,2,3,4,29],[3],[0]),([10,145,171,2,3,4,5],[9,15,14],[0]),([26,16,2,3,4,29,179],[38,3,19],[0]),([96,16,2,3,4,66],[10,5,8,6,14],[]),([16,2,3,4,29,177],[39,15,17],[0]),([227,0,1,3,4,5,77],[],[]),([30,26,16,2,3,4,29],[5],[0]),([145,228,3,4,5],[9,10,3,15],[]),([30,16,2,3,132,4,5],[17],[]),([145,2,3,4,5,229],[27,9,5,15],[]),([16,2,3,4,5,111,191],[2],[]),([181,16,2,3,4,5],[10,2,14],[]),([182,145,2,3,4,23,5],[12,3,9,10,27,5,28],[0]),([16,2,3,184,4,5],[14,2],[]),([192,26,16,2,3,4,5],[6],[0]),([154,12,16,2,3,4,29],[3,40],[]),([26,16,2,3,4,5,163],[],[0]),([26,16,2,3,4,5,166],[20,10,41],[0]),([186,16,2,3,4,5],[10,35,15],[]),([182,145,2,3,4,5,7],[9,12],[0]),([16,2,3,4,5,195],[14,15],[]),([145,2,70,3,4,5],[10,27,9,5,12,3,6,17,15],[]),([169,0,1,2,3,4,29],[],[]),([145,84,2,3,4,5,7],[5,12],[]),([145,230,2,3,4,5,7],[27,12,10],[]),([83,145,2,3,4,5,7],[9,5,12],[]),([26,16,162,2,3,4,29],[3,38],[0]),([231,145,2,3,4,5,7],[27,12],[0]),([6,182,145,2,3,4,5],[3,42],[0]),([11,10,145,2,4,5],[6,3,17,15],[]),([41,145,2,3,4,5],[10,27,9,5,12,15],[]),([232,2,3,4,5],[27,8,15,17],[]),([170,165,0,1,16,3,4],[],[0]),([170,26,16,2,3,4,29],[],[0]),([145,233,2,3,4,5],[5,8,10,9,3,12,6,11],[0]),([30,145,2,19,3,4,5],[3,43,9,17],[0]),([145,2,3,4,108,5],[1,11,8,44],[]),([192,0,1,2,3,4,66],[3],[0]),([10,145,2,3,4,5,46],[12,5,15,17],[]),([145,2,114,3,4,5],[1,3,12,6,5,17],[]),([116,145,2,3,4,5],[10,27,5,12,8,11,9,6,14,4,45],[]),([234,2,3,4,5],[10,8,15,17],[]),([0,1,235,2,3,4,29],[46],[]),([145,2,3,4,5,121],[10,27,5,15],[]),([145,2,19,3,4,5,46],[6,3,5,4],[0]),([11,203,145,2,3,4,5],[5,17,1,26],[0]),([48,47,145,3,5],[9,5,15,1],[]),([145,2,3,4,5,92],[1,47,4,8],[]),([145,2,93,3,4,5],[1,15,6,11],[0]),([96,145,2,3,4,5],[10,27,6,5,11,8,9,14,48,4],[]),([145,2,131,3,4,5],[5,14,15,6,11],[0]),([145,2,3,4,29],[15],[0]),([194,10,145,2,3,4,5],[10,15,12,17],[]),([145,2,167,3,4,5,8],[9,5,6,8,34],[0]),([236,145,2,3,4,5],[3,6,9,5,12,8,11,10,27,1,49],[]),([138,2,3,4,5,66],[10,2,15],[]),([145,2,3,4,5,237],[27,17,1,4,3],[]),([145,2,3,4,5,238],[10,9,5,15],[]),([10,9,145,2,5],[15,17],[0]),([145,2,3,4,239,5],[15,27,1,12,6,42],[]),([11,182,145,2,3,4,5],[9,17,11,28],[0]),([240,0,1,2,3,4,5],[],[]),([241,145,2,3,4,5],[6,9,5,11,8,3,12,27,34],[0]),([9,203,145,2,3,4,5],[5,1],[0]),([145,242,3,4,5],[5,8,10,15],[]),([0,1,2,243,3,4,29],[46],[0]),([145,2,3,4,5,111],[1,17,4,3],[]),([145,2,3,4,244,5],[10,15,14,12,6,42],[]),([11,145,171,2,3,4,5],[9,17,14,50],[0]),([145,171,2,3,4,5,8],[10,27,8,14,9,50],[0]),([170,165,21,0,1,3,4],[],[0]),([9,145,171,2,3,4,5],[3,14,9],[0]),([203,145,2,3,4,5,7],[5,1],[0]),([16,2,3,4,66,29],[17,51,5,3],[]),([145,171,2,3,4,23,5],[10,27,8,14,9,50],[0]),([145,2,3,4,104,5],[1,15,12,6,42],[]),([145,2,3,4,5,29],[17,10,27,9,5,3],[0]),([145,2,245,3,4,5],[3,8,10,15,9,5,6,11],[0]),([145,2,3,4,110,5],[5,14,15,12,6,42],[]),([16,2,3,4,5,29,177],[3],[]),([203,145,2,3,4,5,8],[5,8,1,26],[0]),([203,171,3,4,5],[5,9,7],[0]),([16,2,3,4,5,66,195],[5],[]),([145,2,167,3,4,5,7],[5,9,12],[0]),([145,171,2,19,3,4,5],[3,14,9,50],[0]),([10,203,145,2,3,4,5],[5,15,1],[0]),([145,88,3,4,5],[9,8,15,17],[]),([246,0,1,2,3,4,29],[],[]),([9,145,2,167,3,4,5],[5,9,3,4],[0]),([10,145,2,167,3,4,5],[9,5,12,15],[0]),([145,2,167,3,4,23,5],[10,27,9,5,3,12,34],[0]),([145,2,91,3,4,5],[5,14,3,12,6,9,17],[]),([145,2,247,3,4,5],[6,8,10,9,5,3,12,27,17],[]),([145,2,248,3,4,5],[8,3,27,15,9,5,6,11],[0]),([249,74,1,2,3,4,71],[],[0]),([145,2,250,3,4,5],[8,9,27,5,3,12,6,11],[0]),([0,1,2,251,3,4,29],[46],[0]),([148,16,2,3,4,5,137],[2,35],[]),([27,145,2,3,4],[17,15],[0]),([182,167,3,4,5],[9,5,13],[0]),([10,16,2,3,4,66,46],[5,15,17],[]),([9,182,145,2,3,4,5],[3,4],[0]),([21,54,2,3,4,5,166],[],[0]),([194,145,2,19,3,4,5],[3,10,4,6],[0]),([0,1,252,2,3,4,29],[],[]),([6,145,2,167,3,4,5],[5,9,3,42],[0]),([10,145,2,3,4,5,202],[12,27,15,17],[]),([10,182,145,2,3,4,5],[9,15,12],[0]),([145,2,3,4,5,253],[10,9,28,11,8,3,12],[0]),([145,2,3,4,254,5],[10,9,12,4,52,42],[]),([193,16,2,3,4,5,7],[],[]),([0,1,2,3,4,46,177],[3],[0]),([165,0,1,2,3,4,177],[],[0]),([0,1,2,3,4,5,255],[18,41,53,54],[0]),([182,145,2,19,3,4,5],[3,9,28],[0]),([256,145,2,3,4,5],[3,9,5,12,8,11,42,27,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_6_0 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_5 6 nd_42_6_0 = true := by decide +kernel
def nd_42_6_1 : List NodeSpec := [([0,1,2,3,4,66,166],[55,30],[0]),([146,16,2,3,4,5,142],[3,5],[]),([21,54,162,2,3,4,29],[3,33],[0,1]),([6,203,145,2,3,4,5],[5,1],[0]),([16,2,3,4,5,66,173],[3],[]),([16,2,3,4,5,191],[10,2,17],[]),([16,2,3,185,4,5],[14,15],[0]),([146,6,16,2,3,4,66],[5,35,3,16],[]),([145,2,19,3,4,5,202],[6,3,27],[0]),([48,47,16,3,5,66],[2,5,1,15],[]),([16,2,93,3,4,5,66],[6],[0]),([169,0,1,162,2,3,4],[38,56],[]),([145,2,257,3,4,5],[8,6,27,9,5,3,12,10,17],[]),([170,21,54,2,3,4,29],[],[0]),([145,171,2,3,4,5,7],[9,14],[0]),([145,258,3,4,5],[5,10,3,15],[]),([16,2,19,3,4,66,46],[16,5,3],[0]),([259,145,2,3,4,5],[6,3,9,5,11,8,10,27,1,57,4],[]),([16,2,3,4,66,46,142],[2,5,16,3],[]),([148,16,2,3,4,66,46],[5,2,16,3],[]),([207,16,2,3,4,5,66],[5],[]),([0,1,2,3,4,66,163],[20],[0]),([117,2,3,4,66],[10,8,15,17],[]),([16,2,131,3,4,5,66],[6,16],[0]),([26,16,2,3,4,46,29],[3,19],[0]),([145,260,3,4,5],[9,8,10,15],[]),([0,1,2,3,4,177,179],[3],[0]),([87,145,3,4,5],[5,8,15,17],[]),([16,2,3,4,92,66],[10,6,8],[]),([74,1,2,261,3,4,71],[38],[0]),([169,170,0,1,2,3,4],[58,59],[]),([262,1,2,3,4],[15],[0,2]),([39,0,1,2,3,4,163],[41],[]),([145,2,3,4,263,5],[10,14,4,60],[]),([203,145,2,3,4,23,5],[5,8,1,10,26],[0]),([16,2,3,4,5,204],[10,2],[]),([11,145,2,167,3,4,5],[9,5,11,17,34],[0]),([16,2,3,4,66,111],[10,2,17,3],[]),([16,2,3,4,98,66],[10,17,14,3],[]),([73,154,16,2,3,4,29],[3,24],[]),([145,2,3,4,5,97],[10,27,9,15],[]),([164,158,0,2,3,4,5],[],[0]),([264,0,1,2,3,4,5],[29],[]),([16,2,3,4,5,66,204],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_6_1 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_5 6 nd_42_6_1 = true := by decide +kernel
def nodes_42_6 : List NodeSpec := nd_42_6_0 ++ nd_42_6_1
set_option maxRecDepth 500000 in
lemma chk_42_6 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_5 6 nodes_42_6 = true := by
  unfold nodes_42_6 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_42_6_0, chk_42_6_1⟩
def bk_42_6 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_6
set_option maxRecDepth 500000 in
lemma bk_42_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 6 xs.toFinset) bk_42_6 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_5_ok chk_42_6
def nd_42_7_0 : List NodeSpec := [([0,1,2,3,4,153,29],[3,24,33,56,46,59,15,32,61],[0,2]),([73,154,0,1,2,3,4,29],[3,33,56,38,24],[0]),([154,0,1,2,3,4,29,71],[38,3,62,24,33,56,63],[]),([74,1,2,3,4,71],[3,38,15],[0,2]),([155,0,2,3,4,29],[3,33,15,24],[]),([0,156,2,3,4,29],[3,24,56,15],[]),([154,12,0,1,2,3,4,29],[3,38,56,33,40,24],[0]),([12,0,1,2,3,4,29,157],[56,33,64,24,3,38,32],[]),([0,1,2,3,4,13,29,157],[65,27,3,33,66,32],[]),([158,0,1,2,3,4,5,77],[32,30,20,67],[0]),([159,0,1,2,3,4,5,7],[68,69,70,1],[]),([0,1,2,160,3,4,5,7],[71,23],[]),([0,1,2,3,4,5,29,161],[3],[]),([21,0,1,162,2,3,4,29],[3,46,38,56,33],[0]),([21,1,2,3,4,29,71],[3,38,72,24,33,15],[]),([0,1,2,3,4,31,77],[21,67,73,32,30],[3,0]),([0,1,2,3,4,29,161],[3,56,46,59,15],[]),([21,0,1,2,3,4,46,29],[59,46,3,74,75],[0]),([21,0,1,2,3,4,5,163],[76,77,18,40],[0]),([164,0,1,2,3,4,5,77],[18,20],[0]),([21,1,2,131,3,4,5,13],[23,6,41,16],[0]),([21,54,2,70,3,4,5],[15,17,9,5,78],[0]),([83,21,54,2,3,4,5,7],[9,5,78],[0]),([73,72,1,2,3,4],[3,24,15],[0,3,4]),([10,9,21,54,2,5],[15,33,17],[0]),([41,21,54,2,3,4,5],[18,40,27,9,5,78,15,17],[0]),([87,21,54,3,4,5],[5,68,8,15],[0]),([30,21,54,2,19,3,4,5],[3,79,9,17],[0]),([0,1,2,3,4,5,71,157],[65,3,33,18],[]),([165,21,0,1,2,3,4,29],[3,24,38],[0]),([21,0,1,2,3,4,5,166],[23,46,18,40,55],[0]),([21,54,2,3,4,108,5],[9,2,80,8,81],[0]),([21,54,2,19,3,4,5,46],[6,3,5,25],[0]),([21,54,2,93,3,4,5],[9,2,15,6,80],[0]),([145,2,167,3,4,5],[27,5,14,1,8,3,6,34],[0]),([0,1,2,131,3,4,5,66],[6,30,16,31],[0]),([11,10,21,54,2,4,5],[6,3,17,15],[0]),([16,2,3,4,5,66,142],[16,82,2,5,17,3],[0]),([21,54,2,3,4,5,97],[3,33,9,15],[0]),([0,1,2,131,3,4,5,56],[6,40],[0]),([0,1,2,3,4,66,111],[83,2,17,84,3],[0]),([0,1,168,2,3,4,5,7],[70,41,69,46],[]),([21,54,88,3,4,5],[9,2,8,15],[0]),([169,0,1,2,3,4,5,29],[41],[0]),([26,0,1,2,3,4,5,166],[32,20,55,41,18],[0]),([145,2,3,4,49,5],[5,14,3,15,48,4,9],[0]),([165,0,1,16,2,3,4,29],[38,3,56,33,24,46,59],[0]),([21,54,2,3,4,29],[3,33,15],[0]),([170,0,1,16,2,3,4,29],[46,38,58,24],[0]),([21,54,2,114,3,4,5],[9,2,3,78,6,5,17],[0]),([48,47,21,54,3,5],[9,5,15],[0]),([0,1,16,162,2,3,4,29],[38,3,56,33,46,59,24],[0]),([169,0,1,2,3,4,29],[3,33,46,59,30,31,32,38,56,85,86],[0]),([145,171,2,3,4,5],[5,9,27,8,14,50],[0]),([0,1,2,3,4,5,172],[55,41,20,18,70,54,30,87,10],[]),([0,1,16,2,3,4,5,163],[32,10,41],[0]),([0,1,2,3,4,5,173],[18,41,70,54,15],[]),([0,1,16,2,3,4,5,166],[88,55,89,20,10],[0]),([150,16,2,3,4,5],[10,5,17,15],[]),([0,1,2,3,4,5,174],[55,41,20,18,54,30,53,87,10],[]),([39,30,0,1,2,19,3,4],[90,91,6,14,92,9],[]),([10,21,54,2,3,4,5,46],[78,5,15,17],[0]),([175,0,1,2,3,4,5,147],[14,70],[]),([16,2,19,3,4,5,66],[3,6,10,17,93,5,2],[0]),([21,54,2,3,4,5,111],[9,2,17,25,3],[0]),([0,1,2,176,3,4,5,7],[23,69],[]),([0,1,2,3,4,5,29,177],[87,32,3],[0]),([165,26,0,1,2,3,4,29],[3,24],[0]),([0,178,1,2,3,4,5,77],[21,3,18,20],[0]),([170,26,0,1,2,3,4,29],[3,46,59],[0]),([26,0,1,2,3,4,29,179],[59,46,24,3,38,33,56,94],[0]),([180,145,2,3,4,5],[3,10,5,9,8,15,6,1,14],[0]),([0,1,2,3,4,29,177],[3,33,46,59,15,32,17],[0]),([73,1,16,2,3,4,5,29],[3,41,95,10],[0,1]),([30,26,0,1,2,3,4,29],[3,96,46,5],[0]),([181,0,1,2,3,4,5],[18,41,70,54,30,53,20,29,2,68,5],[0]),([182,145,2,3,4,5],[5,9,8,3,6,27,10,28],[0]),([0,1,2,3,4,5,183],[55,41,20,18,54,97],[]),([0,1,2,3,184,4,5],[68,5,87,69,29,2],[0]),([0,1,2,3,185,4,5],[68,5,15,29],[0]),([186,0,1,2,3,4,5],[18,41,70,54,30,53,20,29,98,68,5],[0]),([0,1,16,2,3,4,29,179],[99,59,3,100],[0]),([145,2,3,4,23,5],[8,3,15,10,27,17,9,5,6],[0]),([26,16,2,70,3,4,5],[15,101,102,17,5,9],[0]),([145,2,3,4,5,8],[8,15,6,10,27,9,5],[0]),([83,26,16,2,3,4,5,7],[3,9,5,103],[0]),([0,1,187,2,3,4,5,147],[21,10,6,54,14,70],[]),([11,10,26,16,2,4,5],[6,3,17,15,104],[0]),([21,54,2,3,4,5,121],[3,5,15],[0]),([170,21,0,1,2,3,4,29],[3,46,59],[0]),([10,9,26,16,2,5],[15,105,17],[0]),([146,16,2,3,4,5,66],[2,6,10,8,17,35,3,5,1],[0]),([0,1,2,3,4,5,137,142],[2,54,3,69],[]),([21,54,2,131,3,4,5],[68,5,15,6,80],[0]),([26,16,2,3,4,104,5],[2,9,35,15],[0]),([39,30,10,0,1,2,3,4],[106,107,108],[]),([41,26,16,2,3,4,5],[20,15,10,41,9,5,103,109,17],[0]),([188,0,1,2,3,4,5,7],[54,41,69,23],[0]),([27,26,16,2,3,4],[8,17,110,15],[0]),([145,189,2,3,4,5],[27,15,5,9,6,1],[0]),([87,26,16,3,4,5],[5,14,17],[0]),([26,113,2,3,4,5],[8,10,17,15],[0]),([26,16,2,3,4,5,29],[3,38,17,9,5],[0]),([26,0,1,162,2,3,4,29],[3,46,38,56,33],[0]),([21,54,84,2,3,4,5,7],[5,78],[0]),([16,2,3,132,4,5],[111,15,17],[0]),([30,10,26,16,2,3,4,5],[9,15,103,17],[0]),([0,1,2,3,4,5,77,190],[3,21,18,15,32,20],[0]),([21,1,2,3,4,13,29],[3,38,112,24,33,15],[]),([30,26,16,2,19,3,4,5],[3,113,9,5,17],[0]),([26,16,2,114,3,4,5],[2,9,17,3,103],[0]),([21,1,2,3,4,5,29,71],[3,40],[]),([0,1,2,3,132,4,5,46],[29,3,54,114,94],[0]),([26,16,2,3,4,5,121],[5,14,115,113,15],[0]),([146,6,0,1,2,3,4,66],[5,98,3,16],[0]),([48,47,26,16,3,5],[9,5,15],[0]),([6,145,2,3,4,5],[3,27,10,5,9,8,15,6],[0]),([26,16,2,93,3,4,5],[2,9,15,6,102],[0]),([148,16,2,3,4,5,66],[3,6,10,5,2,8,15,16,116],[0]),([16,2,3,4,66,8],[6,8,15,16,17,5],[0]),([133,16,2,3,4,5],[9,2,3,15,117,19],[0]),([26,16,2,131,3,4,5],[5,14,102,15,6],[0]),([21,54,2,3,4,5,29],[3,33,17,9,5],[0]),([26,16,2,3,4,5,97],[3,9,118,15],[0]),([0,1,16,2,3,4,46,29],[119,74,59,3,100],[0]),([21,54,2,3,4,104,5],[9,2,15,78,6,120],[0]),([138,26,2,3,4,5],[3,9,15],[0]),([12,1,16,2,3,4,29],[3,33,17,38,64,121,24],[0]),([51,50,26,16,4,5],[9,5,17],[]),([116,26,16,2,3,4,5],[20,103,5,41,10,8,102,9,6,14,122,19],[0]),([115,16,2,3,4,5],[8,10,17,123,3,15],[0]),([0,1,2,3,4,5,111,191],[70,23,2],[0]),([27,21,54,2,3,4],[124,8,17,15],[0]),([9,145,2,3,4,5],[3,27,10,5,9,8,17],[0]),([192,0,1,16,2,3,4,5],[114,41,10,6,125],[0]),([10,145,2,3,4,5],[10,15,27,9,5,6,17],[0]),([10,26,16,2,3,4,5,46],[103,5,15,17],[0]),([96,21,54,2,3,4,5],[18,68,41,5,80,8,6,9,126,25],[0]),([30,145,2,3,4,5],[9,27,10,8,3,6,1,17],[0]),([193,0,1,2,3,4,5,7],[5,69,70],[0]),([145,40,2,3,4,5],[3,27,10,9,15,1,6],[0]),([145,2,3,53,4,5],[5,8,10,27,15,17],[]),([6,16,2,3,4,66],[6,3,5,8,20,15,16],[0]),([0,1,2,93,3,4,5,66],[6,30,77],[0]),([0,1,2,3,4,66,29],[3,33,46,59,5,15,32,17],[0]),([145,61,2,3,4,5],[9,27,10,1,5,3,6,8,15,17,4],[0]),([194,145,2,3,4,5],[6,9,10,5,8,3,14,17],[0]),([0,1,2,3,4,5,66,195],[5],[0]),([26,16,2,3,4,5,111],[2,9,17,19,3],[0]),([196,0,1,2,3,4,5,111],[9],[]),([145,2,3,4,197,5],[27,3,1,15,57,4,10],[0]),([145,2,3,4,5,7],[4,15,6,10,27,9,5,17],[0]),([198,145,2,3,4,5],[3,9,10,5,8,27,6,1,15,14,22,4],[0]),([0,1,2,3,4,5,97,173],[3],[]),([145,2,19,3,4,5],[3,27,10,15,17,5,9,6],[0]),([47,145,2,3,4,5],[5,27,10,8,15,6,14],[0]),([145,199,2,3,4,5],[8,27,15,5,9,10,6,1,17,4],[0]),([96,0,1,2,3,4,66],[55,20,5,8,6,68,84],[0]),([26,16,2,3,4,5,98],[5,14,17,19,3],[0]),([48,16,2,3,4,5,66],[2,6,10,8,5,127,16,1,3,15],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_7_0 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_6 7 nd_42_7_0 = true := by decide +kernel
def nd_42_7_1 : List NodeSpec := [([51,145,2,3,4,5],[9,27,10,5,15,17],[]),([200,145,2,3,4,5],[8,10,5,9,15,17],[0]),([201,145,2,3,4,5],[8,9,10,5,27,3,6,15,1,14,17,4],[0]),([26,16,88,3,4,5],[2,9,17],[0]),([145,2,3,4,5,202],[27,1,6,17,3],[0]),([26,16,2,3,4,110,5],[5,14,103,35,15],[0]),([0,1,2,3,4,5,177],[3,33,17,70,54],[0]),([203,145,2,3,4,5],[5,9,8,1,10,26],[0]),([127,16,2,3,4,5],[5,10,15,14],[0]),([148,0,1,2,3,4,5,137],[54,2,87,98],[0]),([21,54,2,91,3,4,5],[68,5,3,78,6,9,17],[0]),([50,145,2,3,4,5],[5,27,10,9,3,6,14,8,15,17,4],[0]),([116,21,54,2,3,4,5],[18,68,41,5,78,8,80,9,6,25,128],[0]),([146,0,1,2,3,4,5,142],[69,3,70,5],[0]),([6,0,1,2,3,4,66,137],[5,3,2,16,98],[0]),([10,0,1,2,3,4,66,46],[5,15,17],[0]),([16,2,3,4,5,66,137],[16,14,17,3,35,2],[0]),([26,16,2,91,3,4,5],[5,14,102,17,103,3],[0]),([30,10,21,54,2,3,4,5],[9,15,78,17],[0]),([26,140,2,3,4,5],[9,2,17],[]),([0,1,2,3,4,5,195],[3,5,15],[0]),([16,2,3,4,49,5,66],[10,6,14,3,8,15,2,129,16],[0]),([0,1,2,3,4,66,46,142],[2,5,16,3],[0]),([148,0,1,2,3,4,66,46],[5,2,16,3],[0]),([96,26,16,2,3,4,5],[20,5,10,41,102,8,6,9,14,129,19],[0]),([0,1,2,3,4,5,66,204],[2],[0]),([54,89,2,3,4,5],[8,124,3,15,17],[0]),([0,1,2,3,205,4,5],[15,17,70,54],[0]),([10,16,2,3,4,5,66],[10,6,2,5,3,8,15,17,130],[0]),([39,0,1,2,3,4,29],[131,33,3,46,59,30,32,41,38,18,9,17,132],[]),([145,2,3,4,5,46],[5,14,6,17,3],[0]),([0,1,2,3,4,206,66],[3,33,5,15,16],[0]),([0,1,2,3,4,5,204],[83,2,30,53,87,54],[0]),([207,0,1,2,3,4,5,66],[5],[0]),([16,40,2,3,4,5,66],[3,6,10,1,8,15,118,16],[0]),([16,2,151,3,4,5],[9,8,15,2,17,19],[0]),([26,16,2,3,4,5,92],[2,9,127,35,19,8],[0]),([0,1,2,3,4,92,66],[83,2,8,84,6],[0]),([21,0,1,2,3,4,29,179],[59,46,3,33,56,75],[0]),([11,145,2,3,4,5],[10,17,27,9,5,3,15,4,6],[0]),([0,1,2,3,4,5,66,173],[3],[0]),([154,0,1,2,3,4,13,29],[38,3,62,10,24,63],[]),([0,1,2,3,4,5,191],[83,2,17,87,69],[0]),([16,61,2,3,4,5,66],[2,6,10,1,5,35,3,17,15],[0]),([145,2,3,208,4,5],[27,8,9,5,15,17],[]),([0,1,2,19,3,4,66,46],[16,5,3],[0]),([0,1,2,3,4,98,66],[68,5,17,3,84],[0]),([209,0,1,2,3,4,5,97],[9],[]),([192,26,0,1,2,3,4,5],[20,114,6,91],[0]),([26,16,2,3,4,29],[3,38,15],[0]),([73,1,16,2,3,4,29],[3,33,38,95,133,24,15],[0]),([26,16,2,19,3,4,5,46],[5,6,3,19],[0]),([39,0,1,2,93,3,4,5],[30,6,77],[0]),([0,1,2,3,4,56,29],[3,131,38,18,46,59,15],[]),([21,54,2,3,4,5,92],[9,2,134,25,8],[0]),([21,54,2,3,4,5,98],[68,5,17,25,3],[0]),([192,21,0,1,2,3,4,5],[18,40,6,91,46],[0]),([26,117,2,3,4,5],[8,6,10,15],[0]),([30,0,1,16,2,3,4,29],[46,38,96,5,24,14],[0]),([26,0,1,2,3,4,46,29],[59,46,3,74,24,94],[0]),([0,1,2,3,4,66,97],[3,33,70,6,31,8],[0]),([30,0,1,2,3,132,4,5],[70,23,17],[0]),([0,1,2,3,4,29,71,157],[65,24,3,33,56,66,135],[]),([48,145,2,3,4,5],[9,27,10,8,5,6,1,3,15,47,4],[0]),([30,21,0,1,2,3,4,29],[3,96,46,5],[0]),([48,47,0,1,3,5,66],[2,5,3,15],[0]),([26,0,1,2,3,4,5,163],[32,20,77],[0]),([26,16,84,2,3,4,5,7],[6,5,103],[0]),([26,16,2,3,4,108,5],[2,9,136,102,8],[0]),([16,2,3,4,66,46],[6,5,16,17,3],[0]),([21,54,2,3,4,110,5],[68,5,15,78,6,120],[0]),([50,16,2,3,4,5,66],[5,6,10,2,35,3,17,14,15],[0]),([47,16,2,3,4,5,66],[5,6,10,8,15,115,16,14],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_7_1 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_6 7 nd_42_7_1 = true := by decide +kernel
def nodes_42_7 : List NodeSpec := nd_42_7_0 ++ nd_42_7_1
set_option maxRecDepth 500000 in
lemma chk_42_7 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_6 7 nodes_42_7 = true := by
  unfold nodes_42_7 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_42_7_0, chk_42_7_1⟩
def bk_42_7 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_7
set_option maxRecDepth 500000 in
lemma bk_42_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 7 xs.toFinset) bk_42_7 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_6_ok chk_42_7
def nd_42_8_0 : List NodeSpec := [([0,1,2,3,4,5,29,71],[38,24,40,33,56,137,46,59,61,15,138],[0,2,1,5]),([72,0,1,2,3,4,29],[24,38,56,33,59,46,31,30,138],[0,3,4]),([73,0,1,2,3,4,29],[3,56,33,59,46,31,30,38,24,15],[0,2,3,4,1,5]),([0,1,2,3,4,29,71],[3,38,24,139,15,140,33,56,46,59,141,84],[0,2,3,4]),([12,0,1,2,3,4,29],[131,3,56,33,59,46,38,41,87,24],[0,2,3,4]),([74,0,1,2,3,4,29],[3,56,33,59,46,31,30,24,15],[0,2,3,4]),([75,0,1,2,3,4,5],[55,3,29,16,18,20,54,70,41,69,90,61,142],[3,4]),([0,1,2,3,4,76,5],[16,143,27,17,32],[]),([33,22,15,1,2,3,5],[55,32,41,21,33,68,46,31,84,1],[]),([0,1,2,3,4,45,31],[16,21,27,144,32,84],[]),([0,1,2,3,4,5,77],[21,30,32,20,18,70,54],[3,4,0,2]),([0,1,2,3,4,78,5],[21,143,15,54,70],[]),([0,1,2,42,3,4,5,31],[21,32,145,9,23,137,146,147,143,31],[3,0]),([79,0,1,2,3,4,5,38],[55,21,33,68,46,31,61,27,5,2],[]),([0,1,2,3,4,5,38,80],[16,33,144,61,6,32],[]),([0,81,1,2,3,4,5],[18,21,70,143,54,55,69,87,124,15],[]),([82,0,1,2,3,4,5],[53,16,41,143,54,70,69,87,27,17,144],[]),([0,1,2,3,4,44,31],[16,21,27,144,131,148,149,20],[]),([83,21,0,1,2,3,4,5,7],[23,6,21,3,9,68,69,24,150],[0]),([21,0,1,84,2,3,4,5,7],[6,46,9,69,24,151,5,150],[0]),([0,1,85,2,3,4,5],[6,20,3,41,40,54,70,53,30,138],[]),([0,1,86,2,3,4,5],[6,20,16,41,8,124,70,54,87,69,15],[]),([41,21,0,1,2,3,4,5],[18,69,40,138,55,9,5,150,15,109,152,74,61,17],[0]),([27,21,0,1,2,3,4],[124,131,61,110,153,77,69,31,8,154,15],[0]),([87,21,0,1,3,4,5],[54,5,68,14,53,84,31,61],[0]),([21,0,1,88,3,4,5],[9,2,53,84,31,61],[0]),([0,1,89,2,3,4,5],[8,124,41,40,20,3,15,17,61],[0]),([73,0,1,2,3,4,5,29],[3,56,33,59,46,31,30,24,41,27,10,68,83,15],[0,2,1,5]),([21,0,1,2,3,4,5,29],[3,38,59,46,31,30,61,131,40,24,33,56,9,5],[0]),([21,0,1,2,3,4,29],[3,38,59,46,31,30,24,33,56,15],[0]),([0,1,2,3,90,4,5],[3,33,40,15,61,1],[]),([30,10,21,0,1,2,3,4,5],[9,15,150,155,46,138,32,61],[0]),([21,0,1,2,91,3,4,5],[5,68,14,54,114,40,156,84,138,61,150,3],[0]),([48,47,0,1,16,3,5],[9,14,137,157,15,158],[0]),([30,21,0,1,2,19,3,4,5],[3,96,46,159,9,1,68,61],[0]),([48,21,54,2,3,4,5],[18,3,9,2,8,5,6,15,134,25],[0]),([10,21,0,1,2,3,4,5,46],[32,138,150,5,15,107,74,61],[0]),([21,0,1,2,19,3,4,5,46],[91,46,1,6,3,74,68,75],[0]),([21,0,1,2,3,4,5,92],[9,2,23,70,77,84,46,1,83,160,75,8],[0]),([21,0,1,2,93,3,4,5],[9,2,161,70,77,30,69,31,1,83,15,6,156],[0]),([94,0,1,2,3,4,5],[20,3,41,9,53,30,54,40,83,15,162,75],[]),([0,1,95,2,3,4,5],[6,20,5,68,30,53,87,69,74],[]),([96,21,0,1,2,3,4,5],[18,68,32,46,20,156,8,6,9,14,54,74,84,163,75],[0]),([21,0,1,2,3,4,5,97],[3,9,31,15,1],[0]),([21,0,1,2,3,4,5,98],[5,68,14,54,77,30,84,138,61,23,75,3],[0]),([0,1,16,2,91,3,4,5],[68,5,41,164,55,14,18,165,3,166,6,9,167],[0]),([51,50,21,0,1,4,5],[9,68,84,31,61],[]),([99,0,1,2,3,4,5],[20,68,41,9,18,69,87,40,83,124,15],[]),([0,1,2,3,4,5,100],[16,124,32,20,18,70,54],[3,4]),([101,0,1,2,3,4,5],[18,3,41,24,54,70,53,30,168,33,151,138],[]),([0,1,102,2,3,4,5],[5,68,41,9,18,87,69,29,40,124,15],[]),([0,1,2,3,4,5,44,103],[16,21,27,144,61,169,170,10],[]),([21,0,1,2,3,4,104,5],[9,2,171,70,31,30,69,46,1,83,15,150,6,172],[0]),([0,1,16,2,3,4,104,5],[137,9,144,1,30,31,69,46,32,173,174,3],[0]),([0,1,2,105,3,4,5],[68,9,137,40,83,15,61,75],[]),([0,1,16,2,3,4,5,92],[137,9,144,1,84,77,46,32,175,10,173,100,8],[0]),([50,21,1,2,3,4,5,13],[55,68,6,143,137,172,3,61,23,5,15],[]),([6,21,54,2,3,4,5],[18,6,41,21,3,5,9,8,15],[0]),([21,54,2,3,4,5,7],[6,21,25,15,9,5,17],[0]),([21,54,2,3,4,5,8],[6,21,8,15,9,5],[0]),([10,9,21,0,1,2,5],[15,105,176,46,61,33,177],[0]),([9,21,54,2,3,4,5],[18,3,33,5,9,8,17],[0]),([21,54,2,3,4,23,5],[124,8,18,41,3,15,9,5,17,6],[0,1]),([30,21,54,2,3,4,5],[18,6,41,21,9,8,3,17],[0]),([47,21,1,2,3,4,5,13],[55,3,6,143,68,124,15,178,41,16,137,1],[]),([21,54,61,2,3,4,5],[9,2,5,3,6,8,15,17,25],[0]),([21,54,40,2,3,4,5],[3,33,9,8,15,6],[0]),([30,26,16,2,3,4,5],[20,5,2,41,6,8,3,17],[0]),([11,21,54,2,3,4,5],[18,6,41,21,9,17,5,3,15,25],[0]),([21,54,2,3,53,4,5],[68,5,8,3,15,6,17],[0]),([10,0,1,2,3,4,5,56],[55,21,143,18,9,68,3,124,15,61,69,179,107,46],[]),([0,1,2,3,4,49,5,56],[68,143,18,9,32,3,124,84,31,163,6,46,40],[0]),([21,54,2,3,4,49,5],[68,5,3,15,126,25,9],[0]),([0,1,2,19,3,4,5,56],[3,18,143,180,68,9,46,91,15,61,40],[0]),([0,1,2,3,4,5,106],[6,16,124,84,70,54],[]),([0,1,107,2,3,4,5],[5,9,55,68,41,46,137,53,30,29,97],[0]),([21,0,1,2,3,4,108,5],[9,2,23,70,77,84,46,1,83,156,8,181],[0]),([64,0,1,2,3,4,5,46],[6,131,21,70,54,5,46,32,17,30,68,3,84],[]),([0,1,2,109,3,4,5],[3,33,40,9,15],[]),([21,0,1,2,3,4,110,5],[5,68,14,54,77,30,69,31,40,150,172,15],[0]),([10,21,1,2,3,4,5,13],[55,40,6,137,68,3,124,15,61,106,182],[]),([0,1,16,2,3,4,5,111],[137,9,144,1,30,131,46,84,183,114,10,174,100,3],[0]),([0,1,16,2,70,3,4,5],[15,17,41,101,55,174,184,18,20,74,185,10,31,69,5,9,186,166,158],[0]),([0,1,16,84,2,3,4,5,7],[46,6,23,24,69,5,166],[0]),([0,1,112,2,3,4,5],[6,55,21,70,10,54,53,30,138],[]),([10,9,0,1,16,2,5],[158,3,33,105,108,177,46,176],[0]),([10,9,26,0,1,2,5],[15,33,176,46,17],[0]),([0,1,113,2,3,4,5],[124,8,10,53,187,188,54,70,108,15,14],[0]),([0,1,16,2,3,4,5,29],[3,33,38,189,55,56,20,46,59,30,31,32,10,24,9,5,17,186,15,174],[0,1]),([0,1,16,2,3,4,29],[3,33,38,56,46,59,30,31,32,24,174,15,186,190],[0,1]),([0,1,16,2,114,3,4,5],[137,9,144,1,30,77,46,84,131,191,3,166],[0]),([115,0,1,2,3,4,5],[8,18,41,70,54,20,69,29,17,124,3,15],[0]),([116,0,1,16,2,3,4,5],[55,41,192,14,18,193,166,8,174,9,6,100,194],[0]),([21,1,2,3,4,49,5,13],[68,137,23,1,124,6,163],[0]),([0,1,117,2,3,4,5],[21,6,70,10,54,69,87,14,15],[0]),([50,0,1,2,3,4,5,56],[55,21,68,18,143,9,172,3,61,77,131,15,84],[]),([10,0,1,16,2,3,4,5,46],[32,6,138,166,5,15,195,74,107,108],[0]),([118,0,1,2,3,4,5],[20,3,41,54,18,53,30,40,15,68],[]),([0,1,119,2,3,4,5],[6,55,21,30,114,53,69,87,74],[]),([120,0,1,2,3,4,5],[18,5,41,30,53,87,69,29,70,68,74],[]),([0,1,16,2,3,4,5,121],[3,5,196,41,197,55,14,18,198,15,174],[0]),([27,0,1,16,2,3,4],[108,124,8,110,154,77,153,31,69,15,166],[0]),([0,1,122,2,3,4,5],[5,9,55,3,41,137,30,10,53,29,15,199,158],[0]),([0,1,16,2,3,4,5,97],[3,33,137,144,1,158,32,200,114,10],[0]),([0,1,123,2,3,4,5],[5,9,53,68,41,137,10,69,87,108],[]),([21,0,1,2,3,4,5,121],[5,3,14,31,15,178,40,159],[0]),([0,1,16,2,3,4,110,5],[68,5,55,14,41,201,18,202,15,174,166,158,6,173],[0]),([124,0,1,2,3,4,5],[55,3,41,10,54,70,69,29,14,15,203,174,186],[0]),([26,0,1,2,3,4,5,121],[5,3,54,204,31,15,205,206],[0]),([51,50,0,1,16,4,5],[9,14,137,15,158],[0]),([0,1,16,2,3,4,5,98],[68,5,207,41,18,77,30,138,84,14,23,174,100,3],[0]),([51,21,54,2,3,4,5],[18,68,9,2,15,17],[0]),([0,1,2,37,3,4,5,31],[27,32,144,30,143,124],[]),([125,0,1,2,3,4,5],[70,9,41,54,87,69,29,10,137,174,208,209,100,210],[]),([26,0,1,2,114,3,4,5],[9,2,77,30,84,46,17,137,55,3,211],[0]),([26,16,2,3,4,5,8],[8,6,15,9,5],[0]),([126,0,1,2,3,4,5],[18,5,41,30,53,20,70,29,46,3,68,97],[]),([127,0,1,2,3,4,5],[18,5,41,53,30,20,70,29,3,15],[0]),([26,0,1,88,3,4,5],[9,2,53,84,31,17,137,83],[0]),([51,50,26,0,1,4,5],[2,5,68,84,31,17],[0]),([39,48,0,1,2,3,4,5],[70,9,6,10,32,2,84,31,41,17,14,175],[0]),([30,0,1,16,2,19,3,4,5],[46,90,96,3,92,9,21,83,2,14,189],[0]),([26,16,2,19,3,4,5],[3,90,20,5,9,15,17,6],[0]),([0,1,16,2,93,3,4,5],[137,9,144,1,30,77,31,69,32,15,14,6,174,166],[0]),([39,0,1,40,2,3,4,5],[32,33,3,9,6,10,84,31,41,137,17,212,200],[]),([0,1,128,2,3,4,5],[5,68,41,9,30,53,18,29,46,97],[]),([47,0,1,2,3,4,5,66],[55,21,20,6,5,8,15,205,16],[0]),([27,26,0,1,2,3,4],[8,131,17,124,153,77,69,31,15],[0]),([47,26,16,2,3,4,5],[20,5,41,10,8,15,6,14],[0]),([129,0,1,2,3,4,5,44],[55,21,16,83,68,131,3,84,27,14,17,213,33],[]),([51,0,1,63,2,4,5],[9,41,30,84,137],[]),([39,0,1,61,2,3,4,5],[131,2,9,6,10,30,31,84,41,137,14,173,132,183],[]),([26,0,1,2,3,4,5,111],[9,2,131,30,84,46,17,114,137,55,94,3],[0]),([68,0,1,40,2,3,5],[69,9,41,84,32],[]),([0,1,2,3,4,13,29],[3,38,55,24,131,32,33,56,46,59,87,84],[0,2,3,4]),([26,0,1,84,2,3,4,5,7],[3,46,23,2,69,24,21,6,33,5,211],[0]),([39,10,0,1,2,3,4,5],[69,10,31,6,131,214,15,46,107,30,106,9,14,132,17,215,179,108],[0]),([12,10,1,16,2,3,4,5],[55,21,15,33,17,215,6,10,137,68,106,216,108],[]),([21,0,1,2,114,3,4,5],[9,2,23,70,77,30,84,46,61,3,150],[0]),([130,0,1,2,3,4,5],[18,16,41,8,70,54,87,69,30,124,15,17],[]),([39,0,1,2,19,3,4,5],[131,33,3,46,91,10,6,132,30,90,180,14,9,189,212],[0]),([41,26,0,1,2,3,4,5],[20,69,138,15,18,9,5,211,17,152,74],[0]),([26,0,1,2,131,3,4,5],[5,68,217,69,31,32,15,6],[0]),([11,10,0,1,16,2,4,5],[6,15,30,131,17,186,215,74,104,218,32],[0]),([0,1,16,88,3,4,5],[137,9,144,1,84,53,31,131,108],[0]),([0,1,16,2,131,3,4,5],[68,5,41,219,55,14,18,220,15,9,6,174,166],[0]),([83,26,0,1,2,3,4,5,7],[23,3,9,221,5,69,24,211],[0]),([0,1,2,3,132,4,5],[3,33,15,54,70,17],[0]),([30,26,0,1,2,19,3,4,5],[3,96,46,206,9,5,17],[0]),([30,10,26,0,1,2,3,4,5],[9,15,211,155,46,32,138,17],[0]),([10,26,0,1,2,3,4,5,46],[32,138,211,5,15,107,74,17],[0]),([116,26,0,1,2,3,4,5],[20,69,211,5,41,55,8,217,2,6,68,74,84,222,223,94],[0]),([26,0,1,2,3,4,5,29],[3,33,59,46,31,30,17,131,24,9,5],[0]),([26,0,1,2,19,3,4,5,46],[91,46,5,131,3,74,6,94],[0]),([21,54,2,3,4,5,46],[6,21,5,17,3],[0]),([39,30,0,1,2,3,4],[6,54,21,9,108],[0]),([48,47,26,0,1,3,5],[2,5,3,31,84,32,15],[0]),([26,0,1,2,93,3,4,5],[9,2,77,30,69,31,32,137,55,15,6,217],[0]),([30,64,0,1,2,3,4,5],[70,30,23,8,55,83,2,84,3,5,46,32,17],[]),([30,10,0,1,16,2,3,4,5],[9,15,166,46,106,155,32,138,215,108],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_8_0 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_7 8 nd_42_8_0 = true := by decide +kernel
def nd_42_8_1 : List NodeSpec := [([133,0,1,2,3,4,5],[18,3,41,2,53,30,54,29,137,15,224,94],[0]),([96,26,0,1,2,3,4,5],[20,5,32,46,55,41,217,8,6,2,68,74,84,225,94],[0]),([87,26,0,1,3,4,5],[54,5,68,53,84,31,17],[0]),([96,0,1,16,2,3,4,5],[55,41,20,18,46,10,32,6,5,174,8,9,68,226,84,74,14,100],[0]),([26,0,1,2,3,4,5,97],[3,33,23,70,31,15,227,114,9],[0]),([0,1,2,134,3,4,5],[5,3,18,33,70,9,53,30,29,15],[0]),([26,0,1,2,3,4,5,98],[5,68,131,30,84,138,17,77,23,94,3],[0]),([135,0,1,2,3,4,5],[18,5,41,20,70,69,87,77,68,15,74],[]),([21,54,2,19,3,4,5],[3,33,5,9,15,17,6],[0]),([0,1,2,3,4,49,5,66],[68,5,3,8,15,84,2,6,225,16,46],[0]),([136,0,1,2,3,4,5],[18,68,41,2,20,69,87,17,137],[]),([21,0,1,2,131,3,4,5],[5,68,14,54,46,40,156,69,32,15,6],[0]),([0,1,2,3,4,5,66,137],[68,5,16,17,3,98,2],[0]),([10,21,54,2,3,4,5],[18,3,40,15,27,9,5,6,214,17],[0]),([26,0,1,2,3,4,110,5],[5,68,31,30,69,211,98,15],[0]),([138,0,1,2,3,4,5],[70,3,41,9,30,53,29,10,137,15,228,158],[0]),([26,0,1,2,3,4,104,5],[9,2,31,30,69,46,98,137,55,15],[0]),([26,0,1,2,3,4,5,92],[9,2,77,84,46,229,98,137,55,94,8],[0]),([6,26,16,2,3,4,5],[20,3,41,6,5,9,8,15],[0]),([0,1,2,19,3,4,5,66],[3,33,5,2,17,91,46],[0]),([11,26,16,2,3,4,5],[20,16,17,6,9,5,3,15,19],[0]),([12,1,16,2,19,3,4,5],[3,33,17,21,55,189,6,10,90,230,68,137,15],[0]),([11,10,26,0,1,2,4,5],[6,3,30,131,17,31,15,218,74],[0]),([9,26,16,2,3,4,5],[20,3,41,10,5,9,8,17,231],[0]),([26,0,1,2,91,3,4,5],[5,68,217,84,138,17,211,3],[0]),([22,15,1,2,3,5,31],[32,21,33,27,144,84,31],[]),([139,0,1,2,3,4,5],[55,16,41,143,54,70,53,30,18,27,17,33,144],[]),([10,26,16,2,3,4,5],[20,3,15,10,41,9,5,6,106,17],[0]),([51,26,16,2,3,4,5],[20,5,2,41,9,15,17],[0]),([11,10,21,0,1,2,4,5],[6,3,30,131,17,124,31,15,104,218,74,61],[0]),([0,1,140,2,3,4,5],[137,9,10,15,17,158],[0]),([10,0,1,2,3,4,5,66],[55,21,20,6,2,5,3,8,15,17,69,107,46],[0]),([26,16,2,3,4,5,7],[151,6,19,15,9,5,17],[0]),([26,16,2,3,53,4,5],[5,14,20,17,3,15],[0]),([50,21,54,2,3,4,5],[18,5,68,9,3,6,8,15,17,25],[0]),([26,0,1,2,3,4,29],[3,33,59,46,31,30,24,15],[0]),([26,16,2,3,4,49,5],[5,14,3,15,129,19,9],[0]),([87,0,1,16,3,4,5],[5,68,77,14,232,233,15,17,166],[0]),([0,141,1,2,3,4,5],[18,21,17,54,70,55,234,33,235],[]),([48,26,16,2,3,4,5],[20,5,9,2,8,6,3,15,127,19],[0]),([26,0,1,2,3,4,108,5],[9,2,77,84,46,236,137,55,217,8],[0]),([33,0,1,2,37,3,4,5],[55,10,68,83,6,124,30,69,31,32,14],[]),([26,16,40,2,3,4,5],[3,9,41,8,15,6],[0]),([0,1,2,3,4,5,66,142],[16,143,2,5,17,3],[0]),([143,0,1,2,3,4,5],[20,68,41,18,70,69,87,77,5,9,15,74],[]),([21,0,1,2,70,3,4,5],[15,101,185,74,40,156,61,17,18,5,9],[0]),([21,1,2,19,3,4,5,13],[3,90,237,131,6,143,33,68,137,15,61],[0]),([0,1,2,3,4,66,8],[16,21,6,55,8,15,17,5,30],[0]),([50,26,16,2,3,4,5],[20,5,41,10,9,3,6,14,8,15,17,19],[0]),([33,0,1,2,42,3,4,5],[21,137,1,6,238,69,31,32],[]),([0,1,2,3,4,5,144],[16,8,124,84,17,70,54],[]),([30,0,1,63,2,3,4,5],[21,6,70,30,23,14,8,9,84,15,32,46],[]),([83,0,1,16,2,3,4,5,7],[21,239,6,151,23,9,221,24,69,5,166],[0]),([0,1,40,2,3,4,5,66],[3,33,21,55,6,20,2,8,15,227,16],[0]),([145,2,3,4,5],[6],[0]),([0,1,16,2,3,4,108,5],[137,9,144,1,84,77,46,32,240,174,8],[0]),([26,16,2,3,4,5,46],[5,6,17,3],[0]),([146,0,1,2,3,4,5,66],[55,21,6,16,2,8,17,98,3,5,46],[0]),([0,1,65,2,3,4,5,46],[5,131,68,6,46,32,30,114,124,3,84],[]),([47,21,54,2,3,4,5],[18,5,3,8,15,6],[0]),([26,0,1,2,70,3,4,5],[15,17,185,74,217,5,9],[0]),([0,1,2,3,4,5,147],[6,21,30,84,14,70],[0]),([48,47,21,0,1,3,5],[9,3,31,84,1,15],[0]),([26,16,2,3,4,23,5],[8,187,20,17,3,15,9,5,6],[0]),([41,0,1,16,2,3,4,5],[55,41,20,18,69,10,138,9,5,166,174,15,17,215,74,109,152],[0]),([148,0,1,2,3,4,5,66],[55,21,6,3,5,2,8,15,16,69,33,46],[0]),([0,1,2,3,4,66,46],[5,21,68,16,17,3,20],[0]),([0,1,149,2,3,4,5],[9,70,41,137,10,241,166,242,243,100],[]),([150,0,1,2,3,4,5],[18,5,41,20,53,87,69,29,17,68],[0]),([0,1,16,2,19,3,4,5,46],[21,68,6,5,244,46,14,74,91,3,100],[0]),([26,16,61,2,3,4,5],[2,9,20,5,3,6,8,15,17,19],[0]),([50,0,1,2,3,4,5,66],[55,21,20,6,5,2,98,3,17,77,68,15,84],[0]),([0,1,61,2,3,4,5,66],[83,2,5,98,3,17,15,84],[0]),([47,0,1,2,3,4,5,56],[55,21,3,18,143,68,124,15,178,40,6,9,1],[]),([116,21,0,1,2,3,4,5],[18,69,40,150,55,6,3,8,156,9,5,68,14,54,114,74,84,245,75],[0]),([0,1,2,151,3,4,5],[5,137,9,18,68,8,2,15,69,29,17,94],[0]),([16,2,3,4,5,66],[6,17,20],[0]),([21,0,1,2,3,4,5,111],[9,2,23,70,131,30,84,46,1,83,61,75,3],[0]),([48,0,1,2,3,4,5,66],[55,21,20,6,3,2,8,5,229,16,83,15,84],[0]),([0,1,152,2,3,4,5],[5,9,55,68,41,77,137,69,87,74],[]),([6,0,1,2,3,4,66],[55,3,20,5,8,6,33,15,16,69],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_8_1 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_7 8 nd_42_8_1 = true := by decide +kernel
def nodes_42_8 : List NodeSpec := nd_42_8_0 ++ nd_42_8_1
set_option maxRecDepth 500000 in
lemma chk_42_8 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_7 8 nodes_42_8 = true := by
  unfold nodes_42_8 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_42_8_0, chk_42_8_1⟩
def bk_42_8 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_8
set_option maxRecDepth 500000 in
lemma bk_42_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 8 xs.toFinset) bk_42_8 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_7_ok chk_42_8
def nodes_42_9 : List NodeSpec := [([27,0,1,2,3,4],[131,31],[0,1,2,5,3,4]),([28,1,2,3,4,5],[41,53,31,131],[3,4]),([0,1,2,3,4,5,29],[30,31,131,55,24,41,20,18,70,54],[0,1,2,5,3,4]),([0,1,2,3,4,29],[30,31],[0,1,2,5,3,4]),([12,10,0,1,2,3,4,5],[55,69,32,31,21,15,179,214,107,97,131],[0,2,3,4]),([12,0,1,2,19,3,4,5],[131,3,180,33,91,46,55,21,6,10,23,83],[0,2,3,4]),([30,0,1,16,2,3,4,5],[55,21,20,6,70,23,9,246,186,131,46,32,108],[0]),([20,0,1,2,3,4,5,31],[131,20,16,18,27,23,9,32,235,55,247,41,144,84],[0]),([32,0,1,2,3,4,5],[41,20,69,18,54,70,53,30,55,29,84,32],[3,4]),([33,15,0,1,2,3,4,5],[41,20,21,6,33,1,31,84,131,214],[0]),([33,17,0,1,2,3,4,5],[41,20,21,6,137,8,1,53,30,84,31,131,32,33,214],[]),([0,1,2,3,4,5,34],[41,31,32,21,18,20,54,70],[3,4]),([35,0,1,2,3,4,5],[29,41,20,32,18,70,54,30,53,84,15],[3,4]),([33,22,0,1,2,3,4,5],[20,55,32,6,33,41,21,16,83,68,10,31,84,23,2,131,14],[0]),([15,0,1,2,3,4,5,31],[32,20,21,18,23,9,131,247,143,33,234,46,248],[0,3]),([22,0,1,2,3,4,5,31],[32,27,18,20,23,9,131,144,84,31],[0]),([0,1,2,36,3,4,5],[41,20,30,18,84,131,54,70],[3,4]),([22,15,1,2,3,5],[55,41,31,32],[3,4,0,2]),([0,1,2,37,3,4,5],[55,31,20,30,18,32,54,70],[3,4,0,2]),([11,10,0,1,2,4,5],[30,29,87,53,31,131],[0,1,2,5,3,4]),([33,0,1,2,3,4,24,5],[55,21,137,33,1,31,84,20,6,32,131],[0]),([33,14,0,1,2,3,4,5],[20,55,33,6,41,68,46,31,84,27,32,23,2,131,214,249,21,14],[]),([10,9,0,1,2,5],[31,131],[0,1,2,5,3,4]),([0,1,2,3,4,5,38],[55,31,32,249,20,16,18,70,54],[3,4,0,2]),([17,0,1,2,3,4,5,31],[131,20,21,18,23,9,32,235,143,247,55,17,250,148,137,251],[0,3]),([39,0,1,2,3,4,5],[29,41,18,70,6,54,30,53,87,69,14,108],[0]),([18,17,1,2,4,5],[53,41,31,131],[3,4]),([26,0,1,40,2,3,4,5],[3,33,20,70,54,31,84,32,41,55,18,2,8,15,6],[0]),([10,0,1,2,3,4,5,13],[55,32,41,6,40,23,137,131,31,16,15,106,214,179,97,107],[0,2,3,4]),([41,0,1,2,3,4,5],[55,69,41,18,20,54,70,30,31,131],[0,1,2,5,3,4]),([9,21,0,1,2,3,4,5],[18,53,3,84,20,68,9,124,61,231,252,46,33,253],[0]),([0,1,2,42,3,4,5],[41,31,20,30,18,32,54,70],[3,4,0,2]),([0,1,2,19,3,4,5,13],[3,90,131,40,6,142,33,180,23,137,46,91,84],[0,2,3,4]),([0,1,2,3,4,5,43],[41,30,131,15,84,20,21,18,54,70,87],[3,4]),([11,21,0,1,2,3,4,5],[18,30,6,131,55,16,41,21,9,61,68,3,23,74,32,31,15,75],[0]),([10,21,0,1,2,3,4,5],[18,69,3,31,40,15,9,68,6,106,107,97,131,214,179,61],[0]),([21,0,1,2,3,4,23,5],[8,124,187,254,77,69,87,18,61,55,41,188,20,3,15,9,68,6],[0]),([0,1,2,3,4,5,44],[55,30,131,255,84,20,16,18,70,54],[3,4,0,2]),([0,1,2,3,4,5,45],[55,84,61,32,18,20,54,70,53],[3,4,0,2]),([30,21,0,1,2,3,4,5],[18,70,6,23,55,68,41,21,9,124,3,2,131,1,61],[0]),([21,0,1,2,19,3,4,5],[3,90,91,46,18,87,53,30,131,33,41,55,180,68,9,15,61,6],[0]),([21,0,1,2,3,4,5,46],[6,5,54,70,131,32,222,68,61,3],[0]),([11,26,0,1,2,3,4,5],[20,30,16,131,17,41,2,5,3,6,23,74,32,31,21,15,94,256],[0]),([47,21,0,1,2,3,4,5],[18,54,5,3,41,55,20,68,124,15,6,14,32],[0]),([26,0,1,2,3,4,5,7],[6,21,151,23,221,31,84,256,24,3,94,15,2,5,17],[0]),([21,0,1,2,3,4,5,7],[6,151,23,221,31,84,24,21,3,75,15,9,68,61],[0]),([48,21,0,1,2,3,4,5],[18,70,3,9,41,55,124,68,6,2,54,31,84,1,83,15,160,75],[0]),([21,0,1,2,3,4,49,5],[5,68,14,54,70,31,84,18,32,3,15,163,75,9],[0]),([50,21,0,1,2,3,4,5],[18,54,5,68,20,9,3,6,14,70,53,30,84,31,131,124,15,61,75],[0]),([51,21,0,1,2,3,4,5],[18,53,68,9,41,20,15,61],[0]),([52,0,1,2,3,4,5,7],[69,21,6,151,23,221,31,84,55,40,24],[3,4]),([21,0,1,2,3,53,4,5],[5,68,14,53,30,18,84,31,61,55,41,3,15],[0]),([21,1,2,3,4,5,13],[41,55,23,6,1,61],[0]),([21,54,2,3,4,5],[18,41,6],[0]),([55,1,2,3,4,5],[55,53,31,131],[3,4]),([0,1,2,3,4,5,56],[18,55,1,61,6,54,70,53,30,69,87],[0]),([0,1,2,3,4,57,5],[18,55,84,70,54,32],[]),([0,1,2,3,4,58,5],[41,69,30,31,20,18,32,70,54],[3,4]),([0,1,16,2,3,4,5,7],[21,6,221,23,84,31,24,100,158,9,14,108],[0]),([0,1,16,2,3,4,5,8],[21,6,77,23,30,31,32,246,15,158,9,14],[0]),([0,1,16,2,3,53,4,5],[68,5,137,55,14,41,257,20,18,258,53,246,186,158,6,108],[0]),([0,1,16,2,19,3,4,5],[3,33,90,55,186,180,20,46,91,30,53,131,14,9,174,15,189,158,6],[0,1]),([11,0,1,16,2,3,4,5],[55,21,20,6,30,131,9,174,14,17,186,108,74,23,31,32,158,100],[0]),([33,20,0,1,2,3,4,5],[20,55,16,6,10,68,83,53,30,84,31,131,23,2,32,33,214,14],[]),([50,0,1,16,2,3,4,5],[55,5,41,68,20,18,54,10,77,9,14,186,6,259,260,246,158,207,174,100],[0]),([10,0,1,16,2,3,4,5],[55,15,41,20,214,18,69,10,106,31,9,166,14,186,246,6,158,179,97,107,131,215],[0,1]),([9,0,1,16,2,3,4,5],[55,3,41,20,18,33,53,10,84,231,9,14,246,186,108,253,46,252],[0]),([0,1,16,2,3,4,23,5],[124,8,187,55,246,108,188,20,77,254,87,69,15,166,9,14,186,158,6],[0]),([0,1,2,59,3,4,5],[55,20,30,18,84,131,54,70],[3,4]),([47,0,1,16,2,3,4,5],[55,5,41,14,18,20,54,246,158,6,261,262],[0]),([60,0,1,2,3,4,5,7],[69,24,6,151,23,221,31,84,41,3,21],[3,4]),([0,1,16,2,3,4,49,5],[68,5,137,55,263,14,264,54,186,166,246,226,158,100],[0]),([51,0,1,16,2,3,4,5],[55,9,41,53,14,158,108,137],[0]),([26,0,1,2,3,4,5,46],[6,21,70,5,54,131,32,222,256,20,68,17,3],[0]),([0,1,16,61,2,3,4,5],[137,9,41,55,144,18,20,1,70,30,53,31,84,131,14,186,6,246,158,183,174,100],[0]),([14,0,1,2,3,4,5,31],[32,20,33,18,27,23,9,131,247,249,144],[0]),([0,1,2,3,4,62,5],[20,55,84,70,54,32],[]),([48,0,1,16,2,3,4,5],[55,9,41,18,20,70,246,14,6,137,144,1,84,31,32,186,166,175,158,100],[0]),([21,0,1,61,2,3,4,5],[9,2,18,70,54,53,30,84,31,1,41,55,83,68,3,6,124,15,61,75],[0]),([26,0,1,61,2,3,4,5],[9,2,20,70,53,30,84,31,131,137,41,55,68,3,6,8,15,17,94],[0]),([0,1,63,2,3,4,5],[41,20,18,70,30,54,69,87,29,84,6,14],[0]),([26,0,1,2,3,53,4,5],[5,68,54,70,53,30,20,84,31,17,3,15],[0]),([12,1,16,2,3,4,5],[20,55,41,6,23,144,14,108],[0]),([64,0,1,2,3,4,5],[18,55,41,20,70,30,54,69,87,29,84,17],[0]),([26,0,1,2,3,4,5,8],[6,21,77,16,23,8,32,31,17,29,20,55,41,18,15,2,5,256],[0]),([21,0,1,2,3,4,5,8],[6,8,23,77,30,32,31,124,20,15,9,68],[0]),([6,0,1,16,2,3,4,5],[55,21,20,6,87,32,9,3,14,186,246,158,46,23],[0]),([0,1,65,2,3,4,5],[18,20,55,70,30,54,69,87,29,84,6,1],[0]),([0,1,16,40,2,3,4,5],[3,33,55,41,9,137,144,1,70,84,31,32,246,158,6],[0]),([6,26,0,1,2,3,4,5],[20,87,3,32,18,5,2,8,15,256,21,23,46,6,33],[0]),([47,26,0,1,2,3,4,5],[20,54,5,41,55,8,15,6,70,32],[0]),([30,26,0,1,2,3,4,5],[20,70,5,23,2,41,55,8,3,6,131,32,46,256,21,68,17],[0]),([26,0,1,2,3,4,49,5],[5,68,31,84,20,32,3,15,225,94,2],[0]),([10,26,0,1,2,3,4,5],[20,69,3,31,15,18,2,5,6,214,107,97,131,17],[0]),([26,16,2,3,4,5],[20,41,6],[0]),([21,0,1,40,2,3,4,5],[3,9,18,70,31,84,1,20,124,15,6],[0]),([26,0,1,2,3,4,23,5],[8,124,254,77,69,87,20,17,55,41,18,3,15,2,5,256],[0]),([26,0,1,2,19,3,4,5],[3,33,91,46,20,87,53,30,131,5,2,15,17,256],[0]),([9,26,0,1,2,3,4,5],[20,53,3,84,18,5,2,8,17,252,46,87],[0]),([0,1,2,3,4,5,66],[20,55,17,256,70,54,30,53,87,69],[0]),([0,1,2,3,4,24,5,31],[21,32,40,265,1,247,148,9,23,266],[3,0]),([0,1,2,3,4,67,5],[55,84,20,18,32,70,54],[3,4]),([50,26,0,1,2,3,4,5],[20,54,5,41,55,2,3,6,68,53,30,84,31,131,8,15,17,94],[0]),([68,0,1,2,3,4,5],[41,20,18,70,69,54,53,30,32,84],[0]),([6,21,0,1,2,3,4,5],[18,87,6,32,55,3,68,9,124,15,23,46],[0]),([0,1,2,3,4,69,5],[55,69,30,31,20,18,32,70,54],[3,4]),([0,1,16,2,3,4,5,46],[21,6,70,54,14,108,186],[0]),([0,1,2,70,3,4,5],[55,30,41,31,131,18,20,54,70],[0,1,2,5,3,4]),([48,26,0,1,2,3,4,5],[20,70,5,2,41,55,8,6,9,31,84,32,137,3,15,229,94],[0]),([51,26,0,1,2,3,4,5],[20,53,5,2,41,55,18,15,17,54,70],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_9 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_8 9 nodes_42_9 = true := by decide +kernel
def bk_42_9 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_9
set_option maxRecDepth 500000 in
lemma bk_42_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 9 xs.toFinset) bk_42_9 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_8_ok chk_42_9
def nodes_42_10 : List NodeSpec := [([6,0,1,2,3,4,5],[55,87,41,18,20,54,70,53,31,29],[0,1,2,5,3,4]),([0,1,2,3,4,5,7],[84,31,29,55,41,20,18,70,54,131],[0,1,2,5,3,4]),([0,1,2,3,4,5,8],[53,31,29,55,41,20,18,70,54],[0,1,2,5,3,4]),([9,0,1,2,3,4,5],[53,41,55,18,20,54,70,87,131],[0,1,2,5,3,4]),([10,0,1,2,3,4,5],[55,69,41,31,20,18,70,54,29,131],[0,1,2,5,3,4]),([11,0,1,2,3,4,5],[55,30,41,131,20,18,70,54,87,31,84,29],[0,1,2,5,3,4]),([12,0,1,2,3,4,5],[29,20,55,18,54,70,53,87,131],[0,2,3,4,1,5]),([0,1,2,3,4,5,13],[41,29,131,20,18,70,54,87],[0,2,3,4,1,5]),([14,0,1,2,3,4,5],[55,18,20,54,70,53,31,29,249],[0,3,4,2]),([15,0,1,2,3,4,5],[41,18,20,54,70,53,31,29,21],[0,3,4,2]),([0,1,16,2,3,4,5],[41,20,18,70,54,53,87,29,6],[0,1]),([17,0,1,2,3,4,5],[41,18,20,54,70,55,87,29,53,31,30,84,131],[0,3,4,2]),([18,0,1,2,3,4,5],[53,55,18,20,54,70,31,131],[0,3,4]),([0,1,2,19,3,4,5],[55,87,41,30,53,131,18,20,54,70,31,29],[0,1,2,5,3,4]),([20,0,1,2,3,4,5],[53,20,55,18,54,70,41,87,29,31,30,84,131],[0,3,4,2]),([21,0,1,2,3,4,5],[20,41,18,54,70,53,87,29,55,6],[0]),([22,0,1,2,3,4,5],[55,18,20,54,70,53,41,29,87,84,31,32],[0,3,4,2]),([0,1,2,3,4,23,5],[53,87,69,55,41,131,20,18,70,54,31,29],[0,1,2,5,3,4]),([0,1,2,3,4,24,5],[41,87,84,31,20,18,32,70,54,55,29],[3,4,0,2]),([0,1,2,3,25,4,5],[41,53,20,18,31,131,70,54],[3,4]),([26,0,1,2,3,4,5],[20,18,54,70,53,87,29,41,55,256],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_10 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_9 10 nodes_42_10 = true := by decide +kernel
def bk_42_10 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_10
set_option maxRecDepth 500000 in
lemma bk_42_10_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 10 xs.toFinset) bk_42_10 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_9_ok chk_42_10
def nodes_42_11 : List NodeSpec := [([0,1,2,3,4,5],[29],[0,1,2,5,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_11 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_10 11 nodes_42_11 = true := by decide +kernel
def bk_42_11 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_11
set_option maxRecDepth 500000 in
lemma bk_42_11_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 11 xs.toFinset) bk_42_11 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_10_ok chk_42_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_ok : forestRootCheck R_42 G_42 [(VAR 0,11,10),(VAR 1,11,9),(VAR 2,13,9),(VAR 3,11,3),(VAR 4,23,7),(VAR 5,41,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_in : bucketContainsBT bk_42_11 R_42 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_42 : Lower R_42 G_42 12 := lower_of_forestBT root_42_ok bk_42_11_ok root_42_in
def wit : List PEqualNP.CircuitLowerBounds.Gate := [
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 11]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 14]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 15]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 17]⟩
]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by intro g hg; simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4278124032 * 2 ^ 32 + 4269860864) ||| ((4278124032 * 2 ^ 32 + 4269860864) <<< 64)).testBit r.val := by decide +kernel
lemma root_eq : G_42 = ((4278124032 * 2 ^ 32 + 4269860864) ||| ((4278124032 * 2 ^ 32 + 4269860864) <<< 64)) := by decide
lemma low_root : Lower (varsOf 63) ((4278124032 * 2 ^ 32 + 4269860864) ||| ((4278124032 * 2 ^ 32 + 4269860864) <<< 64)) 12 := root_eq ▸ low_42
end PEqualNP.Outside.L_meta_12168
theorem PEqualNP.Outside.L_meta_12168 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124032 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124032 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_12168.table2_of_lower (4278124032 * 2 ^ 32 + 4269860864) (by decide) (by decide) (by decide) (by decide) 12 PEqualNP.Outside.L_meta_12168.low_root PEqualNP.Outside.L_meta_12168.wit PEqualNP.Outside.L_meta_12168.wo (by decide) PEqualNP.Outside.L_meta_12168.wit_mono PEqualNP.Outside.L_meta_12168.wit_eval s hcs
