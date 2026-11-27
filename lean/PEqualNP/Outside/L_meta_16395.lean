import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_16395
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
inductive btAll {α : Type} (P : α → Prop) : BT α → Prop where
  | empty : btAll P .empty
  | leaf {x : α} : P x → btAll P (.leaf x)
  | node {l r : BT α} : btAll P l → btAll P r → btAll P (.node l r)
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction ht generalizing i with
  | empty => exact hd
  | leaf hx => exact hx
  | node _ _ ihl ihr =>
    unfold btGet
    split
    · exact ihl _
    · exact ihr _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact .leaf hv
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btSet; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btSet; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btSet; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases ht with
    | leaf hx => exact .leaf (hf _ hx)
    | empty => exact .leaf (hf d0 hd0)
    | node _ _ => exact .leaf (hf d0 hd0)
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btUpdate; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btUpdate; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btUpdate; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
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
  exact hgo l (0, BT.empty) h .empty
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
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
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
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := .empty
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
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
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
    have htop := checkTiersBT_sound hTlt gp hW hP hAutos tiers 0 BT.empty topBks .empty hres
    have hlow := lower_of_forestBT okRoot (by simpa using htop) okForest
    have heq : tiers.length - 1 + 1 = tiers.length := by omega
    rwa [heq] at hlow
def G_0 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def R_0 : List Nat := varsOf 28
def pos_0 : List Nat := [12,12,20,20,24,24,12,20,24]
def neg_0 : List Nat := [8,4,16,4,16,8,16,8,4]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
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
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := btAll.empty
def bk_0_0 : BT (List (List Nat)) := BT.empty
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 := btAll.empty
def bk_0_1 : BT (List (List Nat)) := BT.empty
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 := btAll.empty
def bk_0_2 : BT (List (List Nat)) := BT.empty
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 := btAll.empty
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
def P_0_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 R_0 slices_0 ps_0 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0_3 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound slices_0_ok) autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,20,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in
def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(0,1),(0,4),(1,3),(0,2)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0
def G_2 : Nat := 0xccc0c000ccc0c000ccc0c000ccc0c000
def R_2 : List Nat := varsOf 30
lemma low_2_ok : liftCheck 0 2 R_2 G_2 R_0 G_0 [(VAR 1,14,12)] = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 5 := lift_of low_2_ok low_0
def G_3 : Nat := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8
def R_3 : List Nat := varsOf 39
lemma low_3_ok : liftCheck 32 0 R_3 G_3 R_1 G_1 [(VAR 5,33,1)] = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 5 := lift_of low_3_ok low_1
def G_4 : Nat := 0xeeaaeeaaaa88aa88eeaaeeaaaa88aa88
def R_4 : List Nat := varsOf 43
def pos_4 : List Nat := [3,3,9,9,11,33,33,35,41,42,42,42,3,3,3,9,9,9,33,33,33,42]
def neg_4 : List Nat := [2,1,8,1,10,32,1,34,40,40,34,10,10,34,40,10,34,40,10,34,40,1]
def fmask_4 : Nat := fullMask 22
def base_4 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ff1ff,0x20004a),(0xcccccccccccccccccccccccccccccccc,0x207e93,0xdbc91),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x238f1c,0x16db14),(0xffffffff00000000ffffffff00000000,0x3c0fe0,0x1b67a0)]
def steps_4 : List (Nat × Nat × Nat) := [(0,1,2),(2,0,1),(2,1,2),(3,0,1),(1,1,2),(1,0,1),(0,0,1),(3,1,2),(3,6,3),(0,9,2),(2,9,2),(1,6,3),(3,10,2),(1,10,2),(3,4,8)]
def W_4 : BT Decor := buildWiresBT 5 base_4 steps_4
def autosL_4 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,3)],[(1,5),(1,3)],[(1,3),(1,5)],[(1,5)]]
def autos_4 : BT (List (Nat × Nat)) := btOfList 3 autosL_4
def slicesL_4 : List (Option (Nat × Nat)) := []
def slices_4 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_4
def ps_4 : BT (Option PoolSpec) := btOfList 1 []
lemma gp_4 : goodPairs G_4 pos_4 neg_4 := goodPairs_of (by decide +kernel)
lemma base_4_ok : ∀ x ∈ base_4, faithful pos_4 neg_4 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_4_ok : btAll (fun x => faithful pos_4 neg_4 x ∧ x.1 < 2^128) W_4 := buildWiresBT_faithful base_4_ok
set_option maxRecDepth 500000 in
lemma autos_4_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_4 = G_4) autos_4 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_4_ok : btAll (fun o => ∀ p, o = some p → Slice R_4 G_4 p.1 p.2) slices_4 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_4 G_4 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def bk_4_init : BT (List (List Nat)) := BT.empty
lemma bk_4_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_4 (0 - 1) xs.toFinset) bk_4_init := btAll.empty
def bk_4_0 : BT (List (List Nat)) := BT.empty
lemma bk_4_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_4 0 xs.toFinset) bk_4_0 := btAll.empty
def bk_4_1 : BT (List (List Nat)) := BT.empty
lemma bk_4_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_4 1 xs.toFinset) bk_4_1 := btAll.empty
def nodes_4_2 : List NodeSpec := [([18,0,3],[],[])]
def P_4_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_4 R_4 slices_4 ps_4 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_4_2 : checkNodesBT W_4 G_4 fmask_4 P_4_2 autos_4 bk_4_1 2 nodes_4_2 = true := by decide +kernel
def bk_4_2 : BT (List (List Nat)) := buildBucketsBT W_4 nodes_4_2
set_option maxRecDepth 500000 in
lemma bk_4_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_4 2 xs.toFinset) bk_4_2 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound slices_4_ok) autos_4_ok bk_4_1_ok chk_4_2
def nodes_4_3 : List NodeSpec := [([6,11,0,3],[],[0]),([0,1,2,12],[],[]),([0,4,8,3],[],[0]),([0,1,13,3],[],[]),([14,0,1,3],[],[]),([0,1,2,15],[],[]),([5,7,2,3],[],[]),([16,0,1,3],[],[]),([0,1,17,3],[],[])]
def P_4_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_4 R_4 slices_4 ps_4 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_4_3 : checkNodesBT W_4 G_4 fmask_4 P_4_3 autos_4 bk_4_2 3 nodes_4_3 = true := by decide +kernel
def bk_4_3 : BT (List (List Nat)) := buildBucketsBT W_4 nodes_4_3
set_option maxRecDepth 500000 in
lemma bk_4_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_4 3 xs.toFinset) bk_4_3 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound slices_4_ok) autos_4_ok bk_4_2_ok chk_4_3
def nodes_4_4 : List NodeSpec := [([0,4,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([6,0,1,2,3],[],[0]),([7,0,1,2,3],[],[0]),([0,1,2,8,3],[],[0]),([0,1,9,2,3],[],[0,1]),([10,0,1,2,3],[],[0,1])]
def P_4_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_4 R_4 slices_4 ps_4 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_4_4 : checkNodesBT W_4 G_4 fmask_4 P_4_4 autos_4 bk_4_3 4 nodes_4_4 = true := by decide +kernel
def bk_4_4 : BT (List (List Nat)) := buildBucketsBT W_4 nodes_4_4
set_option maxRecDepth 500000 in
lemma bk_4_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_4 4 xs.toFinset) bk_4_4 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound slices_4_ok) autos_4_ok bk_4_3_ok chk_4_4
def nodes_4_5 : List NodeSpec := [([0,1,2,3],[],[0,2,3,1,4,5])]
def P_4_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_4 R_4 slices_4 ps_4 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_4_5 : checkNodesBT W_4 G_4 fmask_4 P_4_5 autos_4 bk_4_4 5 nodes_4_5 = true := by decide +kernel
def bk_4_5 : BT (List (List Nat)) := buildBucketsBT W_4 nodes_4_5
set_option maxRecDepth 500000 in
lemma bk_4_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_4 5 xs.toFinset) bk_4_5 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound slices_4_ok) autos_4_ok bk_4_4_ok chk_4_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_4_ok : forestRootCheck R_4 G_4 [(VAR 0,3,2),(VAR 1,3,1),(VAR 3,9,1),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_4_in : bucketContainsBT bk_4_5 R_4 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_4 : Lower R_4 G_4 6 := lower_of_forestBT root_4_ok bk_4_5_ok root_4_in
def G_5 : Nat := 0xfff0f000f0f0f000fff0f000f0f0f000
def R_5 : List Nat := varsOf 60
lemma low_5_ok : liftCheck 0 32 R_5 G_5 R_0 G_0 [(VAR 5,56,24)] = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 5 := lift_of low_5_ok low_0
def G_6 : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
def R_6 : List Nat := varsOf 29
lemma low_6_ok : liftCheck 1 0 R_6 G_6 R_0 G_0 [(VAR 0,1,0)] = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 5 := lift_of low_6_ok low_0
def G_7 : Nat := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8
def R_7 : List Nat := varsOf 23
lemma low_7_ok : carryOK [(1,5),(0,1),(0,4),(1,3),(0,2)] R_7 G_7 R_5 G_5 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 5 := carry_of low_7_ok low_5
def G_8 : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def R_8 : List Nat := varsOf 15
lemma low_8_ok : carryOK [(2,4),(2,5),(2,3)] R_8 G_8 R_4 G_4 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 6 := carry_of low_8_ok low_4
def G_9 : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8
def R_9 : List Nat := varsOf 15
lemma low_9_ok : carryOK [(3,4),(3,5)] R_9 G_9 R_3 G_3 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 5 := carry_of low_9_ok low_3
def G_10 : Nat := 0xccc0c000c0c0c000ccc0c000c0c0c000
def R_10 : List Nat := varsOf 62
lemma low_10_ok : liftCheck 0 2 R_10 G_10 R_5 G_5 [(VAR 1,14,12)] = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 6 := lift_of low_10_ok low_5
def G_11 : Nat := 0xeaaaeaaaeaa8eaa8eaaaeaaaeaa8eaa8
def R_11 : List Nat := varsOf 47
lemma low_11_ok : liftCheck 32 0 R_11 G_11 R_8 G_8 [(VAR 5,33,1)] = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 7 := lift_of low_11_ok low_8
def G_12 : Nat := 0xeae8eaa8eae8eaa8eae8eaa8eae8eaa8
def R_12 : List Nat := varsOf 31
lemma low_12_ok : liftCheck 16 0 R_12 G_12 R_8 G_8 [(VAR 4,22,6)] = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 7 := lift_of low_12_ok low_8
def G_13 : Nat := 0xeaeaaaaae8e8a8a8eaeaaaaae8e8a8a8
def R_13 : List Nat := varsOf 55
lemma low_13_ok : liftCheck 0 16 R_13 G_13 R_3 G_3 [(VAR 4,22,6)] = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 6 := lift_of low_13_ok low_3
def G_14 : Nat := 0xeeaaaaaaaa88aa88eeaaaaaaaa88aa88
def R_14 : List Nat := varsOf 59
lemma low_14_ok : liftCheck 0 16 R_14 G_14 R_4 G_4 [(VAR 4,58,42)] = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 7 := lift_of low_14_ok low_4
def G_15 : Nat := 0xeeeaeaaaeeeaeaaaeeeaeaaaeeeaeaaa
def R_15 : List Nat := varsOf 31
lemma low_15_ok : liftCheck 1 0 R_15 G_15 R_2 G_2 [(VAR 0,1,0)] = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 6 := lift_of low_15_ok low_2
def G_16 : Nat := 0xeeeaeeeaeae8eae8eeeaeeeaeae8eae8
def R_16 : List Nat := varsOf 47
def pos_16 : List Nat := [3,3,5,5,6,6,9,9,11,13,14,14,33,33,35,37,38,38,41,42,42,42,45,46,3,3,3,5,5,5,6,6,6,6,9,9,9,33,33,33,42,42]
def neg_16 : List Nat := [2,1,4,1,4,2,8,1,10,12,12,10,32,1,34,36,36,34,40,40,34,10,44,44,10,34,44,10,34,44,1,10,34,44,10,34,44,10,34,44,1,44]
def fmask_16 : Nat := fullMask 42
def base_16 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfc3f44f3cf,0x1004000208a),(0xcccccccccccccccccccccccccccccccc,0x303c7bb4d33,0x6d9b324921),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3f8c38e3c,0x29224c18614),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x31c00fc0fc0,0x2b6adec0f40),(0xffffffff00000000ffffffff00000000,0x3e000fff000,0x2db36dfd000)]
def steps_16 : List (Nat × Nat × Nat) := [(1,0,3),(2,0,1),(1,1,3),(2,0,3),(3,0,1),(1,0,1),(2,1,3),(0,0,1),(1,11,4),(3,11,0),(1,12,3),(0,0,7),(1,8,1),(0,1,5),(2,10,3),(1,6,3),(2,6,3),(1,12,2),(1,11,0),(1,10,3),(2,10,2),(3,1,5),(2,5,4),(3,0,7),(2,12,3),(2,9,3),(3,12,3),(0,10,3),(3,8,1),(1,9,3),(1,16,4),(2,17,2),(1,6,9),(2,10,4),(2,24,4),(1,30,4),(1,29,2),(2,25,3),(3,12,4),(1,29,4),(0,25,3),(1,16,2),(1,12,4),(2,17,4),(2,20,4),(3,2,24),(1,22,3),(3,22,3),(2,25,4),(1,22,4)]
def W_16 : BT Decor := buildWiresBT 6 base_16 steps_16
def autosL_16 : List (List (Nat × Nat)) := [[],[(3,5)]]
def autos_16 : BT (List (Nat × Nat)) := btOfList 1 autosL_16
def slicesL_16 : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,5),some (subcubeFast 40 0,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,5)]
def slices_16 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_16
def ps_16 : BT (Option PoolSpec) := btOfList 5 [some (0,[]),some (1,[]),some (2,[(2,1,3),(1,11,4)]),some (3,[]),some (2,[(0,0,1),(1,12,3)]),some (2,[]),some (2,[(1,0,1),(2,10,3)]),some (2,[(2,0,1),(3,0,1)]),some (2,[(0,0,1),(3,12,3)]),some (2,[(1,0,1),(0,10,3)]),some (2,[(1,0,3),(2,5,4)]),some (2,[(1,0,3)]),some (2,[(2,0,1)]),some (2,[(1,1,3)]),some (2,[(2,0,3)]),some (2,[(3,0,1)]),some (2,[(1,0,1)]),some (2,[(2,1,3)]),some (2,[(0,0,1)])]
lemma gp_16 : goodPairs G_16 pos_16 neg_16 := goodPairs_of (by decide +kernel)
lemma base_16_ok : ∀ x ∈ base_16, faithful pos_16 neg_16 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_16_ok : btAll (fun x => faithful pos_16 neg_16 x ∧ x.1 < 2^128) W_16 := buildWiresBT_faithful base_16_ok
set_option maxRecDepth 500000 in
lemma autos_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_16 = G_16) autos_16 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_16_0_ok : sliceDirectCheck 32 0 0 R_16 G_16 R_9 G_9 = true := by decide +kernel
lemma sl_16_0 : Slice R_16 G_16 (subcubeFast 32 0) 5 := slice_fast_direct sl_16_0_ok low_9
lemma sl_16_1_ok : sliceDirectCheck 40 0 0 R_16 G_16 R_1 G_1 = true := by decide +kernel
lemma sl_16_1 : Slice R_16 G_16 (subcubeFast 40 0) 4 := slice_fast_direct sl_16_1_ok low_1
lemma sl_16_2_ok : sliceDirectCheck 4 0 0 R_16 G_16 R_4 G_4 = true := by decide +kernel
lemma sl_16_2 : Slice R_16 G_16 (subcubeFast 4 0) 6 := slice_fast_direct sl_16_2_ok low_4
lemma sl_16_3_ok : sliceDirectCheck 8 0 0 R_16 G_16 R_3 G_3 = true := by decide +kernel
lemma sl_16_3 : Slice R_16 G_16 (subcubeFast 8 0) 5 := slice_fast_direct sl_16_3_ok low_3
set_option maxRecDepth 500000 in
lemma slices_16_ok : btAll (fun o => ∀ p, o = some p → Slice R_16 G_16 p.1 p.2) slices_16 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_16 G_16 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (fun _ h => (List.not_mem_nil h).elim)))))
def bk_16_init : BT (List (List Nat)) := BT.empty
lemma bk_16_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 (0 - 1) xs.toFinset) bk_16_init := btAll.empty
def bk_16_0 : BT (List (List Nat)) := BT.empty
lemma bk_16_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 0 xs.toFinset) bk_16_0 := btAll.empty
def bk_16_1 : BT (List (List Nat)) := BT.empty
lemma bk_16_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 1 xs.toFinset) bk_16_1 := btAll.empty
def bk_16_2 : BT (List (List Nat)) := BT.empty
lemma bk_16_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 2 xs.toFinset) bk_16_2 := btAll.empty
def nodes_16_3 : List NodeSpec := [([53,42,0,1],[],[]),([0,1,51,54],[],[])]
def P_16_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_16 R_16 slices_16 ps_16 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_3 : checkNodesBT W_16 G_16 fmask_16 P_16_3 autos_16 bk_16_2 3 nodes_16_3 = true := by decide +kernel
def bk_16_3 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_3
set_option maxRecDepth 500000 in
lemma bk_16_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 3 xs.toFinset) bk_16_3 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound slices_16_ok) autos_16_ok bk_16_2_ok chk_16_3
def nodes_16_4 : List NodeSpec := [([0,1,2,3,35],[],[]),([8,23,1,2,4],[],[]),([36,0,1,3,4],[],[]),([11,0,17,2,4],[],[]),([0,18,2,7,4],[],[]),([9,0,2,3,13],[],[]),([9,37,2,3,4],[],[]),([6,37,2,3,4],[],[]),([38,19,0,1,2],[],[]),([39,0,1,2,3],[],[]),([0,1,2,3,40],[],[]),([38,0,1,32,2],[],[]),([19,0,1,2,4],[],[]),([0,1,41,3,4],[],[]),([0,10,22,3,4],[],[]),([19,25,0,1,4],[],[]),([9,14,2,3,4],[],[]),([6,1,22,3,4],[],[]),([42,25,0,1,4],[],[0]),([0,10,2,3,13],[],[]),([0,10,2,15,4],[],[]),([37,1,2,3,4],[],[]),([43,0,1,2,15],[],[]),([37,0,2,3,4],[],[]),([0,1,2,3,44],[],[]),([45,25,0,1,4],[],[]),([0,1,2,15,4],[],[]),([0,1,46,3,4],[],[]),([0,1,2,15,47],[],[]),([48,0,1,2,3],[],[]),([49,0,1,2,3],[],[]),([50,0,1,3,4],[],[]),([0,1,22,51,4],[],[0]),([52,0,1,22,4],[],[]),([31,0,1,22,4],[],[]),([25,0,1,3,4],[],[]),([0,1,22,15,4],[],[]),([6,9,2,3,4],[],[]),([9,0,22,3,4],[],[]),([9,0,2,15,4],[],[]),([16,1,2,5,4],[],[]),([1,10,22,3,4],[],[]),([0,1,22,3,4],[],[]),([25,0,1,32,4],[],[])]
def P_16_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_16 R_16 slices_16 ps_16 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_4 : checkNodesBT W_16 G_16 fmask_16 P_16_4 autos_16 bk_16_3 4 nodes_16_4 = true := by decide +kernel
def bk_16_4 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_4
set_option maxRecDepth 500000 in
lemma bk_16_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 4 xs.toFinset) bk_16_4 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound slices_16_ok) autos_16_ok bk_16_3_ok chk_16_4
def nodes_16_5 : List NodeSpec := [([11,0,1,2,3,13],[1],[]),([0,1,2,3,13],[2],[0]),([14,0,1,2,3,4],[3],[0]),([0,1,2,15,4],[4],[0]),([11,0,1,2,7,4],[1],[]),([16,0,1,2,3,4],[3,5,0],[0]),([12,0,1,2,3,4],[5,3,0],[0,1]),([8,11,0,1,2,4],[1],[0]),([0,1,17,2,3,4],[5,0],[0]),([0,18,1,2,3,4],[],[0]),([6,0,1,2,3,4],[],[0]),([0,1,2,5,7,4],[1],[0]),([11,9,0,2,3,4],[3],[0]),([19,0,1,10,2,4],[3,6],[0,1]),([8,0,1,2,5,4],[1],[]),([9,0,2,3,7,4],[3],[]),([6,9,2,3,4],[7],[0]),([0,1,2,3,20,4],[0],[0]),([21,0,1,2,3,4],[],[]),([12,0,1,22,3,4],[5],[0,1]),([19,0,1,2,4],[6],[]),([0,23,1,2,3,4],[],[0]),([0,1,2,3,24,4],[5,0],[0]),([9,12,0,2,3,4],[5],[0,1]),([12,0,1,2,15,4],[4,3],[0]),([25,0,1,10,3,4],[5],[0,1]),([26,0,1,2,3,4],[],[]),([6,12,1,2,3,4],[5],[0]),([25,0,1,3,4],[],[0,1]),([9,0,1,2,3,4],[],[0]),([0,1,22,3,4],[],[0,1]),([11,0,10,2,3,4],[3],[0]),([0,10,2,3,7,4],[3],[]),([27,0,1,2,3,5],[0],[]),([9,1,10,2,3,4],[5],[0]),([28,0,1,2,3,4],[],[]),([19,0,1,2,3,4],[],[]),([12,1,10,2,3,4],[],[0]),([29,0,1,2,3,4],[5,0],[0]),([30,0,1,2,3,4],[0],[0]),([12,0,10,2,3,4],[],[0,1]),([0,1,10,2,3,4],[5,3,0],[0,1]),([31,12,0,1,2,4],[8,1],[0,1]),([6,9,0,2,3,4],[],[0]),([0,1,32,10,2,4],[9,1],[0]),([0,33,1,2,3,4],[],[]),([0,1,2,3,34,4],[],[]),([6,0,10,2,3,4],[5],[0]),([27,0,1,2,3],[10],[]),([6,9,1,2,3,4],[],[0]),([0,1,2,3,15,4],[],[])]
def P_16_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_16 R_16 slices_16 ps_16 [0,1,2,3,4,5,6,7,8,9,10]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_5 : checkNodesBT W_16 G_16 fmask_16 P_16_5 autos_16 bk_16_4 5 nodes_16_5 = true := by decide +kernel
def bk_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_5
set_option maxRecDepth 500000 in
lemma bk_16_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 5 xs.toFinset) bk_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound slices_16_ok) autos_16_ok bk_16_4_ok chk_16_5
def nodes_16_6 : List NodeSpec := [([0,1,2,3,5,4],[1,11],[0]),([6,0,1,2,3,4],[12,3,0],[0,1]),([0,1,2,3,7,4],[1,13],[0]),([8,0,1,2,3,4],[1,14],[0]),([9,0,1,2,3,4],[15,3,0],[0,1]),([0,1,10,2,3,4],[16,3,0],[0,1]),([11,0,1,2,3,4],[1,17],[0]),([12,0,1,2,3,4],[18,3,0],[0,1])]
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_16 R_16 slices_16 ps_16 [0,1,3,11,12,13,14,15,16,17,18]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_6 : checkNodesBT W_16 G_16 fmask_16 P_16_6 autos_16 bk_16_5 6 nodes_16_6 = true := by decide +kernel
def bk_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_6
set_option maxRecDepth 500000 in
lemma bk_16_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 6 xs.toFinset) bk_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound slices_16_ok) autos_16_ok bk_16_5_ok chk_16_6
def nodes_16_7 : List NodeSpec := [([0,1,2,3,4],[5,1],[0,1])]
def P_16_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_16 R_16 slices_16 ps_16 [1,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_7 : checkNodesBT W_16 G_16 fmask_16 P_16_7 autos_16 bk_16_6 7 nodes_16_7 = true := by decide +kernel
def bk_16_7 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_7
set_option maxRecDepth 500000 in
lemma bk_16_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 7 xs.toFinset) bk_16_7 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound slices_16_ok) autos_16_ok bk_16_6_ok chk_16_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck R_16 G_16 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,9,1),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT bk_16_7 R_16 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_16 : Lower R_16 G_16 8 := lower_of_forestBT root_16_ok bk_16_7_ok root_16_in
def G_17 : Nat := 0xfffafaaafafafaaafffafaaafafafaaa
def R_17 : List Nat := varsOf 61
lemma low_17_ok : liftCheck 1 0 R_17 G_17 R_5 G_5 [(VAR 0,1,0)] = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 6 := lift_of low_17_ok low_5
def G_18 : Nat := 0xeeeaeaaaeae8eaa8eeeaeaaaeae8eaa8
def R_18 : List Nat := varsOf 63
def pos_18 : List Nat := [3,3,5,5,7,9,9,11,13,14,14,14,19,19,21,21,22,22,22,25,25,27,29,30,30,33,33,35,37,39,41,43,45,46,46,46,49,49,51,53,54,54,54,57,58,58,58,58,61,62,3,3,3,3,3,3,5,5,5,5,5,5,9,9,9,9,9,9,14,14,14,14,14,14,22,22,22,22,22,22,33,33,33,33,33,33,58,58,58]
def neg_18 : List Nat := [2,1,4,1,6,8,1,10,12,12,10,6,18,17,20,17,20,18,6,24,17,26,28,28,26,32,1,34,36,38,40,42,44,44,42,38,48,17,50,52,52,50,38,56,56,50,42,26,60,60,17,26,38,42,50,60,17,26,38,42,50,60,17,26,38,42,50,60,17,26,38,42,50,60,17,26,38,42,50,60,17,26,38,42,50,60,17,38,60]
def fmask_18 : Nat := fullMask 89
def base_18 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3f000ffffd08f1fe78f1ff,0x410410410400200410a04a),(0xcccccccccccccccccccccccccccccccc,0x1c0fff000fef74ea9a73e93,0x9e79e79e78e64ca9261c91),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff03f03078f31c7cf1c,0x1a492492493058b30c54b14),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1c003ffc003f80fc1f80fe0,0x12aaaaaaaabd807c1e807a0),(0xffff0000ffff0000ffff0000ffff0000,0x1c0fc000003fff001fff000,0x173cf3cf3cfbbf001fbf000),(0xffffffff00000000ffffffff00000000,0x1ff00000003fffffe000000,0x1bcf3cf3cf37fdffa000000)]
def steps_18 : List (Nat × Nat × Nat) := [(1,3,5),(1,2,5),(3,2,3),(0,1,4),(1,1,3),(2,1,3),(0,1,3),(2,3,5),(0,0,1),(2,1,2),(1,1,2),(2,0,5),(1,0,5),(1,0,1),(3,0,3),(1,2,3),(2,1,5),(2,0,3),(3,1,3),(0,0,3),(2,0,2),(3,2,5),(1,1,5),(1,0,2),(3,0,1),(1,0,3),(2,0,1),(3,0,4),(1,13,2),(0,21,4),(3,1,21),(0,1,21),(3,0,21),(2,0,21),(1,0,21),(0,0,21),(1,22,2),(3,3,28),(1,24,2),(3,8,1),(3,11,5),(1,11,5),(2,11,2),(1,11,0),(1,0,12),(3,15,3),(1,15,3),(2,11,0),(0,15,3),(2,15,0),(2,16,3),(0,4,7),(0,3,7),(1,8,0),(1,17,3),(1,17,2),(3,3,18),(3,33,1),(2,21,5),(2,31,5),(3,2,31),(3,29,3),(1,22,3),(0,1,31),(0,1,29),(1,20,2),(1,11,2),(1,25,2),(3,20,1),(3,25,1),(1,26,3),(2,29,3),(1,21,5),(2,19,2),(0,29,3),(1,25,5),(0,19,3),(3,3,7),(0,31,5),(2,19,3),(2,19,5),(1,14,3),(3,14,3),(3,2,18),(3,2,28),(1,32,3),(1,24,5),(1,1,21),(1,14,5),(1,25,1),(1,32,2),(1,15,0),(1,14,2),(3,2,10),(1,23,2),(1,0,9),(1,12,2),(1,45,5),(1,0,45),(2,59,5),(0,59,1),(2,1,35),(1,0,35),(1,0,37),(0,38,4),(3,56,5),(2,40,5),(3,1,40),(0,1,40),(3,41,1),(3,2,68),(2,42,3),(1,90,3),(0,21,28),(1,41,1),(3,9,21),(3,11,7),(1,11,8),(3,2,47),(1,42,3),(1,98,3),(1,15,20),(1,2,46),(3,72,5),(1,101,2),(1,11,27),(1,11,24),(2,50,2),(2,101,3),(3,98,5),(3,48,5),(0,71,4),(3,0,52),(1,101,3),(3,17,21),(3,2,60),(1,11,29),(1,89,3),(2,61,3),(1,36,5),(0,21,18),(3,21,28),(0,63,3),(3,21,18),(1,63,3),(2,63,2),(2,79,3),(3,20,21),(2,63,3),(0,1,71),(1,79,3),(2,74,2),(0,66,5),(1,48,0),(1,74,2),(3,14,19),(1,65,2),(1,63,2),(1,2,84),(3,27,31),(0,31,7),(3,2,87),(2,97,3),(2,66,5),(3,11,19),(1,27,14),(3,66,1),(3,98,3),(3,70,5),(1,96,3),(3,48,4),(1,70,3),(3,15,31),(1,15,31),(0,15,31),(0,101,3),(2,98,3),(3,25,31),(0,40,5),(1,48,5),(3,33,21),(1,62,2),(3,101,3),(3,63,3),(2,101,2),(3,22,21),(3,15,19),(0,79,5),(3,11,29),(3,32,21),(1,69,2),(3,12,21),(1,85,2),(0,97,5),(1,72,5),(1,12,29),(3,8,31),(2,49,2),(3,8,30),(1,8,14),(0,98,3),(2,55,3),(0,37,4),(1,8,32),(1,53,2),(3,0,72),(2,96,3),(0,102,4),(0,76,5),(3,14,21),(1,86,2),(1,43,2),(3,2,94),(1,41,5),(3,79,3),(0,40,4),(0,91,5),(3,0,102),(3,27,19),(3,53,5),(0,30,21),(3,12,29),(3,77,1),(3,8,19),(0,19,21),(2,70,3),(1,55,3),(1,61,3),(3,2,91),(3,38,1),(0,79,3),(1,48,35),(3,35,93),(3,37,93),(1,121,0),(3,0,139),(1,121,5),(1,48,24),(3,41,40),(3,48,47),(2,1,181),(2,132,2),(1,132,2),(3,51,7),(2,130,3),(3,54,52),(1,186,5),(3,186,1),(3,33,102),(3,63,21),(1,39,35),(0,63,21),(3,148,1),(0,101,21),(3,2,139),(3,65,40),(3,84,40),(3,101,21),(1,48,33),(3,35,40),(1,183,2),(3,48,19),(3,9,71),(0,114,4),(3,25,40),(3,9,40),(0,1,233),(3,80,7),(3,154,1),(1,154,2),(1,151,3),(1,53,27),(3,0,130),(3,27,91),(0,130,3),(1,48,46),(1,188,0),(3,151,1),(3,151,3),(3,80,40),(2,183,2),(3,181,139),(0,1,266),(3,148,150),(3,45,7)]
def W_18 : BT Decor := buildWiresBT 9 base_18 steps_18
def autosL_18 : List (List (Nat × Nat)) := [[]]
def autos_18 : BT (List (Nat × Nat)) := btOfList 1 autosL_18
def slicesL_18 : List (Option (Nat × Nat)) := [some (subcubeFast 8 16,5),some (subcubeFast 4 0,7),some (subcubeFast 16 0,7),some (subcubeFast 0 34,5),some (subcubeFast 40 0,5),some (subcubeFast 8 0,6),some (subcubeFast 1 2,5),some (subcubeFast 1 32,5),some (subcubeFast 1 34,4),some (subcubeFast 32 0,7),some (subcubeFast 0 2,6),some (subcubeFast 1 0,6),some (subcubeFast 0 16,8),some (subcubeFast 4 16,6),some (subcubeFast 48 0,6),some (subcubeFast 0 32,6),some (subcubeFast 40 16,4),some (subcubeFast 32 16,5)]
def slices_18 : BT (Option (Nat × Nat)) := btOfList 5 slicesL_18
def ps_18 : BT (Option PoolSpec) := btOfList 8 [some (0,[]),some (1,[(0,1,4),(1,0,9),(0,101,3)]),some (1,[(2,1,3),(0,1,4),(3,9,21)]),some (2,[(2,1,3),(3,1,3),(1,11,24)]),some (3,[]),some (4,[]),some (5,[]),some (2,[(0,1,3),(1,1,3),(3,12,10)]),some (1,[(0,1,3),(1,1,3),(3,12,10)]),some (6,[]),some (2,[(0,0,3),(1,0,3),(3,25,31)]),some (7,[]),some (8,[]),some (2,[(1,0,2),(1,2,5),(0,29,3)]),some (1,[(0,0,1),(1,0,1),(3,14,19)]),some (1,[(3,0,4),(3,33,1),(3,63,3)]),some (2,[(2,1,2),(3,15,3),(1,2,5)]),some (1,[(0,0,3),(1,0,3),(3,25,31)]),some (9,[]),some (1,[]),some (10,[]),some (11,[]),some (12,[]),some (13,[]),some (2,[]),some (14,[]),some (15,[]),some (12,[(1,2,3),(1,0,21),(2,40,5)]),some (1,[(3,3,7),(0,4,7)]),some (2,[(1,2,5),(3,3,7)]),some (12,[(1,2,3),(1,0,21),(3,1,40)]),some (2,[(3,2,3),(3,8,1)]),some (12,[(1,2,3),(1,0,21),(0,1,40)]),some (12,[(1,2,3),(0,0,21),(3,41,1)]),some (1,[(2,1,5),(1,22,3)]),some (9,[(3,2,28),(1,90,3)]),some (12,[(1,2,3),(0,0,21),(1,41,1)]),some (14,[(1,2,3)]),some (1,[(0,1,4),(3,9,21)]),some (12,[(2,1,3),(1,2,3),(3,1,21)]),some (1,[(2,1,3),(0,1,4)]),some (1,[(2,1,3),(1,11,5)]),some (2,[(2,1,2),(1,2,5)]),some (2,[(2,1,3),(1,11,5)]),some (16,[]),some (2,[(2,1,3),(3,1,3)]),some (17,[]),some (1,[(2,1,3),(3,11,5)]),some (12,[(1,0,9)]),some (14,[(2,1,3)]),some (1,[(2,1,3),(1,11,27)]),some (1,[(2,1,3),(3,1,3),(1,11,24)]),some (9,[(2,1,2),(1,15,3)]),some (2,[(1,0,2),(0,29,3)]),some (14,[(2,101,3)]),some (9,[(2,1,2)]),some (2,[(2,1,2),(3,15,3)]),some (2,[(2,1,2),(1,15,3)]),some (1,[(0,15,3),(1,15,3)]),some (1,[(2,1,3),(3,1,3)]),some (14,[(1,101,3)]),some (1,[(0,1,4),(1,0,9)]),some (9,[(1,17,2),(2,61,3)]),some (12,[(1,2,3),(3,1,21),(1,36,5)]),some (1,[(1,0,3),(0,1,40)]),some (1,[(3,0,4),(3,33,1)]),some (14,[(1,63,3)]),some (1,[(2,0,1),(3,0,1)]),some (14,[(2,63,3)]),some (9,[(1,0,1),(2,19,2)]),some (2,[(1,0,2),(1,2,5)]),some (9,[(1,0,2)]),some (12,[(0,0,1),(1,0,1),(3,14,19)]),some (1,[(1,0,3),(2,31,5)]),some (1,[(1,0,3),(0,31,5)]),some (1,[(0,0,1),(1,14,3)]),some (1,[(1,0,3),(0,31,7)]),some (2,[(0,0,3),(1,0,3)]),some (2,[(1,0,3),(2,31,5)]),some (1,[(0,1,4),(3,8,1)]),some (1,[(0,0,1),(1,0,1)]),some (2,[(0,0,1),(1,14,5)]),some (12,[(0,0,1),(1,14,5)]),some (14,[(1,0,3),(0,1,31)]),some (14,[(1,0,2),(0,1,29)]),some (2,[(1,0,1),(2,19,2)]),some (12,[(1,0,1),(2,19,2)]),some (1,[(0,0,3),(1,0,3)]),some (12,[(1,0,2),(1,29,3),(2,40,5)]),some (1,[(1,0,3),(0,1,31)]),some (12,[(2,1,2),(2,15,3),(1,48,5)]),some (12,[(1,0,2),(1,29,3),(3,1,40)]),some (12,[(1,0,2),(1,29,3),(0,1,40)]),some (1,[(1,0,5),(3,3,18)]),some (12,[(1,0,2),(1,2,3),(0,0,21)]),some (9,[(1,0,2),(2,29,3)]),some (1,[(1,29,3),(0,1,40)]),some (1,[(1,0,1),(2,19,3)]),some (2,[(0,0,1),(1,14,2)]),some (12,[(0,0,1),(1,14,2)]),some (1,[(3,0,4),(3,33,21)]),some (1,[(2,29,3),(3,29,3)]),some (1,[(0,1,29),(0,1,4)]),some (12,[(1,0,1),(2,19,3)]),some (2,[(1,0,1),(2,19,3)]),some (2,[(0,0,1),(1,14,3)]),some (12,[(0,0,1),(1,14,3)]),some (1,[(2,1,3),(3,11,7)]),some (14,[(1,0,3)]),some (1,[(1,0,3),(3,27,31)]),some (2,[(2,1,3),(1,11,2)]),some (1,[(0,0,1),(1,8,14)]),some (2,[(1,0,3),(3,2,31)]),some (9,[(0,0,1),(1,14,2)]),some (2,[(1,0,1),(2,19,5)]),some (12,[(1,0,1),(2,19,5)]),some (14,[(1,0,2)]),some (2,[(2,0,1),(3,0,1)]),some (12,[(2,0,1),(3,0,1)]),some (12,[(1,2,3),(0,0,21),(1,41,5)]),some (1,[(1,0,1),(3,27,19)]),some (1,[(1,0,1),(2,19,5)]),some (1,[(0,0,1),(1,14,5)]),some (1,[(1,0,1),(3,8,19)]),some (12,[(1,2,3),(2,1,21),(1,48,5)]),some (12,[(2,1,2),(1,2,3),(3,1,21)]),some (2,[(1,2,3)]),some (12,[(1,2,3),(3,1,21)]),some (12,[(1,2,3),(0,1,21)]),some (1,[(0,1,21)]),some (12,[(1,2,3),(3,0,21)]),some (1,[(3,0,21)]),some (12,[(1,2,3),(2,0,21)]),some (12,[(1,2,3),(1,0,21)]),some (12,[(1,2,3),(0,0,21)]),some (9,[(1,22,2)]),some (1,[(2,1,3)]),some (12,[(2,1,3),(1,2,3)]),some (1,[(3,8,1)]),some (2,[(2,1,3)]),some (12,[(2,1,3),(1,11,5)]),some (1,[(1,1,3)]),some (1,[(0,1,3)]),some (1,[(3,15,3)]),some (2,[(2,1,2)]),some (1,[(2,15,3)]),some (12,[(1,2,3),(2,1,21)]),some (12,[(2,1,2),(2,15,3)]),some (1,[(1,15,3)]),some (12,[(2,1,2),(1,15,3)]),some (1,[(0,15,3)]),some (1,[(2,16,3)]),some (1,[(0,3,7)]),some (1,[(1,8,0)]),some (1,[(2,0,5)]),some (9,[(1,17,2)]),some (12,[(1,0,2),(1,29,3)]),some (1,[(1,29,3)]),some (2,[(1,0,3)]),some (1,[(3,0,3)]),some (2,[(3,0,3)]),some (2,[(2,0,3)]),some (1,[(2,0,3)]),some (12,[(1,0,3),(2,31,5)]),some (1,[(1,0,3)]),some (12,[(1,0,3),(3,2,31)]),some (12,[(1,0,3),(1,2,3)]),some (2,[(1,0,1)]),some (12,[(1,0,1)]),some (1,[(3,29,3)]),some (2,[(1,0,2)]),some (12,[(1,0,3),(0,1,31)]),some (1,[(0,1,29)]),some (12,[(1,0,2),(0,1,29)]),some (12,[(2,1,3),(1,11,2)]),some (9,[(3,0,1)]),some (1,[(3,0,1)]),some (1,[(1,26,3)]),some (2,[(3,2,3)]),some (1,[(2,29,3)]),some (12,[(1,0,2),(2,29,3)]),some (2,[(0,1,3)]),some (1,[(0,29,3)]),some (9,[(2,0,1)]),some (1,[(2,0,1)]),some (2,[(2,0,1)]),some (12,[(2,0,1)]),some (9,[(0,0,1)]),some (1,[(0,0,1)]),some (12,[(0,0,1),(1,0,1)]),some (1,[(1,0,1)]),some (2,[(3,0,1)]),some (12,[(3,0,1)]),some (9,[(3,2,18)]),some (9,[(3,2,28)]),some (1,[(1,1,5)]),some (2,[(1,1,3)]),some (2,[(0,0,1)]),some (12,[(0,0,1)]),some (12,[(1,2,3),(1,1,21)]),some (1,[(3,3,7)]),some (12,[(1,2,5),(3,3,7)]),some (1,[(1,15,0)]),some (9,[(1,0,1)]),some (12,[(1,1,3)]),some (12,[(2,1,3)]),some (1,[(1,0,5)]),some (1,[(2,1,5)]),some (12,[(2,0,3)]),some (12,[(1,0,3)])]
lemma gp_18 : goodPairs G_18 pos_18 neg_18 := goodPairs_of (by decide +kernel)
lemma base_18_ok : ∀ x ∈ base_18, faithful pos_18 neg_18 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_18_ok : btAll (fun x => faithful pos_18 neg_18 x ∧ x.1 < 2^128) W_18 := buildWiresBT_faithful base_18_ok
set_option maxRecDepth 500000 in
lemma autos_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_18 = G_18) autos_18 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_18_0_ok : sliceDirectCheck 8 16 0 R_18 G_18 R_3 G_3 = true := by decide +kernel
lemma sl_18_0 : Slice R_18 G_18 (subcubeFast 8 16) 5 := slice_fast_direct sl_18_0_ok low_3
lemma sl_18_1_ok : sliceDirectCheck 4 0 0 R_18 G_18 R_14 G_14 = true := by decide +kernel
lemma sl_18_1 : Slice R_18 G_18 (subcubeFast 4 0) 7 := slice_fast_direct sl_18_1_ok low_14
lemma sl_18_2_ok : sliceDirectCheck 16 0 0 R_18 G_18 R_11 G_11 = true := by decide +kernel
lemma sl_18_2 : Slice R_18 G_18 (subcubeFast 16 0) 7 := slice_fast_direct sl_18_2_ok low_11
lemma sl_18_3_ok : sliceDirectCheck 0 34 0 R_18 G_18 R_6 G_6 = true := by decide +kernel
lemma sl_18_3 : Slice R_18 G_18 (subcubeFast 0 34) 5 := slice_fast_direct sl_18_3_ok low_6
lemma sl_18_4_ok : sliceDirectCheck 40 0 0 R_18 G_18 R_7 G_7 = true := by decide +kernel
lemma sl_18_4 : Slice R_18 G_18 (subcubeFast 40 0) 5 := slice_fast_direct sl_18_4_ok low_7
lemma sl_18_5_ok : sliceDirectCheck 8 0 0 R_18 G_18 R_13 G_13 = true := by decide +kernel
lemma sl_18_5 : Slice R_18 G_18 (subcubeFast 8 0) 6 := slice_fast_direct sl_18_5_ok low_13
lemma sl_18_6_ok : sliceDirectCheck 1 2 0 R_18 G_18 R_5 G_5 = true := by decide +kernel
lemma sl_18_6 : Slice R_18 G_18 (subcubeFast 1 2) 5 := slice_fast_direct sl_18_6_ok low_5
lemma sl_18_7_ok : sliceDirectCheck 1 32 0 R_18 G_18 R_2 G_2 = true := by decide +kernel
lemma sl_18_7 : Slice R_18 G_18 (subcubeFast 1 32) 5 := slice_fast_direct sl_18_7_ok low_2
lemma sl_18_8_ok : sliceDirectCheck 1 34 0 R_18 G_18 R_0 G_0 = true := by decide +kernel
lemma sl_18_8 : Slice R_18 G_18 (subcubeFast 1 34) 4 := slice_fast_direct sl_18_8_ok low_0
lemma sl_18_9_ok : sliceDirectCheck 32 0 0 R_18 G_18 R_12 G_12 = true := by decide +kernel
lemma sl_18_9 : Slice R_18 G_18 (subcubeFast 32 0) 7 := slice_fast_direct sl_18_9_ok low_12
lemma sl_18_10_ok : sliceDirectCheck 0 2 0 R_18 G_18 R_17 G_17 = true := by decide +kernel
lemma sl_18_10 : Slice R_18 G_18 (subcubeFast 0 2) 6 := slice_fast_direct sl_18_10_ok low_17
lemma sl_18_11_ok : sliceDirectCheck 1 0 0 R_18 G_18 R_10 G_10 = true := by decide +kernel
lemma sl_18_11 : Slice R_18 G_18 (subcubeFast 1 0) 6 := slice_fast_direct sl_18_11_ok low_10
lemma sl_18_12_ok : sliceDirectCheck 0 16 0 R_18 G_18 R_16 G_16 = true := by decide +kernel
lemma sl_18_12 : Slice R_18 G_18 (subcubeFast 0 16) 8 := slice_fast_direct sl_18_12_ok low_16
lemma sl_18_13_ok : sliceDirectCheck 4 16 0 R_18 G_18 R_4 G_4 = true := by decide +kernel
lemma sl_18_13 : Slice R_18 G_18 (subcubeFast 4 16) 6 := slice_fast_direct sl_18_13_ok low_4
lemma sl_18_14_ok : sliceDirectCheck 48 0 0 R_18 G_18 R_8 G_8 = true := by decide +kernel
lemma sl_18_14 : Slice R_18 G_18 (subcubeFast 48 0) 6 := slice_fast_direct sl_18_14_ok low_8
lemma sl_18_15_ok : sliceDirectCheck 0 32 0 R_18 G_18 R_15 G_15 = true := by decide +kernel
lemma sl_18_15 : Slice R_18 G_18 (subcubeFast 0 32) 6 := slice_fast_direct sl_18_15_ok low_15
lemma sl_18_16_ok : sliceDirectCheck 40 16 0 R_18 G_18 R_1 G_1 = true := by decide +kernel
lemma sl_18_16 : Slice R_18 G_18 (subcubeFast 40 16) 4 := slice_fast_direct sl_18_16_ok low_1
lemma sl_18_17_ok : sliceDirectCheck 32 16 0 R_18 G_18 R_9 G_9 = true := by decide +kernel
lemma sl_18_17 : Slice R_18 G_18 (subcubeFast 32 16) 5 := slice_fast_direct sl_18_17_ok low_9
set_option maxRecDepth 500000 in
lemma slices_18_ok : btAll (fun o => ∀ p, o = some p → Slice R_18 G_18 p.1 p.2) slices_18 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_18 G_18 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (forall_cons (fun _ h => by cases h; exact sl_18_2) (forall_cons (fun _ h => by cases h; exact sl_18_3) (forall_cons (fun _ h => by cases h; exact sl_18_4) (forall_cons (fun _ h => by cases h; exact sl_18_5) (forall_cons (fun _ h => by cases h; exact sl_18_6) (forall_cons (fun _ h => by cases h; exact sl_18_7) (forall_cons (fun _ h => by cases h; exact sl_18_8) (forall_cons (fun _ h => by cases h; exact sl_18_9) (forall_cons (fun _ h => by cases h; exact sl_18_10) (forall_cons (fun _ h => by cases h; exact sl_18_11) (forall_cons (fun _ h => by cases h; exact sl_18_12) (forall_cons (fun _ h => by cases h; exact sl_18_13) (forall_cons (fun _ h => by cases h; exact sl_18_14) (forall_cons (fun _ h => by cases h; exact sl_18_15) (forall_cons (fun _ h => by cases h; exact sl_18_16) (forall_cons (fun _ h => by cases h; exact sl_18_17) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))
def bk_18_init : BT (List (List Nat)) := BT.empty
lemma bk_18_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 (0 - 1) xs.toFinset) bk_18_init := btAll.empty
def bk_18_0 : BT (List (List Nat)) := BT.empty
lemma bk_18_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 0 xs.toFinset) bk_18_0 := btAll.empty
def bk_18_1 : BT (List (List Nat)) := BT.empty
lemma bk_18_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 1 xs.toFinset) bk_18_1 := btAll.empty
def bk_18_2 : BT (List (List Nat)) := BT.empty
lemma bk_18_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 2 xs.toFinset) bk_18_2 := btAll.empty
def bk_18_3 : BT (List (List Nat)) := BT.empty
lemma bk_18_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 3 xs.toFinset) bk_18_3 := btAll.empty
def nodes_18_4 : List NodeSpec := [([287,0,1,2,5],[],[]),([15,121,0,12,5],[],[]),([0,1,251,4,7],[],[]),([183,288,2,4,5],[],[]),([121,0,69,2,5],[],[]),([289,0,1,2,5],[],[]),([183,114,2,4,5],[],[]),([285,0,1,4,7],[],[]),([15,290,0,3,4],[],[]),([0,114,80,4,7],[],[]),([121,0,70,3,5],[],[]),([1,259,29,3,5],[],[]),([70,50,21,4,5],[],[])]
def P_18_4 : BT (Option BoundPool) := buildPoolsSubBT 8 W_18 R_18 slices_18 ps_18 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_4 : checkNodesBT W_18 G_18 fmask_18 P_18_4 autos_18 bk_18_3 4 nodes_18_4 = true := by decide +kernel
def bk_18_4 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_4
set_option maxRecDepth 500000 in
lemma bk_18_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 4 xs.toFinset) bk_18_4 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound slices_18_ok) autos_18_ok bk_18_3_ok chk_18_4
def nodes_18_5 : List NodeSpec := [([107,36,0,2,3,5],[],[]),([0,1,2,3,237,5],[],[]),([0,1,72,3,35,5],[],[]),([238,0,1,2,3,5],[],[]),([239,0,2,3,4,5],[],[]),([107,0,37,2,3,5],[],[]),([38,1,2,3,108,5],[],[]),([77,0,1,2,35,5],[],[]),([0,1,2,3,35,219],[],[]),([0,120,2,3,35,5],[],[]),([112,0,1,2,3,35],[],[]),([0,45,9,2,3,103],[],[]),([0,240,1,2,3,5],[],[]),([134,188,0,1,2,5],[],[0]),([241,1,101,2,3,5],[],[]),([0,1,181,2,139,5],[0,1],[0]),([121,0,1,2,3,242],[],[]),([11,121,0,1,2,5],[2],[]),([48,132,0,2,4,5],[0,3,4,5],[]),([11,243,0,2,4,5],[6],[]),([0,1,2,52,46,4],[],[]),([244,1,2,3,4,5],[],[]),([0,1,2,3,245,4],[],[]),([0,37,2,3,4,47],[],[]),([246,0,101,2,3,5],[],[]),([132,0,2,72,4,5],[],[]),([0,1,2,52,35,5],[],[]),([66,0,1,3,35,5],[],[]),([124,0,1,72,3,4],[],[]),([0,1,2,3,35,185],[],[]),([197,0,1,2,35,5],[],[]),([247,132,0,2,4,5],[0,7,4,5],[]),([132,0,2,248,4,5],[8],[]),([15,36,0,3,35,5],[],[]),([15,121,0,1,3,5],[],[0]),([15,249,0,1,3,4],[],[]),([41,1,2,3,108,5],[],[]),([0,1,2,52,136,4],[],[]),([0,1,2,52,176,5],[],[]),([250,0,1,101,2,5],[],[]),([0,37,2,3,4,185],[],[]),([113,0,2,3,35,5],[],[]),([0,1,72,3,128,4],[],[]),([0,37,72,3,4,5],[],[]),([0,12,9,2,52,5],[],[]),([0,1,2,251,4,5],[],[0]),([15,0,45,3,4,7],[],[0]),([186,0,1,2,3,252],[],[]),([253,0,1,2,3,5],[],[]),([11,186,0,1,2,5],[],[]),([186,0,12,1,2,5],[],[]),([254,0,1,2,3,5],[],[]),([63,0,37,2,3,5],[],[]),([255,0,1,2,3,5],[],[]),([0,1,2,3,256,5],[],[]),([0,1,2,3,176,185],[],[]),([257,0,1,2,3,5],[],[]),([0,114,2,3,221,5],[],[]),([148,0,1,2,150,5],[],[0]),([258,63,0,2,3,5],[],[]),([0,153,1,2,35,5],[],[]),([0,1,259,2,3,5],[],[0]),([66,0,1,3,164,4],[],[]),([260,0,1,101,3,5],[],[]),([0,1,2,3,261,4],[],[]),([262,0,1,2,3,4],[],[]),([77,0,1,2,84,4],[],[]),([263,0,1,2,3,5],[],[]),([65,0,114,2,3,4],[],[]),([161,2,3,21,4,5],[],[]),([11,0,230,2,4,5],[],[]),([121,0,1,2,31,5],[],[0]),([41,1,29,3,35,5],[],[]),([20,186,0,1,2,5],[],[]),([8,0,69,9,2,5],[9],[]),([66,38,1,3,4,5],[],[]),([264,0,1,2,3,5],[],[]),([265,0,1,2,3,5],[],[]),([25,114,2,31,4,5],[],[0]),([183,1,2,266,4,5],[9,10,0,5,11],[0]),([41,1,2,31,35,5],[],[]),([0,267,2,3,4,5],[],[]),([112,0,1,2,3,221],[],[]),([77,0,1,2,221,5],[],[]),([15,0,12,9,21,5],[],[0]),([15,0,230,3,4,5],[],[]),([77,67,0,1,4,7],[],[0]),([112,0,114,2,3,4],[],[]),([0,114,2,3,184,4],[],[]),([268,0,1,2,3,5],[],[]),([1,50,29,21,4,5],[9],[0]),([113,0,2,3,221,5],[],[]),([115,0,2,3,35,5],[],[]),([0,269,114,2,3,5],[],[]),([15,0,37,3,4,7],[],[]),([270,1,2,31,4,5],[6],[]),([121,0,12,1,2,5],[],[0]),([66,0,1,3,221,5],[],[]),([97,70,2,3,4,5],[12],[]),([0,114,2,80,4,5],[],[0]),([0,114,9,2,3,5],[],[]),([38,1,29,3,4,7],[],[]),([0,1,72,3,176,5],[],[]),([79,0,45,3,4,5],[],[]),([0,1,80,40,4,7],[13,5],[0]),([271,0,1,2,3,5],[],[]),([0,37,2,52,4,5],[],[]),([121,20,0,1,2,5],[],[]),([77,38,1,2,4,5],[],[]),([11,36,0,2,35,5],[],[]),([49,69,2,3,4,5],[],[]),([0,272,2,3,4,5],[],[]),([1,101,29,3,21,5],[],[0]),([0,37,2,87,4,5],[],[]),([186,0,1,2,31,5],[],[]),([273,0,1,29,3,4],[],[]),([0,114,2,3,35,5],[],[]),([63,0,274,2,3,5],[],[]),([63,0,1,275,3,5],[],[]),([66,183,1,2,4,5],[5,11],[]),([63,0,1,2,276,5],[],[]),([54,0,1,52,4,7],[],[0]),([0,114,2,3,84,4],[],[]),([277,0,1,2,3,4],[],[]),([70,101,2,29,3,5],[12],[]),([77,0,114,2,4,5],[],[]),([278,1,101,2,3,5],[],[]),([0,37,2,3,4,94],[],[]),([66,0,1,162,3,4],[],[]),([0,70,12,21,4,5],[],[0]),([66,0,114,3,4,5],[],[]),([0,1,279,2,3,4],[],[]),([0,12,2,177,4,5],[],[]),([70,50,2,3,4,5],[12],[0]),([0,1,2,3,35,145],[],[]),([33,0,114,2,3,5],[],[]),([59,1,29,3,4,7],[],[]),([121,0,1,29,3,5],[],[0]),([190,1,101,29,3,5],[12],[]),([186,0,1,29,3,5],[],[]),([77,66,0,1,4,5],[],[]),([8,0,1,156,4,5],[],[]),([0,1,101,2,280,5],[],[]),([0,1,2,3,281,4],[],[]),([77,0,1,2,184,4],[],[]),([113,0,2,3,184,4],[],[]),([131,30,0,2,3,4],[],[]),([282,1,101,2,3,5],[],[]),([0,70,9,3,21,5],[],[0]),([63,0,283,2,3,5],[],[]),([14,109,2,3,4,5],[],[]),([0,1,72,52,4,5],[],[]),([77,0,1,72,4,5],[],[]),([63,0,1,2,284,5],[],[]),([0,114,29,3,4,7],[],[0]),([131,0,19,2,3,4],[5],[]),([8,161,2,3,4,5],[14],[]),([0,114,2,3,4,5],[],[]),([66,0,1,52,4,5],[],[]),([183,1,2,40,4,5],[9,10,0,5,11],[0]),([0,69,9,2,21,5],[],[0]),([0,37,98,3,4,5],[],[]),([0,114,98,3,4,5],[],[]),([154,189,0,1,2,5],[15],[0]),([236,0,1,156,4,5],[],[]),([15,186,0,1,3,5],[],[]),([0,114,2,87,4,5],[],[]),([182,8,0,1,4,5],[],[]),([285,0,1,2,4,5],[],[0]),([0,45,101,2,3,5],[],[]),([48,0,1,51,4,7],[16,5],[0]),([286,183,1,2,4,5],[5,11,17],[]),([182,173,0,1,4,5],[],[])]
def P_18_5 : BT (Option BoundPool) := buildPoolsSubBT 8 W_18 R_18 slices_18 ps_18 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_5 : checkNodesBT W_18 G_18 fmask_18 P_18_5 autos_18 bk_18_4 5 nodes_18_5 = true := by decide +kernel
def bk_18_5 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_5
set_option maxRecDepth 500000 in
lemma bk_18_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 5 xs.toFinset) bk_18_5 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound slices_18_ok) autos_18_ok bk_18_4_ok chk_18_5
def nd_18_6_0 : List NodeSpec := [([0,45,1,2,3,4,103],[18],[0]),([0,1,104,2,3,4,5],[20],[]),([105,0,59,1,2,3,4],[18],[]),([106,0,1,2,3,4,5],[21],[]),([107,0,1,2,3,21,5],[23],[0]),([0,1,2,3,21,108,5],[23],[0]),([36,0,1,2,3,35,5],[0,25,23],[0]),([0,1,2,3,35,93,5],[],[0]),([56,0,1,2,21,4,5],[20],[]),([0,37,2,3,93,4,5],[],[0]),([0,1,109,2,3,4,5],[19,6,24,22,18,26],[0]),([38,0,1,2,3,35,5],[24,22],[0]),([110,38,0,1,2,3,5],[22],[0]),([56,0,1,2,3,111,4],[26],[]),([112,0,1,2,3,21,4],[27],[0]),([20,33,0,1,2,21,5],[],[0]),([0,1,2,3,35,40,5],[25],[0]),([83,0,1,2,3,57],[11,4,28,29],[]),([77,0,1,2,21,4,5],[22],[0]),([113,0,2,3,21,4,5],[30],[0]),([30,0,45,2,3,4,5],[11,31],[]),([0,114,2,3,21,4,5],[32],[0]),([115,0,2,3,21,4,5],[33],[0]),([116,0,1,2,3,4,5],[34],[]),([117,0,1,2,3,4,5],[26,18],[]),([0,1,2,91,21,4,5],[20],[]),([0,1,2,3,118,4,5],[35],[]),([0,1,2,3,119,4,5],[24,22],[]),([0,120,2,3,21,4,5],[36],[0]),([8,0,69,1,2,4,5],[9,19],[0]),([0,37,2,3,4,5,28],[18],[]),([33,0,45,1,2,3,5],[31,11,25],[]),([0,45,9,1,2,3,5],[4,25],[]),([121,0,1,2,3,5],[38,22,37],[0]),([0,19,2,72,3,4,5],[11],[]),([41,1,2,3,40,4,5],[],[0]),([90,0,1,3,21,4,5],[20,26],[]),([11,0,1,2,3,122,4],[4],[]),([11,123,0,1,2,4,5],[5],[]),([11,36,0,2,21,4,5],[39],[0]),([11,0,37,2,21,4,5],[20],[]),([0,1,2,76,21,4,5],[21],[]),([11,0,9,1,2,21,5],[20,40],[0]),([11,0,1,2,46,21,4],[4],[]),([0,1,80,29,21,4,5],[23],[]),([11,124,0,1,2,3,4],[5,41,4],[0]),([11,8,0,1,2,4,47],[],[]),([15,0,1,51,3,4,7],[23,42,4],[0]),([53,8,0,1,2,4,5],[],[]),([0,1,2,3,125,4,5],[18,24,22],[]),([0,1,2,3,126,4,5],[24,22],[0]),([127,0,1,2,3,4,5],[],[]),([11,0,1,2,21,4,47],[41,4],[]),([0,1,2,3,21,4,47],[44,4,43],[0]),([48,11,24,0,2,4,5],[0,45,4,5],[0]),([48,0,1,2,3,46,4],[46,25],[0]),([48,0,1,2,3,4,47],[44,43],[0]),([0,45,19,2,3,4,5],[5,11,31],[0]),([0,1,2,72,3,46,4],[26,18],[0]),([11,0,1,2,3,128,4],[47,5,26],[0]),([129,0,1,2,72,3,4],[26],[0]),([0,1,101,2,130,3,5],[12,48,25],[0]),([0,9,1,2,72,3,5],[40,4,25],[]),([131,0,1,2,3,4],[44,50,49],[0]),([11,132,0,2,4,5],[5,9,0,4,51],[0]),([66,0,1,2,3,84,4],[18,26],[0]),([0,1,2,52,31,4,5],[21,52],[0]),([0,59,9,1,2,3,5],[25,4],[]),([8,0,49,1,2,4,5],[9,19],[]),([55,97,1,2,3,4,5],[12],[0]),([0,1,2,80,40,4,5],[53,5],[0]),([22,0,37,2,3,4,5],[18],[]),([0,49,1,2,21,4,5],[],[]),([99,0,1,3,21,4,5],[20],[]),([0,12,1,2,35,21,5],[],[0]),([0,12,9,1,2,21,5],[20],[0]),([132,0,2,4,5],[9,0,5,8],[0]),([0,9,1,2,102,3,5],[24,23],[]),([0,1,50,2,21,4,5],[9],[0]),([133,0,1,2,3,4,5],[18,26],[]),([38,0,9,1,2,3,5],[24],[0]),([77,0,1,29,21,4,5],[],[]),([15,0,37,3,21,4,5],[20],[]),([15,0,9,1,3,21,5],[20],[0]),([15,0,12,1,21,4,5],[20],[0]),([15,0,12,9,2,3,5],[23,4],[0]),([134,0,1,101,2,3,5],[54],[0]),([48,15,0,1,3,4,7],[23,42,4,55],[0]),([48,0,1,2,51,4,5],[56,5],[0]),([77,33,0,1,2,3,5],[],[]),([48,0,9,1,2,3,5],[25,22,4],[]),([135,0,1,98,3,4],[12],[]),([48,0,1,2,3,136,4],[26,46,25],[0]),([27,0,49,1,2,3,4],[12],[]),([0,1,2,3,52,4,5],[],[]),([0,1,2,137,71,3,5],[22],[]),([0,37,1,2,3,4,5],[24,22],[]),([15,0,1,3,52,4,7],[],[0]),([0,1,2,3,84,40,4],[12,25,46],[0]),([48,0,1,2,52,4,5],[57,52],[0]),([0,9,1,2,3,52,5],[23],[0]),([0,12,1,2,52,4,5],[6],[0]),([138,0,1,2,3,4,5],[],[]),([54,15,0,1,3,4,7],[],[0]),([54,0,1,2,52,4,5],[58],[0]),([11,24,0,2,72,4,5],[59,4,5],[0]),([15,0,45,2,3,4,5],[6,19],[0]),([15,0,70,2,3,4,5],[12],[0]),([0,97,1,3,21,4,5],[],[]),([33,0,59,1,2,3,5],[25,11],[]),([0,1,101,2,3,139,5],[60,12,48,61],[0]),([48,0,1,72,3,4,5],[22],[0]),([0,1,2,3,140,4,5],[24,22],[]),([15,0,1,51,21,4,5],[23],[]),([141,0,1,2,3,4,5],[26],[]),([0,1,2,60,21,4,5],[26],[]),([0,1,2,142,3,4,5],[20],[]),([0,1,2,3,143,4,5],[18,26],[]),([144,0,1,2,3,4,5],[62],[]),([0,1,2,3,21,4,145],[63],[0]),([0,1,2,3,146,4,5],[21],[]),([15,0,1,102,3,4,5],[19],[]),([0,1,101,2,3,21,5],[],[0]),([38,33,0,1,2,3,5],[24,22],[]),([15,33,0,1,3,21,5],[9],[0]),([33,0,1,2,72,3,5],[11,25],[]),([0,114,2,3,31,4,5],[64],[0]),([33,0,12,1,2,21,5],[],[0]),([33,0,1,2,102,3,5],[24],[0]),([48,33,0,1,2,3,5],[25,11],[0]),([147,0,1,2,3,4,5],[18,22,24,26],[]),([148,63,0,1,2,3,5],[12,25],[0]),([0,49,1,2,3,46,4],[12],[]),([149,0,1,2,3,4,5],[22,24],[]),([8,63,0,1,2,3,5],[65],[]),([63,0,1,2,3,21,5],[9],[0]),([63,0,1,2,3,150,5],[66],[0]),([8,32,30,2,3,4,5],[67],[0]),([0,1,2,72,3,4,47],[26,18],[0]),([0,37,2,3,10,4,5],[6],[]),([151,63,0,1,2,3,5],[12,25],[0]),([20,0,1,2,35,21,5],[],[0]),([152,0,1,2,3,4,5],[22,24],[]),([0,153,1,2,21,4,5],[6],[0]),([154,63,0,1,2,3,5],[68,65,12],[0]),([20,0,1,2,52,4,5],[],[]),([15,0,1,72,3,4,5],[4],[0]),([0,155,1,2,3,4,5],[24,22],[]),([33,0,1,2,71,3,5],[24,23],[]),([79,0,1,3,156,4,5],[69,4],[0]),([74,0,1,2,21,4,5],[9],[]),([0,1,29,3,40,4,7],[12,70,23,71],[0]),([157,0,1,2,3,4,5],[6,22,24,26,18],[]),([158,66,0,1,2,3,4],[26],[0]),([0,159,1,2,3,4,5],[22,24],[]),([15,0,1,31,21,4,5],[9],[]),([0,1,2,160,3,4,5],[26,18],[]),([15,0,37,2,3,4,5],[19],[0]),([23,38,1,2,3,4,5],[6],[]),([0,1,100,3,21,4,5],[21],[]),([161,2,3,4,5],[9,72,11,14],[0]),([0,1,2,162,3,31,4],[73,11,18],[0]),([63,0,1,2,163,3,5],[65,12,25],[]),([0,1,2,162,3,4],[11,4],[]),([0,1,2,3,31,164,4],[5,74,26],[0]),([0,1,165,2,3,31,4],[5],[]),([0,1,2,3,166,31,4],[11],[]),([167,0,1,2,3,4,5],[75],[]),([53,0,1,2,3,46,4],[11],[]),([15,0,1,3,35,21,5],[0],[0]),([168,0,1,2,3,4,5],[22,24],[]),([0,1,2,3,166,4],[12,76],[]),([65,66,0,1,2,3,4],[26,18],[0]),([48,0,1,2,3,35,5],[25],[0]),([53,0,1,2,21,4,5],[19],[]),([169,66,0,1,2,3,4],[18],[0]),([11,0,170,2,3,4,5],[20],[]),([171,0,1,2,3,4],[12],[]),([25,1,2,31,40,4,5],[9,77,0,5,11],[0]),([0,172,1,2,3,4,5],[26,18],[]),([65,0,1,2,3,40,4],[4,78,44],[0]),([173,0,1,98,3,4,5],[],[0]),([65,8,0,1,2,31,4],[],[]),([0,45,9,2,3,5],[44,31,79],[0]),([38,1,2,3,31,4,5],[6],[0]),([0,1,2,84,31,21,4],[11],[]),([8,14,19,2,3,4,5],[80],[0]),([41,1,2,31,21,4,5],[],[0]),([0,1,2,3,21,4,94],[4,81,82],[0]),([0,69,1,2,3,84,4],[12,83],[]),([27,0,69,1,2,3,4],[11,83],[]),([174,0,70,1,2,3,4],[12,84],[]),([0,1,2,3,175,4,5],[20,24,22,18,26],[]),([48,0,1,2,3,176,5],[22,25],[0]),([8,0,9,1,2,31,5],[9],[0]),([11,0,69,2,3,4,5],[9],[0]),([15,66,0,1,3,4,5],[4],[0]),([0,1,2,3,177,4,5],[24,22],[0]),([0,1,2,178,3,4,5],[22,24],[]),([0,1,2,3,179,4,5],[20,18,26],[]),([180,0,1,2,3,4,5],[21],[]),([65,0,1,2,31,21,4],[11,73],[]),([66,0,1,2,3,4,5],[18,26],[]),([15,0,1,52,21,4,5],[],[]),([79,0,1,3,21,4,5],[6,85,86],[]),([97,1,2,29,3,4,5],[12],[0]),([66,33,0,1,2,3,5],[25,11],[]),([66,25,1,2,31,4,5],[5,11,87],[0]),([55,0,70,2,3,4,5],[12],[0]),([167,0,1,2,87,4,5],[75],[]),([38,0,1,2,3,4,5],[24,22],[]),([0,1,181,101,2,3,5],[9],[0]),([33,0,1,2,31,21,5],[21],[0]),([182,0,1,2,3,4,5],[21,26,18],[0]),([183,1,2,4,5],[9,5,0,11,17],[0]),([0,1,2,52,21,4,5],[22],[0]),([38,1,2,29,3,4,5],[19],[0]),([77,0,1,2,40,4,5],[22],[0]),([112,0,1,2,3,40,4],[18,4,88],[0]),([0,69,1,2,21,4,5],[89,9],[0]),([48,0,1,2,3,4,5],[22,24,26,18],[]),([0,1,2,3,184,40,4],[26,25,46],[0]),([48,0,1,2,3,4,185],[90,18],[0]),([113,0,2,3,40,4,5],[91,4],[0]),([33,0,1,29,3,21,5],[21],[0]),([0,114,2,3,40,4,5],[20,92],[0]),([186,0,1,2,3,21,5],[24],[]),([0,114,1,2,3,4,5],[92,24],[0]),([0,1,2,187,3,4,5],[93],[]),([38,1,2,3,40,4,5],[22],[0]),([20,0,1,29,21,4,5],[21],[]),([188,0,1,101,2,3,5],[12,25],[0]),([11,0,1,2,52,4,5],[52,6],[0]),([11,27,0,19,2,3,4],[5],[0]),([189,63,0,1,2,3,5],[],[0]),([11,8,0,19,2,4,5],[],[]),([190,0,1,101,2,3,5],[25,12,61],[0]),([124,0,1,2,3,4],[11,4],[]),([48,36,0,2,3,4,5],[4],[0]),([77,0,1,2,3,4,5],[],[]),([67,0,1,29,3,4,7],[],[0]),([77,0,1,29,3,4,7],[],[0]),([0,1,80,29,3,4,7],[23,70,11],[0]),([0,1,29,3,35,21,5],[0],[0]),([41,1,29,3,21,4,5],[94],[0]),([0,9,1,2,31,21,5],[9],[0]),([77,0,1,2,31,4,5],[6,95],[0]),([77,0,9,1,2,3,5],[],[]),([14,0,37,2,3,4,5],[],[0]),([0,114,2,29,3,4,5],[96],[0])]
def P_18_6_0 : BT (Option BoundPool) := buildPoolsSubBT 8 W_18 R_18 slices_18 ps_18 [0,4,5,6,8,9,11,12,14,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_6_0 : checkNodesBT W_18 G_18 fmask_18 P_18_6_0 autos_18 bk_18_5 6 nd_18_6_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_18_6_0 : ∀ ns ∈ nd_18_6_0, Impossible G_18 6 (nodeValsBT W_18 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound slices_18_ok) autos_18_ok bk_18_5_ok chk_18_6_0
def nd_18_6_1 : List NodeSpec := [([0,1,2,3,191,4,5],[20],[]),([0,1,61,3,21,4,5],[26],[]),([15,0,192,2,3,4,5],[4],[]),([11,0,1,29,21,4,5],[9],[]),([193,79,0,1,2,3,4],[4],[]),([0,1,2,194,3,4,5],[22,24],[]),([0,1,72,29,3,4,5],[11],[0]),([0,1,195,2,3,4,5],[24,22],[]),([32,0,37,2,3,4,5],[],[0]),([0,1,2,196,3,4,5],[24,22],[0]),([0,37,9,1,2,3,5],[24,22],[]),([197,0,1,2,21,4,5],[6],[0]),([11,0,1,2,21,4,5],[20],[]),([11,8,33,0,1,2,5],[],[]),([11,33,0,1,2,21,5],[9],[0]),([85,0,1,2,198,4,5],[97],[]),([27,0,1,2,87,4],[12],[]),([0,1,98,3,21,4,5],[9,98,99],[0]),([77,0,12,1,2,4,5],[20],[]),([0,199,97,1,2,3,4],[12],[]),([0,12,1,29,21,4,5],[9],[0]),([0,19,2,3,52,4,5],[],[]),([186,0,1,2,3,5],[100,22,37],[0]),([49,1,2,3,31,4,5],[9],[0]),([0,1,29,102,3,4,5],[21],[]),([0,1,2,72,3,4,200],[18],[0]),([77,67,0,1,2,4,5],[101],[0]),([0,1,2,201,3,4,5],[6,24,22,18,26],[0]),([33,0,37,1,2,3,5],[24],[0]),([0,70,9,2,3,5],[12,84,102],[0]),([0,1,202,2,31,4,5],[5],[]),([203,0,1,2,3,4,5],[22,24],[]),([0,70,12,2,3,4,5],[12],[0]),([11,8,0,9,1,2,5],[20],[]),([0,1,71,29,3,4,5],[19],[]),([152,85,0,1,2,4,5],[103,104],[]),([33,0,1,2,3,52,5],[],[]),([0,1,2,87,21,4,5],[9,105,106],[0]),([11,27,30,0,2,3,4],[5,11],[0]),([0,1,2,3,122,4],[12,107],[]),([1,50,2,29,3,4,5],[19,12,6],[0]),([65,0,1,2,3,21,4],[44,78],[]),([27,32,30,2,3,4],[12],[]),([11,0,19,2,3,46,4],[11,5],[]),([11,30,0,2,3,46,4],[12],[]),([204,0,1,2,3,4,5],[26,18],[]),([0,1,165,2,3,4],[44,109,108],[]),([30,0,2,72,3,4,5],[11],[]),([20,0,9,1,2,21,5],[],[0]),([0,1,2,31,21,4,5],[21],[]),([0,114,2,3,4,5],[92,96],[0]),([0,1,2,31,35,21,5],[23],[0]),([0,1,2,72,3,4,5],[26,18],[]),([11,0,1,72,21,4,5],[],[]),([0,1,72,3,21,4,5],[110],[0]),([205,0,1,2,3,4,5],[111],[]),([8,0,1,101,2,3,5],[9,61],[0]),([11,8,30,0,2,4,5],[],[]),([15,30,0,3,21,4,5],[9],[]),([66,0,1,3,21,4,5],[112],[0]),([11,131,0,1,2,3,4],[5],[]),([15,30,97,2,3,4,5],[12],[]),([0,1,206,98,3,4,5],[99,98,11,113],[]),([207,0,1,2,3,4,5],[22,24,26,18],[0]),([77,20,0,1,2,4,5],[6],[]),([86,0,1,2,3,21,4],[114,115],[]),([41,0,1,2,3,35,5],[0,25,23],[0]),([27,0,1,98,3,4],[12],[]),([0,208,37,1,2,3,5],[22],[0]),([209,0,1,2,3,4,5],[18,26],[]),([11,30,0,2,21,4,5],[9],[]),([53,49,1,2,3,4,5],[9],[0]),([1,101,2,29,3,5],[12,61,116],[0]),([53,0,1,2,3,84,4],[4],[]),([0,1,96,3,21,4,5],[20],[]),([0,1,29,31,21,4,5],[21],[]),([0,9,1,2,3,40,5],[25,4],[0]),([27,0,1,2,3,91,4],[18],[0]),([38,1,2,31,21,4,5],[21],[]),([66,0,1,29,3,4,5],[11],[0]),([66,0,1,31,21,4,5],[],[]),([135,0,1,2,98,3,4],[11],[]),([0,1,2,3,40,4,5],[20,24,22,18,26],[0]),([121,0,1,2,3,21,5],[24],[]),([0,1,2,210,3,4,5],[26,18],[]),([211,0,1,2,3,4,5],[26,18],[]),([55,0,1,3,21,4,5],[6],[]),([212,0,1,2,3,4,5],[],[]),([38,1,29,3,21,4,5],[21],[]),([0,1,2,213,102,3,5],[22],[]),([15,20,0,1,21,4,5],[9],[]),([0,1,2,3,214,76,4],[26],[]),([215,0,1,2,3,4,5],[19,6,24,22],[]),([0,9,1,29,3,21,5],[9],[0]),([8,0,1,2,91,4,5],[],[]),([32,30,2,3,21,4,5],[117,118],[0]),([11,0,37,2,3,4,5],[6],[0]),([11,15,0,1,21,4,5],[20],[]),([0,1,2,216,3,4],[11,4],[]),([85,8,0,1,2,4,5],[19],[]),([0,1,2,217,3,4,5],[26],[]),([0,70,9,2,29,3,5],[12],[0]),([11,30,49,2,3,4,5],[12],[]),([218,0,1,2,3,4],[11,4],[]),([85,0,1,2,21,4,5],[19,104,103],[]),([0,1,2,3,21,4,219],[119],[0]),([0,1,2,198,3,4,5],[97],[]),([79,8,0,1,3,4,5],[20],[0]),([85,27,0,1,2,4],[12],[]),([27,0,1,2,3,87,4],[],[]),([79,0,1,220,3,4,5],[86,85,4,69],[]),([0,1,2,3,221,40,5],[22,25],[0]),([0,1,2,3,222,91,4],[26],[]),([0,9,1,2,71,3,5],[24],[0]),([33,0,1,2,3,40,5],[25,22,9,11],[0]),([223,0,1,2,3,4,5],[24,22],[]),([8,0,1,98,3,4,5],[21],[0]),([0,69,9,2,3,5],[12,83],[0]),([0,1,98,3,126,4,5],[9,98,99],[0]),([0,1,224,2,3,4],[12,120],[]),([83,0,1,2,21,4,5],[26],[]),([86,8,0,1,2,3,4],[121],[]),([53,27,0,1,2,3,4],[18],[0]),([11,77,0,1,2,4,5],[20,95],[0]),([15,0,1,71,3,4,5],[20],[]),([0,69,9,2,3,31,5],[12,83],[]),([53,0,1,2,3,225,4],[26],[]),([0,1,2,3,156,4,5],[20,18,26],[0]),([226,0,1,2,3,4,5],[24,22],[]),([227,0,1,2,3,4,5],[],[]),([79,27,0,1,3,4],[12,69],[]),([152,79,0,1,3,4,5],[86,85],[]),([43,0,1,2,21,4,5],[20,26],[]),([0,1,2,87,126,4,5],[9,105,106],[0]),([0,228,1,2,3,4,5],[],[]),([48,0,19,2,3,4,5],[11],[0]),([39,0,1,2,3,35,5],[],[0]),([66,0,1,3,40,4,5],[22],[0]),([8,0,1,2,87,4,5],[19],[]),([39,38,1,2,3,4,5],[],[0]),([8,0,1,2,3,4,94],[122],[]),([48,0,37,2,3,4,5],[22],[0]),([0,1,229,2,3,4,5],[123],[]),([8,33,0,1,2,31,5],[],[]),([0,37,1,2,3,35,5],[24,22],[0]),([30,0,2,3,52,4,5],[],[]),([11,0,19,2,21,4,5],[],[0]),([0,1,230,2,3,4,5],[21,19,6,24,22],[0]),([15,0,19,3,21,4,5],[],[0]),([231,0,1,2,3,4,5],[21,26,18],[]),([0,1,2,3,232,4,5],[],[]),([53,0,69,2,3,4,5],[9],[0]),([11,0,1,2,35,21,5],[23],[0]),([14,19,2,3,21,4,5],[],[0]),([0,70,1,3,21,4,5],[9],[0]),([0,1,2,3,233,4,5],[20,24,22,26],[0]),([234,0,1,2,3,4,5],[18,26],[]),([0,1,2,3,21,4,185],[4,124],[0]),([85,27,0,1,2,3,4],[],[]),([15,36,0,3,21,4,5],[125],[0]),([66,0,9,1,2,3,5],[25,4],[]),([193,79,0,1,3,4],[12,69],[]),([182,0,1,98,3,4,5],[11,113],[0]),([48,30,0,2,3,4,5],[11],[]),([235,0,1,2,3,4,5],[19,6,22,24,26,18],[]),([183,1,2,31,4,5],[5,9,11,0,17],[0]),([59,1,2,29,3,4,5],[19,6],[0]),([236,79,0,1,3,4,5],[20],[0])]
def P_18_6_1 : BT (Option BoundPool) := buildPoolsSubBT 8 W_18 R_18 slices_18 ps_18 [0,4,5,6,9,11,12,17,18,19,20,21,22,23,24,25,26,37,44,61,69,78,83,84,85,86,92,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_6_1 : checkNodesBT W_18 G_18 fmask_18 P_18_6_1 autos_18 bk_18_5 6 nd_18_6_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_18_6_1 : ∀ ns ∈ nd_18_6_1, Impossible G_18 6 (nodeValsBT W_18 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound slices_18_ok) autos_18_ok bk_18_5_ok chk_18_6_1
def nodes_18_6 : List NodeSpec := nd_18_6_0 ++ nd_18_6_1
def bk_18_6 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_6
set_option maxRecDepth 500000 in
lemma bk_18_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 6 xs.toFinset) bk_18_6 :=
  buildBucketsBT_of_mem (forall_append (mem_18_6_0) mem_18_6_1)
def nodes_18_7 : List NodeSpec := [([0,1,2,34,3,4,5],[11,5,4,24,22],[]),([0,1,2,3,35,21,5],[23,37,0],[0]),([36,0,1,2,3,21,4,5],[23,5,127,126,20],[0]),([0,37,1,2,3,21,4,5],[23,6,128,20,126],[0]),([0,37,1,2,3,4,5],[129,128,21,18,26,6,24],[0]),([38,0,1,2,3,21,4,5],[23,6,130,21,126],[0]),([38,0,1,2,3,4,5],[131,130,20,18,26,6,24],[0]),([39,0,1,2,3,21,4,5],[132,126,21],[0]),([0,1,2,3,21,40,4,5],[133,21,126,5],[0]),([41,0,1,2,3,21,4,5],[23,5,134,126,21],[0]),([0,1,2,42,3,4,5],[11,4,135,6,24,22],[0]),([43,0,1,2,3,4,5],[11,5,20,19,24,22],[0]),([0,1,2,3,21,4,5,28],[20,5,23,26,25,46,126],[0]),([0,9,1,2,3,21,5],[23,126,9,0,25,4],[0]),([0,1,44,3,4,5],[9,5,0,4],[]),([11,0,1,2,21,4,5],[136,9,137,6,4],[0]),([11,0,9,1,2,3,5],[9,49,4,40,0],[0]),([11,24,0,2,4,5],[9,5,0,4,59],[0]),([0,45,1,2,3,4,5],[5,0,138,21,26],[0]),([11,0,1,2,3,46,4],[44,12,49,47],[0]),([11,0,1,2,3,21,4,5],[5,19,20,0,139],[0]),([11,0,1,2,3,4,47],[12,5,140,41],[0]),([0,1,2,3,4,47],[11,4,140,44,41],[0]),([48,11,0,1,2,3,4,5],[136,0,139,4,5],[0]),([11,0,49,1,2,3,4,5],[12,6],[0]),([0,49,1,2,3,4,5],[12,19,24,22],[0]),([27,0,1,2,3,10,4],[12,5,23,25,141],[]),([0,12,1,2,3,4,7],[12,5,142,23,25],[]),([11,0,1,2,3,4,5],[9,5,4,19,24,22],[0]),([0,1,50,2,3,4,5],[12,5,19,24,22],[0]),([0,1,2,44,3,4,5],[9,5,0,4],[]),([15,0,1,3,4,7],[12,23],[0]),([11,15,0,1,2,3,4,5],[4,19,6,55],[0]),([15,0,1,2,51,3,4,5],[143,4,23,6,144,55],[0]),([48,15,0,1,2,3,4,5],[6,23,144,4,55,145],[0]),([48,0,1,2,3,21,4,5],[146,20,126,5],[0]),([48,0,1,2,3,4,5],[147,145,18,26,21,24],[0]),([15,0,1,2,3,52,4,5],[148,6,20],[0]),([0,1,2,3,52,4,5],[148,149,52,21,26,6],[0]),([53,11,0,1,2,3,4,5],[12,5],[0]),([54,15,0,1,2,3,4,5],[6,150],[0]),([55,15,0,1,2,3,4,5],[12],[0]),([0,9,1,2,3,7],[12,25,23],[]),([56,0,1,2,3,4,5],[9,4,151,24,22,18],[0]),([0,1,2,3,57,7],[11,4,23,25],[0]),([0,1,2,58,3,4,7],[11,4,5,152,25,23],[]),([0,59,1,2,3,4,5],[5,153,0,20,26],[0]),([0,1,2,3,60,4,5],[4,5,21,19,24,22],[0]),([15,0,9,1,2,3,5],[9,23,4,0,144],[0]),([0,1,2,61,3,4,5],[4,155,21,6,24,22,154],[0]),([22,0,1,2,3,21,4,5],[26,5,25,46,20],[0]),([62,0,1,2,3,4,5],[44,4,93,11],[0]),([63,0,1,2,3,5],[12,65,25],[0]),([0,1,2,3,40,4,5],[156,20,157,18,26,24],[0]),([0,1,2,3,31,21,4,5],[5,21,19,0,158],[0]),([20,0,1,2,3,4,7],[12,5,159,23,25],[]),([11,33,0,1,2,3,5],[12,49,0,23],[0]),([64,0,1,2,3,21,4,5],[37,44,26],[]),([15,20,0,1,2,3,4,5],[6,12,19],[0]),([20,33,0,1,2,3,5],[44,9,160,11,23],[0]),([11,8,0,1,2,4,5],[0,136,5,9],[0]),([23,0,1,2,3,21,4,5],[23,21,0,126,161],[0]),([23,27,0,1,2,3,4],[12,5,23,25,162],[]),([0,1,2,3,31,4,5],[11,9,5,19,24,22],[0]),([11,0,1,2,3,31,4,5],[9,5,11,4],[0]),([65,0,1,2,3,4],[11,4,163,44,73],[0]),([0,12,1,2,21,4,5],[0,142,9,5],[0]),([66,0,1,2,3,4,5],[164,165,18,26,20,6,21],[0]),([33,0,1,2,3,7],[12,23,25],[]),([8,0,1,2,31,4,5],[0,164,5,9],[0]),([0,1,2,31,21,4,5],[164,9,166,6,11],[0]),([0,1,19,2,3,21,4,5],[20,23,5,126,167,168],[0]),([67,0,1,2,29,3,4,5],[169,6],[0]),([0,9,1,2,3,31,5],[12,108,0,23],[0]),([53,0,1,2,3,31,4,5],[12,5],[0]),([0,1,2,3,68,4,5],[44,11,34,4],[0]),([0,1,2,29,3,40,4,5],[157,9,6,170,23,71,11],[0]),([0,69,1,2,3,4,5],[12,171,89],[0]),([0,69,1,2,3,31,4,5],[12],[0]),([0,70,1,2,3,4,5],[12,173,172,6,18],[0]),([27,0,1,2,3,31,4],[44,12,164,108],[0]),([15,0,1,2,3,31,4,5],[12,6,19,55],[0]),([33,0,1,2,3,31,5],[11,108,9,0,23],[0]),([0,1,2,71,3,4,5],[0,159,20,18,26,24],[0]),([11,0,1,2,72,3,4,5],[136,4,5],[0]),([0,12,2,10,4,5],[9,0,5],[0]),([25,1,2,31,4,5],[9,11,0,5,87],[0]),([0,1,2,3,31,4,7],[12,164,5,23,25],[0]),([0,1,2,73,3,4,5],[9,5,0,11],[]),([20,0,1,2,29,3,4,5],[19,11,6],[0]),([74,0,1,2,3,4,5],[12,5,19,24,22],[0]),([65,0,1,2,3,31,4],[12,5,163,73],[0]),([0,1,2,72,3,4,5],[136,174,18,26,21,6,20],[0]),([0,1,73,3,4,5],[9,5,0,11],[]),([23,20,1,2,4,5],[9,5,0,11],[0]),([27,30,0,1,2,3,4],[12,175,176,25,23,5],[0]),([75,0,2,3,4,5],[9,5,0,11],[]),([0,1,2,3,76,4,5],[9,11,177,24,22,18],[0]),([8,30,0,1,2,3,4,5],[6,9,178,23,176],[0]),([77,0,1,2,29,3,4,5],[179,21,6],[0]),([55,0,1,2,3,4,5],[12,176,6,24,22],[0]),([77,0,1,2,3,4,5],[179,180,95,20,26,6],[0]),([0,1,2,3,21,4,5,78],[44,37,26],[0]),([0,12,9,1,2,3,5],[44,9,181,4,23],[0]),([79,0,1,3,4,5],[9,4,86],[0]),([0,1,2,80,29,3,4,5],[182,11,23,170,71,6],[0]),([0,1,2,3,4,81],[4,0,21,5],[]),([27,32,0,1,2,3,4],[11,4,23,25,183,184,5],[0]),([32,0,1,2,3,21,4,5],[20,23,6,126,185,186],[0]),([11,0,1,2,29,3,4,5],[12,19,71,6],[0]),([20,0,1,2,21,4,5],[0,159,9,5],[0]),([0,12,1,2,29,3,4,5],[12,6,19],[0]),([0,1,82,2,4,5],[9,5,0,4],[]),([27,14,0,1,2,3,4],[12,5,23,25,187,188],[0]),([0,1,2,29,3,31,4,5],[164,11,6,71],[0]),([33,0,12,1,2,3,5],[44,12,181,23],[0]),([83,0,1,2,3,4,5],[11,4,5,24,22],[0]),([0,1,29,3,4,7],[12,23],[0]),([11,30,0,2,3,4,5],[12,6],[0]),([8,0,9,1,2,3,5],[0,23,178,9,4,25],[0]),([14,19,2,3,4,5],[11,20,189,80],[0]),([33,0,1,2,3,21,5],[23,126,9,0,25,11],[0]),([15,30,0,2,3,4,5],[12,176],[0]),([8,32,0,1,2,3,4,5],[6,21,23,178,184],[0]),([11,27,0,1,2,3,4],[44,12,136,49],[0]),([11,0,1,2,3,4,7],[12,136,5,23,25],[0]),([0,1,2,3,84,31,4],[44,12,108,74],[0]),([85,0,1,2,4,5],[9,4,103,97],[0]),([8,14,0,1,2,3,4,5],[5,23,21,188,178],[0]),([15,0,1,3,21,4,5],[23,9,6,4],[0]),([85,0,1,2,3,4,5],[9,4,103,97],[0]),([79,0,1,2,3,4,5],[4,9,86,190,6,18],[0]),([15,0,12,1,2,3,4,5],[6,4,19],[0]),([86,0,1,2,3,4],[11,20,115,121],[0]),([15,33,0,1,2,3,5],[12,144,23,0],[0]),([0,9,1,2,29,3,5],[12,170,23,0],[0]),([0,70,1,2,29,3,4,5],[12,71],[0]),([0,1,2,3,87,4,5],[9,11,106,75],[0]),([88,0,1,2,4,5],[9,5,0,11],[]),([30,0,1,2,3,21,4,5],[9,23,6,126,191,192],[0]),([89,0,1,2,3,4,5],[4,11,193,6,24,22],[0]),([11,0,19,2,3,4,5],[4,9,6],[0]),([15,0,19,2,3,4,5],[9,4,190],[0]),([0,1,29,3,21,4,5],[23,9,6,11],[0]),([90,0,1,2,3,4,5],[11,194,20,6,24,22,195],[0]),([20,0,9,1,2,3,5],[44,12,160,23],[0]),([0,1,2,3,10,21,4,5],[23,20,0,126,196],[0]),([33,0,1,2,29,3,5],[23,9,11,0,170],[0]),([0,1,2,3,91,4,5],[11,20,19,24,22,18],[0]),([14,0,1,2,3,21,4,5],[21,23,5,126,20,197,198],[0]),([0,1,2,3,4,92],[11,0,20,5],[]),([8,33,0,1,2,3,5],[0,23,178,9,11,25],[0]),([8,0,1,19,2,3,4,5],[5,20,23,190,178],[0]),([66,0,1,2,3,31,4,5],[164,11,5],[0]),([32,30,2,3,4,5],[9,11,118,67],[0]),([0,1,2,3,31,40,4,5],[164,9,158,0,5,11],[0]),([0,1,2,3,21,93,4,5],[199,20,126],[0]),([0,1,2,3,4,94],[4,21,82,122],[0]),([83,0,1,2,3,4,7],[11,4,200,201,5],[0]),([0,95,2,3,4,5],[11,0,20,5],[]),([55,0,1,2,29,3,4,5],[12],[0]),([17,0,1,2,3,21,4,5],[5,26,23,25,46,126],[0]),([0,1,2,96,3,4,5],[11,20,184,6,24,22],[0]),([0,1,2,87,4,5],[9,11,106,75],[0]),([15,0,97,1,2,3,4,5],[12,19,55],[0]),([0,97,1,2,3,4,5],[12,202,6,24,22,18],[0]),([53,0,1,2,3,4,5],[12,19,24,22,18],[0]),([0,1,2,98,3,4,5],[11,9,99,188,6,18],[0]),([99,0,1,2,3,4,5],[9,4,141,24,22],[0]),([0,1,2,100,3,4,5],[9,11,162,24,22],[0]),([0,1,101,2,3,5],[12,61,25],[0]),([27,0,1,19,2,3,4],[12,203,190,5,25,23],[0]),([0,1,2,3,21,4,5,18],[26,5,25,46],[0]),([0,1,2,102,3,4,5],[0,142,21,18,26,24],[0]),([0,1,98,3,4,5],[9,11,99],[0])]
def P_18_7 : BT (Option BoundPool) := buildPoolsSubBT 8 W_18 R_18 slices_18 ps_18 [0,4,5,6,9,11,12,18,19,20,21,22,23,24,25,26,34,37,40,41,44,46,47,49,52,55,59,61,65,67,71,73,74,75,80,82,86,87,89,93,95,97,99,103,106,108,115,118,121,122,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_7 : checkNodesBT W_18 G_18 fmask_18 P_18_7 autos_18 bk_18_6 7 nodes_18_7 = true := by decide +kernel
def bk_18_7 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_7
set_option maxRecDepth 500000 in
lemma bk_18_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 7 xs.toFinset) bk_18_7 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound slices_18_ok) autos_18_ok bk_18_6_ok chk_18_7
def nodes_18_8 : List NodeSpec := [([0,1,2,3,4,5,6],[11,5,4,25],[]),([0,1,2,3,4,5,7],[11,23,4,18,24,6],[0]),([8,0,1,2,3,4,5],[5,23,21,20],[0]),([0,9,1,2,3,5],[25,9,23],[0]),([0,1,2,3,10,4,5],[9,4,204,0,141,24],[0]),([11,0,1,2,3,4,5],[9,205,5,4,136,18],[0]),([0,12,1,2,3,4,5],[0,5,9,142],[0]),([13,0,1,2,3,4,5],[11,25,4,6,22,19],[0]),([14,0,1,2,3,4,5],[9,11,198,188,19,24,18,6],[0]),([15,0,1,2,3,4,5],[23,9,4,55,6],[0]),([0,1,2,16,3,4,5],[9,23,4,24,6],[0]),([17,0,1,2,3,4,5],[4,25,21,5,154,22],[0]),([0,1,2,3,4,5,18],[4,25,11,5,206],[0]),([0,1,19,2,3,4,5],[9,4,168,190,19,24,18,6],[0]),([20,0,1,2,3,4,5],[0,5,9,159],[0]),([0,1,2,3,4,7],[23,12,18],[0]),([0,1,2,3,21,4,5],[23,5,21,20,26,24],[0]),([22,0,1,2,3,4,5],[11,25,4,5,207],[0]),([23,0,1,2,3,4,5],[9,11,208,0,162,24],[0]),([24,0,1,2,3,4,5],[9,5,0,19,4,22,24,18],[0]),([25,0,1,2,3,4,5],[9,5,0,19,11,22,24,18],[0]),([26,0,1,2,3,4,5],[9,23,11,24,6],[0]),([27,0,1,2,3,4],[23,25,5],[0]),([0,1,2,3,4,5,28],[11,25,20,5,195,22],[0]),([0,1,2,29,3,4,5],[23,12,71,6],[0]),([30,0,1,2,3,4,5],[12,192,176,24,6],[0]),([0,1,2,3,31,4,5],[9,209,5,11,164,18],[0]),([32,0,1,2,3,4,5],[11,20,186,184,24,6],[0]),([33,0,1,2,3,5],[25,9,23],[0])]
def P_18_8 : BT (Option BoundPool) := buildPoolsSubBT 8 W_18 R_18 slices_18 ps_18 [0,4,5,6,9,11,12,18,19,20,21,22,23,24,25,26,55,71,136,141,142,154,159,162,164,168,176,184,186,188,190,192,195,198,204,205,206,207,208,209]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_8 : checkNodesBT W_18 G_18 fmask_18 P_18_8 autos_18 bk_18_7 8 nodes_18_8 = true := by decide +kernel
def bk_18_8 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_8
set_option maxRecDepth 500000 in
lemma bk_18_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 8 xs.toFinset) bk_18_8 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound slices_18_ok) autos_18_ok bk_18_7_ok chk_18_8
def nodes_18_9 : List NodeSpec := [([0,1,2,3,4,5],[22,19,18],[0])]
def P_18_9 : BT (Option BoundPool) := buildPoolsSubBT 8 W_18 R_18 slices_18 ps_18 [18,19,22]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_9 : checkNodesBT W_18 G_18 fmask_18 P_18_9 autos_18 bk_18_8 9 nodes_18_9 = true := by decide +kernel
def bk_18_9 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_9
set_option maxRecDepth 500000 in
lemma bk_18_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 9 xs.toFinset) bk_18_9 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound slices_18_ok) autos_18_ok bk_18_8_ok chk_18_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck R_18 G_18 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,9,1),(VAR 4,22,6),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT bk_18_9 R_18 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_18 : Lower R_18 G_18 10 := lower_of_forestBT root_18_ok bk_18_9_ok root_18_in
def wit : List PEqualNP.CircuitLowerBounds.Gate := [
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 11]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 14]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 15]⟩
]
def wo : Nat := 16
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by intro g hg; simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4008372906 * 2 ^ 32 + 3941132968) ||| ((4008372906 * 2 ^ 32 + 3941132968) <<< 64)).testBit r.val := by decide +kernel
lemma root_eq : G_18 = ((4008372906 * 2 ^ 32 + 3941132968) ||| ((4008372906 * 2 ^ 32 + 3941132968) <<< 64)) := by decide
lemma low_root : Lower (varsOf 63) ((4008372906 * 2 ^ 32 + 3941132968) ||| ((4008372906 * 2 ^ 32 + 3941132968) <<< 64)) 10 := root_eq ▸ low_18
end PEqualNP.Outside.L_meta_16395
theorem PEqualNP.Outside.L_meta_16395 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3941132968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3941132968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_16395.table2_of_lower (4008372906 * 2 ^ 32 + 3941132968) (by decide) (by decide) (by decide) (by decide) 10 PEqualNP.Outside.L_meta_16395.low_root PEqualNP.Outside.L_meta_16395.wit PEqualNP.Outside.L_meta_16395.wo (by decide) PEqualNP.Outside.L_meta_16395.wit_mono PEqualNP.Outside.L_meta_16395.wit_eval s hcs
