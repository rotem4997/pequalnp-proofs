import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_12138
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
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in
def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(2,5),(1,4),(0,3)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0
def G_2 : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
def R_2 : List Nat := varsOf 11
lemma low_2_ok : carryOK [(2,5),(0,2),(1,4),(0,3)] R_2 G_2 R_0 G_0 = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 4 := carry_of low_2_ok low_0
def G_3 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def R_3 : List Nat := varsOf 13
lemma low_3_ok : carryOK [(1,2),(1,5),(2,4),(0,1),(0,3)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0
def G_4 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_4 : List Nat := varsOf 14
lemma low_4_ok : carryOK [(1,2),(1,5),(2,4),(1,3)] R_4 G_4 R_0 G_0 = true := by decide +kernel
lemma low_4 : Lower R_4 G_4 4 := carry_of low_4_ok low_0
def G_5 : Nat := 0xe8e8e8e800000000e8e8e8e800000000
def R_5 : List Nat := varsOf 39
lemma low_5_ok : liftCheck 0 32 R_5 G_5 R_1 G_1 [(VAR 5,35,3)] = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 5 := lift_of low_5_ok low_1
def G_6 : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def R_6 : List Nat := varsOf 15
def pos_6 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12,3,3,5,5,6,6,9,9,10,10,12,12]
def neg_6 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4,4,8,2,8,1,8,2,4,1,4,1,2]
def fmask_6 : Nat := fullMask 24
def base_6 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc0fc0,0x2a540)]
def steps_6 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_6 : BT Decor := buildWiresBT 4 base_6 steps_6
def autosL_6 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(2,3),(0,1)],[(1,2)],[(1,3),(1,2)],[(0,1),(0,2)],[(1,3),(0,1),(0,2)],[(1,3),(0,2)]]
def autos_6 : BT (List (Nat × Nat)) := btOfList 4 autosL_6
def slicesL_6 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 1 0,4),some (subcubeFast 8 0,4),some (subcubeFast 4 0,4)]
def slices_6 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_6
def ps_6 : BT (Option PoolSpec) := btOfList 2 [some (0,[]),some (1,[]),some (2,[]),some (3,[])]
lemma gp_6 : goodPairs G_6 pos_6 neg_6 := goodPairs_of (by decide +kernel)
lemma base_6_ok : ∀ x ∈ base_6, faithful pos_6 neg_6 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_6_ok : btAll (fun x => faithful pos_6 neg_6 x ∧ x.1 < 2^128) W_6 := buildWiresBT_faithful base_6_ok
set_option maxRecDepth 500000 in
lemma autos_6_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_6 = G_6) autos_6 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_6_0_ok : sliceDirectCheck 2 0 0 R_6 G_6 R_3 G_3 = true := by decide +kernel
lemma sl_6_0 : Slice R_6 G_6 (subcubeFast 2 0) 4 := slice_fast_direct sl_6_0_ok low_3
lemma sl_6_1_ok : sliceDirectCheck 1 0 0 R_6 G_6 R_4 G_4 = true := by decide +kernel
lemma sl_6_1 : Slice R_6 G_6 (subcubeFast 1 0) 4 := slice_fast_direct sl_6_1_ok low_4
lemma sl_6_2_ok : sliceDirectCheck 8 0 0 R_6 G_6 R_1 G_1 = true := by decide +kernel
lemma sl_6_2 : Slice R_6 G_6 (subcubeFast 8 0) 4 := slice_fast_direct sl_6_2_ok low_1
lemma sl_6_3_ok : sliceDirectCheck 4 0 0 R_6 G_6 R_2 G_2 = true := by decide +kernel
lemma sl_6_3 : Slice R_6 G_6 (subcubeFast 4 0) 4 := slice_fast_direct sl_6_3_ok low_2
set_option maxRecDepth 500000 in
lemma slices_6_ok : btAll (fun o => ∀ p, o = some p → Slice R_6 G_6 p.1 p.2) slices_6 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_6 G_6 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_6_0) (forall_cons (fun _ h => by cases h; exact sl_6_1) (forall_cons (fun _ h => by cases h; exact sl_6_2) (forall_cons (fun _ h => by cases h; exact sl_6_3) (fun _ h => (List.not_mem_nil h).elim)))))
def bk_6_init : BT (List (List Nat)) := BT.empty
lemma bk_6_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 (0 - 1) xs.toFinset) bk_6_init := trivial
def nodes_6_0 : List NodeSpec := []
def P_6_0 : BT (Option BoundPool) := buildPoolsSubBT 2 W_6 R_6 slices_6 ps_6 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_0 : checkNodesBT W_6 G_6 fmask_6 P_6_0 autos_6 bk_6_init 0 nodes_6_0 = true := by decide +kernel
def bk_6_0 : BT (List (List Nat)) := buildBucketsBT W_6 nodes_6_0
set_option maxRecDepth 500000 in
lemma bk_6_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 0 xs.toFinset) bk_6_0 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound slices_6_ok) autos_6_ok bk_6_init_ok chk_6_0
def nodes_6_1 : List NodeSpec := []
def P_6_1 : BT (Option BoundPool) := buildPoolsSubBT 2 W_6 R_6 slices_6 ps_6 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_1 : checkNodesBT W_6 G_6 fmask_6 P_6_1 autos_6 bk_6_0 1 nodes_6_1 = true := by decide +kernel
def bk_6_1 : BT (List (List Nat)) := buildBucketsBT W_6 nodes_6_1
set_option maxRecDepth 500000 in
lemma bk_6_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 1 xs.toFinset) bk_6_1 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound slices_6_ok) autos_6_ok bk_6_0_ok chk_6_1
def nodes_6_2 : List NodeSpec := []
def P_6_2 : BT (Option BoundPool) := buildPoolsSubBT 2 W_6 R_6 slices_6 ps_6 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_2 : checkNodesBT W_6 G_6 fmask_6 P_6_2 autos_6 bk_6_1 2 nodes_6_2 = true := by decide +kernel
def bk_6_2 : BT (List (List Nat)) := buildBucketsBT W_6 nodes_6_2
set_option maxRecDepth 500000 in
lemma bk_6_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 2 xs.toFinset) bk_6_2 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound slices_6_ok) autos_6_ok bk_6_1_ok chk_6_2
def nodes_6_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
def P_6_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_6 R_6 slices_6 ps_6 [0,1]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_3 : checkNodesBT W_6 G_6 fmask_6 P_6_3 autos_6 bk_6_2 3 nodes_6_3 = true := by decide +kernel
def bk_6_3 : BT (List (List Nat)) := buildBucketsBT W_6 nodes_6_3
set_option maxRecDepth 500000 in
lemma bk_6_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 3 xs.toFinset) bk_6_3 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound slices_6_ok) autos_6_ok bk_6_2_ok chk_6_3
def nodes_6_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
def P_6_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_6 R_6 slices_6 ps_6 [0,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_4 : checkNodesBT W_6 G_6 fmask_6 P_6_4 autos_6 bk_6_3 4 nodes_6_4 = true := by decide +kernel
def bk_6_4 : BT (List (List Nat)) := buildBucketsBT W_6 nodes_6_4
set_option maxRecDepth 500000 in
lemma bk_6_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 4 xs.toFinset) bk_6_4 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound slices_6_ok) autos_6_ok bk_6_3_ok chk_6_4
def nodes_6_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
def P_6_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_6 R_6 slices_6 ps_6 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_5 : checkNodesBT W_6 G_6 fmask_6 P_6_5 autos_6 bk_6_4 5 nodes_6_5 = true := by decide +kernel
def bk_6_5 : BT (List (List Nat)) := buildBucketsBT W_6 nodes_6_5
set_option maxRecDepth 500000 in
lemma bk_6_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 5 xs.toFinset) bk_6_5 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound slices_6_ok) autos_6_ok bk_6_4_ok chk_6_5
def nodes_6_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
def P_6_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_6 R_6 slices_6 ps_6 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_6 : checkNodesBT W_6 G_6 fmask_6 P_6_6 autos_6 bk_6_5 6 nodes_6_6 = true := by decide +kernel
def bk_6_6 : BT (List (List Nat)) := buildBucketsBT W_6 nodes_6_6
set_option maxRecDepth 500000 in
lemma bk_6_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_6 6 xs.toFinset) bk_6_6 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound slices_6_ok) autos_6_ok bk_6_5_ok chk_6_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_ok : forestRootCheck R_6 G_6 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,9,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_in : bucketContainsBT bk_6_6 R_6 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_6 : Lower R_6 G_6 7 := lower_of_forestBT root_6_ok bk_6_6_ok root_6_in
def G_7 : Nat := 0xfefefefe80808080fefefefe80808080
def R_7 : List Nat := varsOf 39
def pos_7 : List Nat := [7,7,7,33,33,34,34,35,36,36,37,38,7,33,33,33,34,34,34,36,36,36]
def neg_7 : List Nat := [6,5,3,32,1,32,2,3,32,4,5,6,32,3,5,6,3,5,6,3,5,6]
def fmask_7 : Nat := fullMask 22
def base_7 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf49f,0x1b6496),(0xcccccccccccccccccccccccccccccccc,0x718e7,0x2da8c5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x381f07,0x36ce03),(0xffffffff00000000ffffffff00000000,0x3feff8,0x1128)]
def steps_7 : List (Nat × Nat × Nat) := [(2,0,3),(1,0,3),(3,0,3),(1,0,1),(0,0,3),(2,0,1),(0,0,1),(3,1,5),(3,8,1),(0,1,5),(3,0,1),(1,8,1),(3,9,2),(1,9,2),(3,10,7)]
def W_7 : BT Decor := buildWiresBT 5 base_7 steps_7
def autosL_7 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_7 : BT (List (Nat × Nat)) := btOfList 3 autosL_7
def slicesL_7 : List (Option (Nat × Nat)) := []
def slices_7 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_7
def ps_7 : BT (Option PoolSpec) := btOfList 1 []
lemma gp_7 : goodPairs G_7 pos_7 neg_7 := goodPairs_of (by decide +kernel)
lemma base_7_ok : ∀ x ∈ base_7, faithful pos_7 neg_7 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_7_ok : btAll (fun x => faithful pos_7 neg_7 x ∧ x.1 < 2^128) W_7 := buildWiresBT_faithful base_7_ok
set_option maxRecDepth 500000 in
lemma autos_7_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_7 = G_7) autos_7 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_7_ok : btAll (fun o => ∀ p, o = some p → Slice R_7 G_7 p.1 p.2) slices_7 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_7 G_7 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
def bk_7_init : BT (List (List Nat)) := BT.empty
lemma bk_7_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_7 (0 - 1) xs.toFinset) bk_7_init := trivial
def nodes_7_0 : List NodeSpec := []
def P_7_0 : BT (Option BoundPool) := buildPoolsSubBT 1 W_7 R_7 slices_7 ps_7 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_0 : checkNodesBT W_7 G_7 fmask_7 P_7_0 autos_7 bk_7_init 0 nodes_7_0 = true := by decide +kernel
def bk_7_0 : BT (List (List Nat)) := buildBucketsBT W_7 nodes_7_0
set_option maxRecDepth 500000 in
lemma bk_7_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_7 0 xs.toFinset) bk_7_0 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound slices_7_ok) autos_7_ok bk_7_init_ok chk_7_0
def nodes_7_1 : List NodeSpec := []
def P_7_1 : BT (Option BoundPool) := buildPoolsSubBT 1 W_7 R_7 slices_7 ps_7 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_1 : checkNodesBT W_7 G_7 fmask_7 P_7_1 autos_7 bk_7_0 1 nodes_7_1 = true := by decide +kernel
def bk_7_1 : BT (List (List Nat)) := buildBucketsBT W_7 nodes_7_1
set_option maxRecDepth 500000 in
lemma bk_7_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_7 1 xs.toFinset) bk_7_1 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound slices_7_ok) autos_7_ok bk_7_0_ok chk_7_1
def nodes_7_2 : List NodeSpec := [([18,2,3],[],[])]
def P_7_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_7 R_7 slices_7 ps_7 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_2 : checkNodesBT W_7 G_7 fmask_7 P_7_2 autos_7 bk_7_1 2 nodes_7_2 = true := by decide +kernel
def bk_7_2 : BT (List (List Nat)) := buildBucketsBT W_7 nodes_7_2
set_option maxRecDepth 500000 in
lemma bk_7_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_7 2 xs.toFinset) bk_7_2 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound slices_7_ok) autos_7_ok bk_7_1_ok chk_7_2
def nodes_7_3 : List NodeSpec := [([11,0,2,3],[],[]),([12,0,2,3],[],[]),([0,13,2,3],[],[]),([9,14,2,3],[],[0]),([0,15,2,3],[],[]),([0,1,16,3],[],[]),([0,1,17,3],[],[]),([4,6,1,2],[],[]),([10,7,2,3],[],[0])]
def P_7_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_7 R_7 slices_7 ps_7 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_3 : checkNodesBT W_7 G_7 fmask_7 P_7_3 autos_7 bk_7_2 3 nodes_7_3 = true := by decide +kernel
def bk_7_3 : BT (List (List Nat)) := buildBucketsBT W_7 nodes_7_3
set_option maxRecDepth 500000 in
lemma bk_7_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_7 3 xs.toFinset) bk_7_3 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound slices_7_ok) autos_7_ok bk_7_2_ok chk_7_3
def nodes_7_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([0,1,2,3,5],[],[0,1]),([6,0,1,2,3],[],[0]),([0,1,7,2,3],[],[0]),([8,0,1,2,3],[],[0,1]),([9,0,1,2,3],[],[0]),([10,0,1,2,3],[],[0])]
def P_7_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_7 R_7 slices_7 ps_7 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_4 : checkNodesBT W_7 G_7 fmask_7 P_7_4 autos_7 bk_7_3 4 nodes_7_4 = true := by decide +kernel
def bk_7_4 : BT (List (List Nat)) := buildBucketsBT W_7 nodes_7_4
set_option maxRecDepth 500000 in
lemma bk_7_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_7 4 xs.toFinset) bk_7_4 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound slices_7_ok) autos_7_ok bk_7_3_ok chk_7_4
def nodes_7_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
def P_7_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_7 R_7 slices_7 ps_7 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_5 : checkNodesBT W_7 G_7 fmask_7 P_7_5 autos_7 bk_7_4 5 nodes_7_5 = true := by decide +kernel
def bk_7_5 : BT (List (List Nat)) := buildBucketsBT W_7 nodes_7_5
set_option maxRecDepth 500000 in
lemma bk_7_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_7 5 xs.toFinset) bk_7_5 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound slices_7_ok) autos_7_ok bk_7_4_ok chk_7_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck R_7 G_7 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContainsBT bk_7_5 R_7 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_7 : Lower R_7 G_7 6 := lower_of_forestBT root_7_ok bk_7_5_ok root_7_in
def G_8 : Nat := 0xfff0ff00ff000000fff0ff00ff000000
def R_8 : List Nat := varsOf 60
lemma low_8_ok : liftCheck 0 4 R_8 G_8 R_0 G_0 [(VAR 2,52,48)] = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 5 := lift_of low_8_ok low_0
def G_9 : Nat := 0xffffff00ff00f000ffffff00ff00f000
def R_9 : List Nat := varsOf 60
lemma low_9_ok : liftCheck 4 0 R_9 G_9 R_0 G_0 [(VAR 2,12,8)] = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 5 := lift_of low_9_ok low_0
def G_10 : Nat := 0xe8e80000e8e80000e8e80000e8e80000
def R_10 : List Nat := varsOf 23
lemma low_10_ok : carryOK [(4,5)] R_10 G_10 R_5 G_5 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 5 := carry_of low_10_ok low_5
def G_11 : Nat := 0xee88ee00ee88ee00ee88ee00ee88ee00
def R_11 : List Nat := varsOf 27
lemma low_11_ok : carryOK [(0,2),(1,5),(0,4)] R_11 G_11 R_8 G_8 = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 5 := carry_of low_11_ok low_8
def G_12 : Nat := 0xee88ee88ee00ee00ee88ee88ee00ee00
def R_12 : List Nat := varsOf 43
lemma low_12_ok : carryOK [(1,2),(0,2),(1,5),(0,4)] R_12 G_12 R_8 G_8 = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 5 := carry_of low_12_ok low_8
def G_13 : Nat := 0xfaa0fa00faa0fa00faa0fa00faa0fa00
def R_13 : List Nat := varsOf 29
lemma low_13_ok : carryOK [(1,2),(2,5),(0,1),(0,4)] R_13 G_13 R_8 G_8 = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 5 := carry_of low_13_ok low_8
def G_14 : Nat := 0xfaa0faa0fa00fa00faa0faa0fa00fa00
def R_14 : List Nat := varsOf 45
lemma low_14_ok : carryOK [(2,5),(0,1),(0,4)] R_14 G_14 R_8 G_8 = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 5 := carry_of low_14_ok low_8
def G_15 : Nat := 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00
def R_15 : List Nat := varsOf 30
lemma low_15_ok : carryOK [(1,2),(2,5),(1,4)] R_15 G_15 R_8 G_8 = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 5 := carry_of low_15_ok low_8
def G_16 : Nat := 0xfcc0fcc0fc00fc00fcc0fcc0fc00fc00
def R_16 : List Nat := varsOf 46
lemma low_16_ok : carryOK [(2,5),(1,4)] R_16 G_16 R_8 G_8 = true := by decide +kernel
lemma low_16 : Lower R_16 G_16 5 := carry_of low_16_ok low_8
def G_17 : Nat := 0xfefe8080fefe8080fefe8080fefe8080
def R_17 : List Nat := varsOf 23
lemma low_17_ok : carryOK [(4,5)] R_17 G_17 R_7 G_7 = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 6 := carry_of low_17_ok low_7
def G_18 : Nat := 0xffaaff00ff000000ffaaff00ff000000
def R_18 : List Nat := varsOf 57
lemma low_18_ok : carryOK [(0,1),(0,2)] R_18 G_18 R_8 G_8 = true := by decide +kernel
lemma low_18 : Lower R_18 G_18 5 := carry_of low_18_ok low_8
def G_19 : Nat := 0xffccff00ff000000ffccff00ff000000
def R_19 : List Nat := varsOf 58
lemma low_19_ok : carryOK [(1,2)] R_19 G_19 R_8 G_8 = true := by decide +kernel
lemma low_19 : Lower R_19 G_19 5 := carry_of low_19_ok low_8
def G_20 : Nat := 0xffffff00ff00aa00ffffff00ff00aa00
def R_20 : List Nat := varsOf 57
lemma low_20_ok : carryOK [(0,1),(0,2)] R_20 G_20 R_9 G_9 = true := by decide +kernel
lemma low_20 : Lower R_20 G_20 5 := carry_of low_20_ok low_9
def G_21 : Nat := 0xffffff00ff00cc00ffffff00ff00cc00
def R_21 : List Nat := varsOf 58
lemma low_21_ok : carryOK [(1,2)] R_21 G_21 R_9 G_9 = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 5 := carry_of low_21_ok low_9
def G_22 : Nat := 0xe8e8000000000000e8e8000000000000
def R_22 : List Nat := varsOf 55
lemma low_22_ok : liftCheck 0 16 R_22 G_22 R_5 G_5 [(VAR 4,51,35)] = true := by decide +kernel
lemma low_22 : Lower R_22 G_22 6 := lift_of low_22_ok low_5
def G_23 : Nat := 0xfcc0fc00fc000000fcc0fc00fc000000
def R_23 : List Nat := varsOf 62
def pos_23 : List Nat := [26,26,26,28,28,28,30,30,42,42,42,44,44,44,46,46,54,54,54,54,58,58,60,60,26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54]
def neg_23 : List Nat := [24,18,10,24,20,12,22,14,40,34,10,40,36,12,38,14,52,50,38,22,56,50,56,52,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,56]
def fmask_23 : Nat := fullMask 50
def base_23 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x303f03f3fc7c7,0x13cf3cf2ec6c6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3fc0fc0cff8f8,0x15d75d78df0f0),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffff0ffff,0x386186150adad),(0xffff0000ffff0000ffff0000ffff0000,0x3000fffff00ff,0x2ebaebafb005b),(0xffffffff00000000ffffffff00000000,0x3fff000ffff00,0x2f3cf3cf75b00)]
def steps_23 : List (Nat × Nat × Nat) := [(0,0,3),(2,0,2),(0,0,2),(0,6,3),(3,5,2),(1,5,2),(3,7,3),(0,7,3),(3,6,3),(3,7,1),(0,1,10),(3,13,4),(3,12,1)]
def W_23 : BT Decor := buildWiresBT 5 base_23 steps_23
def autosL_23 : List (List (Nat × Nat)) := [[],[(2,5),(1,4)],[(4,5)],[(1,2)],[(4,5),(1,2)],[(1,2),(2,5),(1,4)]]
def autos_23 : BT (List (Nat × Nat)) := btOfList 3 autosL_23
def slicesL_23 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 6,4),some (subcubeFast 0 4,5),some (subcubeFast 0 2,5),some (subcubeFast 0 32,5),some (subcubeFast 0 48,4)]
def slices_23 : BT (Option (Nat × Nat)) := btOfList 3 slicesL_23
def ps_23 : BT (Option PoolSpec) := btOfList 3 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[])]
lemma gp_23 : goodPairs G_23 pos_23 neg_23 := goodPairs_of (by decide +kernel)
lemma base_23_ok : ∀ x ∈ base_23, faithful pos_23 neg_23 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_23_ok : btAll (fun x => faithful pos_23 neg_23 x ∧ x.1 < 2^128) W_23 := buildWiresBT_faithful base_23_ok
set_option maxRecDepth 500000 in
lemma autos_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_23 = G_23) autos_23 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_23_0_ok : sliceDirectCheck 0 16 0 R_23 G_23 R_16 G_16 = true := by decide +kernel
lemma sl_23_0 : Slice R_23 G_23 (subcubeFast 0 16) 5 := slice_fast_direct sl_23_0_ok low_16
lemma sl_23_1_ok : sliceDirectCheck 0 6 0 R_23 G_23 R_0 G_0 = true := by decide +kernel
lemma sl_23_1 : Slice R_23 G_23 (subcubeFast 0 6) 4 := slice_fast_direct sl_23_1_ok low_0
lemma sl_23_2_ok : sliceDirectCheck 0 4 0 R_23 G_23 R_19 G_19 = true := by decide +kernel
lemma sl_23_2 : Slice R_23 G_23 (subcubeFast 0 4) 5 := slice_fast_direct sl_23_2_ok low_19
lemma sl_23_3_ok : sliceDirectCheck 0 2 0 R_23 G_23 R_8 G_8 = true := by decide +kernel
lemma sl_23_3 : Slice R_23 G_23 (subcubeFast 0 2) 5 := slice_fast_direct sl_23_3_ok low_8
lemma sl_23_4_ok : sliceDirectCheck 0 32 0 R_23 G_23 R_15 G_15 = true := by decide +kernel
lemma sl_23_4 : Slice R_23 G_23 (subcubeFast 0 32) 5 := slice_fast_direct sl_23_4_ok low_15
lemma sl_23_5_ok : sliceDirectCheck 0 48 0 R_23 G_23 R_4 G_4 = true := by decide +kernel
lemma sl_23_5 : Slice R_23 G_23 (subcubeFast 0 48) 4 := slice_fast_direct sl_23_5_ok low_4
set_option maxRecDepth 500000 in
lemma slices_23_ok : btAll (fun o => ∀ p, o = some p → Slice R_23 G_23 p.1 p.2) slices_23 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_23 G_23 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (forall_cons (fun _ h => by cases h; exact sl_23_4) (forall_cons (fun _ h => by cases h; exact sl_23_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def bk_23_init : BT (List (List Nat)) := BT.empty
lemma bk_23_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 (0 - 1) xs.toFinset) bk_23_init := trivial
def nodes_23_0 : List NodeSpec := []
def P_23_0 : BT (Option BoundPool) := buildPoolsSubBT 3 W_23 R_23 slices_23 ps_23 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_0 : checkNodesBT W_23 G_23 fmask_23 P_23_0 autos_23 bk_23_init 0 nodes_23_0 = true := by decide +kernel
def bk_23_0 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_0
set_option maxRecDepth 500000 in
lemma bk_23_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 0 xs.toFinset) bk_23_0 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound slices_23_ok) autos_23_ok bk_23_init_ok chk_23_0
def nodes_23_1 : List NodeSpec := []
def P_23_1 : BT (Option BoundPool) := buildPoolsSubBT 3 W_23 R_23 slices_23 ps_23 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_1 : checkNodesBT W_23 G_23 fmask_23 P_23_1 autos_23 bk_23_0 1 nodes_23_1 = true := by decide +kernel
def bk_23_1 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_1
set_option maxRecDepth 500000 in
lemma bk_23_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 1 xs.toFinset) bk_23_1 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound slices_23_ok) autos_23_ok bk_23_0_ok chk_23_1
def nodes_23_2 : List NodeSpec := []
def P_23_2 : BT (Option BoundPool) := buildPoolsSubBT 3 W_23 R_23 slices_23 ps_23 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_2 : checkNodesBT W_23 G_23 fmask_23 P_23_2 autos_23 bk_23_1 2 nodes_23_2 = true := by decide +kernel
def bk_23_2 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_2
set_option maxRecDepth 500000 in
lemma bk_23_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 2 xs.toFinset) bk_23_2 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound slices_23_ok) autos_23_ok bk_23_1_ok chk_23_2
def nodes_23_3 : List NodeSpec := []
def P_23_3 : BT (Option BoundPool) := buildPoolsSubBT 3 W_23 R_23 slices_23 ps_23 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_3 : checkNodesBT W_23 G_23 fmask_23 P_23_3 autos_23 bk_23_2 3 nodes_23_3 = true := by decide +kernel
def bk_23_3 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_3
set_option maxRecDepth 500000 in
lemma bk_23_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 3 xs.toFinset) bk_23_3 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound slices_23_ok) autos_23_ok bk_23_2_ok chk_23_3
def nodes_23_4 : List NodeSpec := [([0,15,2,3,4],[],[]),([16,0,1,2,3],[],[]),([17,0,2,3,4],[],[])]
def P_23_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_23 R_23 slices_23 ps_23 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_4 : checkNodesBT W_23 G_23 fmask_23 P_23_4 autos_23 bk_23_3 4 nodes_23_4 = true := by decide +kernel
def bk_23_4 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_4
set_option maxRecDepth 500000 in
lemma bk_23_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 4 xs.toFinset) bk_23_4 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound slices_23_ok) autos_23_ok bk_23_3_ok chk_23_4
def nodes_23_5 : List NodeSpec := [([8,0,1,2,3,4],[],[]),([7,5,1,2,3,4],[0,1],[]),([9,0,1,2,3,4],[],[]),([0,1,2,10,3,4],[0,2,3,4],[0,1]),([11,0,1,2,3,4],[],[]),([12,0,1,2,3,4],[2,4],[0,1]),([0,1,2,13,3,4],[4],[0]),([14,0,2,3,4],[],[]),([14,7,0,2,3,4],[2],[]),([6,7,1,2,3,4],[1],[])]
def P_23_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_23 R_23 slices_23 ps_23 [0,1,2,3,4]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_5 : checkNodesBT W_23 G_23 fmask_23 P_23_5 autos_23 bk_23_4 5 nodes_23_5 = true := by decide +kernel
def bk_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_5
set_option maxRecDepth 500000 in
lemma bk_23_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 5 xs.toFinset) bk_23_5 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound slices_23_ok) autos_23_ok bk_23_4_ok chk_23_5
def nodes_23_6 : List NodeSpec := [([5,0,1,2,3,4],[1,5],[0,1]),([6,0,1,2,3,4],[1,0,4],[0,2]),([7,0,1,2,3,4],[1,0,4],[0,2])]
def P_23_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_23 R_23 slices_23 ps_23 [0,1,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_6 : checkNodesBT W_23 G_23 fmask_23 P_23_6 autos_23 bk_23_5 6 nodes_23_6 = true := by decide +kernel
def bk_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_6
set_option maxRecDepth 500000 in
lemma bk_23_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 6 xs.toFinset) bk_23_6 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound slices_23_ok) autos_23_ok bk_23_5_ok chk_23_6
def nodes_23_7 : List NodeSpec := [([0,1,2,3,4],[1,5],[0,2,3,4,1,5])]
def P_23_7 : BT (Option BoundPool) := buildPoolsSubBT 3 W_23 R_23 slices_23 ps_23 [1,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_7 : checkNodesBT W_23 G_23 fmask_23 P_23_7 autos_23 bk_23_6 7 nodes_23_7 = true := by decide +kernel
def bk_23_7 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_7
set_option maxRecDepth 500000 in
lemma bk_23_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 7 xs.toFinset) bk_23_7 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound slices_23_ok) autos_23_ok bk_23_6_ok chk_23_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck R_23 G_23 [(VAR 1,26,24),(VAR 2,28,24),(VAR 3,26,18),(VAR 4,26,10),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT bk_23_7 R_23 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_23 : Lower R_23 G_23 8 := lower_of_forestBT root_23_ok bk_23_7_ok root_23_in
def G_24 : Nat := 0xfe00fe0080008000fe00fe0080008000
def R_24 : List Nat := varsOf 47
lemma low_24_ok : liftCheck 0 8 R_24 G_24 R_7 G_7 [(VAR 3,15,7)] = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 7 := lift_of low_24_ok low_7
def G_25 : Nat := 0xfee8fee8fe00fe00fee8fee8fe00fe00
def R_25 : List Nat := varsOf 47
lemma low_25_ok : liftCheck 0 32 R_25 G_25 R_6 G_6 [(VAR 5,35,3)] = true := by decide +kernel
lemma low_25 : Lower R_25 G_25 8 := lift_of low_25_ok low_6
def G_26 : Nat := 0xfefefefefefe8080fefefefefefe8080
def R_26 : List Nat := varsOf 55
lemma low_26_ok : liftCheck 16 0 R_26 G_26 R_7 G_7 [(VAR 4,17,1)] = true := by decide +kernel
lemma low_26 : Lower R_26 G_26 7 := lift_of low_26_ok low_7
def G_27 : Nat := 0xfffcff00ff00c000fffcff00ff00c000
def R_27 : List Nat := varsOf 62
def pos_27 : List Nat := [14,14,14,24,24,26,26,28,28,30,40,40,42,42,44,44,46,50,50,50,52,52,52,54,54,56,14,14,14,24,24,24,24,24,40,40,40,40,40,50,50,50,50,52,52,52,52]
def neg_27 : List Nat := [12,10,6,16,8,18,10,20,12,22,32,8,34,10,36,12,38,48,34,18,48,36,20,38,22,48,22,38,48,10,12,22,38,48,10,12,22,38,48,10,12,22,38,10,12,22,38]
def fmask_27 : Nat := fullMask 47
def base_27 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x7801d8f3267,0x6eb5ad8d3266),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x78001df1c387,0x7739cde1c385),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x7ffe01ffff,0x198c6000a953),(0xffff0000ffff0000ffff0000ffff0000,0x7f83e3fe03f8,0x2252975a02a8),(0xffffffff00000000ffffffff00000000,0x7ffc03fffc00,0x44631ab75400)]
def steps_27 : List (Nat × Nat × Nat) := [(2,3,4),(1,3,4),(3,2,3),(0,3,4),(2,2,3),(1,2,3),(0,2,3),(3,3,4),(3,5,2),(1,5,2),(3,5,0),(1,5,0),(0,2,6),(2,2,8),(1,2,8),(1,9,4),(0,0,10),(3,10,4),(2,10,4),(0,11,4),(1,10,4),(1,11,4),(0,10,4),(2,9,4),(3,7,4),(2,0,11),(3,11,4),(0,7,4),(3,2,6),(1,7,4),(2,11,4),(1,0,11),(3,9,4),(3,0,10),(3,5,1),(3,8,6),(0,3,26),(1,5,1),(1,9,7),(3,5,10),(3,1,10),(0,1,10),(1,12,11),(1,1,11),(2,1,11),(1,12,2),(3,24,3),(3,40,0),(3,32,6),(1,40,0),(3,12,20),(0,10,26)]
def W_27 : BT Decor := buildWiresBT 6 base_27 steps_27
def autosL_27 : List (List (Nat × Nat)) := [[],[(1,2)],[(4,5)],[(4,5),(1,2)]]
def autos_27 : BT (List (Nat × Nat)) := btOfList 2 autosL_27
def slicesL_27 : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 2 4,4),some (subcubeFast 2 0,5),some (subcubeFast 4 2,4),some (subcubeFast 0 4,5),some (subcubeFast 4 0,5)]
def slices_27 : BT (Option (Nat × Nat)) := btOfList 3 slicesL_27
def ps_27 : BT (Option PoolSpec) := btOfList 3 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[])]
lemma gp_27 : goodPairs G_27 pos_27 neg_27 := goodPairs_of (by decide +kernel)
lemma base_27_ok : ∀ x ∈ base_27, faithful pos_27 neg_27 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_27_ok : btAll (fun x => faithful pos_27 neg_27 x ∧ x.1 < 2^128) W_27 := buildWiresBT_faithful base_27_ok
set_option maxRecDepth 500000 in
lemma autos_27_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_27 = G_27) autos_27 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_27_0_ok : sliceDirectCheck 0 2 0 R_27 G_27 R_9 G_9 = true := by decide +kernel
lemma sl_27_0 : Slice R_27 G_27 (subcubeFast 0 2) 5 := slice_fast_direct sl_27_0_ok low_9
lemma sl_27_1_ok : sliceDirectCheck 2 4 0 R_27 G_27 R_0 G_0 = true := by decide +kernel
lemma sl_27_1 : Slice R_27 G_27 (subcubeFast 2 4) 4 := slice_fast_direct sl_27_1_ok low_0
lemma sl_27_2_ok : sliceDirectCheck 2 0 0 R_27 G_27 R_8 G_8 = true := by decide +kernel
lemma sl_27_2 : Slice R_27 G_27 (subcubeFast 2 0) 5 := slice_fast_direct sl_27_2_ok low_8
lemma sl_27_3_ok : sliceDirectCheck 4 2 0 R_27 G_27 R_0 G_0 = true := by decide +kernel
lemma sl_27_3 : Slice R_27 G_27 (subcubeFast 4 2) 4 := slice_fast_direct sl_27_3_ok low_0
lemma sl_27_4_ok : sliceDirectCheck 0 4 0 R_27 G_27 R_21 G_21 = true := by decide +kernel
lemma sl_27_4 : Slice R_27 G_27 (subcubeFast 0 4) 5 := slice_fast_direct sl_27_4_ok low_21
lemma sl_27_5_ok : sliceDirectCheck 4 0 0 R_27 G_27 R_19 G_19 = true := by decide +kernel
lemma sl_27_5 : Slice R_27 G_27 (subcubeFast 4 0) 5 := slice_fast_direct sl_27_5_ok low_19
set_option maxRecDepth 500000 in
lemma slices_27_ok : btAll (fun o => ∀ p, o = some p → Slice R_27 G_27 p.1 p.2) slices_27 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_27 G_27 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_27_0) (forall_cons (fun _ h => by cases h; exact sl_27_1) (forall_cons (fun _ h => by cases h; exact sl_27_2) (forall_cons (fun _ h => by cases h; exact sl_27_3) (forall_cons (fun _ h => by cases h; exact sl_27_4) (forall_cons (fun _ h => by cases h; exact sl_27_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def bk_27_init : BT (List (List Nat)) := BT.empty
lemma bk_27_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_27 (0 - 1) xs.toFinset) bk_27_init := trivial
def nodes_27_0 : List NodeSpec := []
def P_27_0 : BT (Option BoundPool) := buildPoolsSubBT 3 W_27 R_27 slices_27 ps_27 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_27_0 : checkNodesBT W_27 G_27 fmask_27 P_27_0 autos_27 bk_27_init 0 nodes_27_0 = true := by decide +kernel
def bk_27_0 : BT (List (List Nat)) := buildBucketsBT W_27 nodes_27_0
set_option maxRecDepth 500000 in
lemma bk_27_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_27 0 xs.toFinset) bk_27_0 :=
  buildBucketsBT_sound (by decide) gp_27 W_27_ok (buildPoolsSubBT_sound slices_27_ok) autos_27_ok bk_27_init_ok chk_27_0
def nodes_27_1 : List NodeSpec := []
def P_27_1 : BT (Option BoundPool) := buildPoolsSubBT 3 W_27 R_27 slices_27 ps_27 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_27_1 : checkNodesBT W_27 G_27 fmask_27 P_27_1 autos_27 bk_27_0 1 nodes_27_1 = true := by decide +kernel
def bk_27_1 : BT (List (List Nat)) := buildBucketsBT W_27 nodes_27_1
set_option maxRecDepth 500000 in
lemma bk_27_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_27 1 xs.toFinset) bk_27_1 :=
  buildBucketsBT_sound (by decide) gp_27 W_27_ok (buildPoolsSubBT_sound slices_27_ok) autos_27_ok bk_27_0_ok chk_27_1
def nodes_27_2 : List NodeSpec := []
def P_27_2 : BT (Option BoundPool) := buildPoolsSubBT 3 W_27 R_27 slices_27 ps_27 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_27_2 : checkNodesBT W_27 G_27 fmask_27 P_27_2 autos_27 bk_27_1 2 nodes_27_2 = true := by decide +kernel
def bk_27_2 : BT (List (List Nat)) := buildBucketsBT W_27 nodes_27_2
set_option maxRecDepth 500000 in
lemma bk_27_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_27 2 xs.toFinset) bk_27_2 :=
  buildBucketsBT_sound (by decide) gp_27 W_27_ok (buildPoolsSubBT_sound slices_27_ok) autos_27_ok bk_27_1_ok chk_27_2
def nodes_27_3 : List NodeSpec := [([40,52,1,2],[],[]),([40,0,1,2],[],[]),([40,16,1,2],[],[]),([0,1,2,53],[],[]),([40,54,1,2],[],[]),([0,1,2,55],[],[]),([40,15,1,2],[],[]),([0,1,2,56],[],[])]
def P_27_3 : BT (Option BoundPool) := buildPoolsSubBT 3 W_27 R_27 slices_27 ps_27 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_27_3 : checkNodesBT W_27 G_27 fmask_27 P_27_3 autos_27 bk_27_2 3 nodes_27_3 = true := by decide +kernel
def bk_27_3 : BT (List (List Nat)) := buildBucketsBT W_27 nodes_27_3
set_option maxRecDepth 500000 in
lemma bk_27_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_27 3 xs.toFinset) bk_27_3 :=
  buildBucketsBT_sound (by decide) gp_27 W_27_ok (buildPoolsSubBT_sound slices_27_ok) autos_27_ok bk_27_2_ok chk_27_3
def nodes_27_4 : List NodeSpec := [([5,12,15,1,2],[],[0]),([15,39,2,3,4],[],[]),([5,12,16,1,2],[],[0]),([40,0,1,2,3],[],[]),([40,0,1,2,6],[],[]),([0,1,2,19,6],[],[0]),([40,0,1,2,8],[],[]),([23,38,1,2,3],[],[]),([0,1,17,2,8],[],[0]),([38,1,2,3,27],[],[]),([5,12,0,1,2],[],[0]),([0,1,11,2,27],[],[0]),([23,0,1,2,3],[],[]),([7,0,1,13,4],[],[]),([5,0,1,2,29],[],[0]),([0,1,2,41,26],[],[]),([16,42,2,3,4],[],[]),([7,43,0,1,4],[],[]),([0,1,2,44,4],[],[]),([40,0,1,2],[],[0,1]),([32,0,1,2,6],[],[0]),([45,38,2,3,4],[],[]),([43,0,1,2,4],[],[]),([5,0,1,2,27],[],[]),([30,31,1,2,3],[],[]),([30,1,2,3,26],[],[]),([0,1,2,3,26],[],[]),([21,46,2,3,4],[],[]),([0,1,2,8,6],[],[0]),([0,1,2,47,4],[],[]),([2,36,48,3,4],[],[]),([9,43,0,1,4],[],[]),([21,1,2,3,27],[],[]),([0,1,2,8,26],[],[]),([9,7,0,1,4],[],[]),([12,0,1,2,26],[],[]),([0,1,2,27,6],[],[]),([7,0,1,2,26],[],[]),([30,49,2,3,4],[],[]),([12,0,1,2,20],[],[0]),([5,40,0,1,2],[],[0,1]),([9,0,1,2,27],[],[]),([9,0,1,50,4],[],[]),([31,1,2,36,3],[],[]),([23,21,1,2,3],[],[]),([51,0,1,2,4],[],[]),([43,0,1,3,4],[],[]),([0,1,2,41,4],[],[]),([0,1,2,10,26],[],[0]),([1,2,36,3,26],[],[]),([28,0,1,2,8],[],[0])]
def P_27_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_27 R_27 slices_27 ps_27 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_27_4 : checkNodesBT W_27 G_27 fmask_27 P_27_4 autos_27 bk_27_3 4 nodes_27_4 = true := by decide +kernel
def bk_27_4 : BT (List (List Nat)) := buildBucketsBT W_27 nodes_27_4
set_option maxRecDepth 500000 in
lemma bk_27_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_27 4 xs.toFinset) bk_27_4 :=
  buildBucketsBT_sound (by decide) gp_27 W_27_ok (buildPoolsSubBT_sound slices_27_ok) autos_27_ok bk_27_3_ok chk_27_4
def nodes_27_5 : List NodeSpec := [([5,12,0,1,2,3],[],[0]),([5,12,0,1,2],[],[0,2,1,3]),([0,1,13,2,3,4],[],[0]),([0,1,2,14,3,4],[],[2,0]),([5,15,1,2,3,4],[0,1],[0]),([5,16,1,2,3,4],[2,3],[0]),([5,0,1,2,3,6],[0],[0]),([0,1,17,2,3,4],[0,2,4,5],[2,0]),([0,1,2,8,3,6],[],[0]),([0,1,2,8,6],[],[0]),([5,0,1,2,3,4],[0,2,4,5],[0]),([5,0,1,2,8,4],[0],[0]),([18,0,1,2,3,4],[],[]),([0,1,2,3,19,4],[2,0,5,4],[0,2]),([9,12,0,1,2,4],[],[2,0]),([12,0,1,11,2,4],[],[0]),([7,0,1,2,4,6],[],[0]),([9,0,1,2,8,4],[],[0]),([5,0,1,2,10,4],[],[0]),([9,7,0,1,4],[],[0]),([0,1,2,8,3,4],[],[0]),([0,1,2,3,4,20],[2,0,5,4],[0,2]),([21,1,2,3,10,4],[0,1],[0]),([0,1,2,3,10,4],[2,0,5,4],[2,0]),([5,7,0,1,2,4],[],[0]),([0,1,11,2,3,4],[0,2,4,5],[0,2]),([22,0,1,2,3,4],[0,2,4,5],[2]),([23,0,1,2,3,10],[],[2,0,1]),([23,0,1,2,3],[],[]),([0,1,24,2,3,4],[0,2,4,5],[0,2]),([0,1,2,3,4,25],[2,0,5,4],[2,0]),([0,1,11,2,3,26],[],[0,1,2]),([0,1,2,3,27,4],[],[2,0]),([0,1,11,3,10,4],[],[0]),([28,0,1,2,3,4],[],[0]),([9,7,0,1,2,4],[],[0]),([0,1,2,3,27],[],[0,2]),([0,1,2,3,26],[],[0]),([0,1,11,2,10,4],[],[0]),([0,1,2,29,3,4],[0,2,4,5],[0]),([9,7,0,1,3,4],[],[0]),([9,0,1,2,10,4],[0],[0]),([30,1,11,2,3,4],[0,1],[0]),([31,0,1,2,3,4],[],[]),([0,1,2,10,4,6],[],[0,2]),([32,0,1,2,3,4],[],[0]),([31,0,1,11,2,3],[],[0,1]),([33,0,1,2,3,4],[],[]),([0,1,2,3,4,34],[],[]),([0,1,11,2,8,4],[],[0]),([35,0,1,2,3,4],[0,2,4,5],[0]),([1,11,2,36,3,4],[3,2],[0]),([7,0,1,2,3,4],[],[0]),([31,0,1,2,3],[],[]),([0,1,2,3,27,10],[],[0,1]),([7,0,1,3,10,4],[0],[0]),([7,0,1,11,2,4],[0],[0]),([0,1,2,3,4,6],[],[0]),([0,1,2,3,37,4],[],[]),([9,0,1,11,3,4],[0],[0]),([38,1,2,3,10,4],[2,3],[0]),([23,0,1,2,3,4],[],[]),([9,0,1,2,3,4],[],[0]),([0,1,2,3,4,26],[],[0])]
def P_27_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_27 R_27 slices_27 ps_27 [0,1,2,3,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_27_5 : checkNodesBT W_27 G_27 fmask_27 P_27_5 autos_27 bk_27_4 5 nodes_27_5 = true := by decide +kernel
def bk_27_5 : BT (List (List Nat)) := buildBucketsBT W_27 nodes_27_5
set_option maxRecDepth 500000 in
lemma bk_27_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_27 5 xs.toFinset) bk_27_5 :=
  buildBucketsBT_sound (by decide) gp_27 W_27_ok (buildPoolsSubBT_sound slices_27_ok) autos_27_ok bk_27_4_ok chk_27_5
def nodes_27_6 : List NodeSpec := [([5,0,1,2,3,4],[2,0,5,4],[0,1,2]),([0,1,2,3,4,6],[2,0,5,4],[0,2]),([7,0,1,2,3,4],[2,0,5,4],[0,2]),([0,1,2,8,3,4],[2,0,5,4],[0,2]),([9,0,1,2,3,4],[2,0,5,4],[0,2]),([0,1,2,3,10,4],[2,0,5,4],[0,1]),([0,1,11,2,3,4],[2,0,5,4],[0,1])]
def P_27_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_27 R_27 slices_27 ps_27 [0,2,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_27_6 : checkNodesBT W_27 G_27 fmask_27 P_27_6 autos_27 bk_27_5 6 nodes_27_6 = true := by decide +kernel
def bk_27_6 : BT (List (List Nat)) := buildBucketsBT W_27 nodes_27_6
set_option maxRecDepth 500000 in
lemma bk_27_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_27 6 xs.toFinset) bk_27_6 :=
  buildBucketsBT_sound (by decide) gp_27 W_27_ok (buildPoolsSubBT_sound slices_27_ok) autos_27_ok bk_27_5_ok chk_27_6
def nodes_27_7 : List NodeSpec := [([0,1,2,3,4],[5,4,0,2],[0,2])]
def P_27_7 : BT (Option BoundPool) := buildPoolsSubBT 3 W_27 R_27 slices_27 ps_27 [0,2,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_27_7 : checkNodesBT W_27 G_27 fmask_27 P_27_7 autos_27 bk_27_6 7 nodes_27_7 = true := by decide +kernel
def bk_27_7 : BT (List (List Nat)) := buildBucketsBT W_27 nodes_27_7
set_option maxRecDepth 500000 in
lemma bk_27_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_27 7 xs.toFinset) bk_27_7 :=
  buildBucketsBT_sound (by decide) gp_27 W_27_ok (buildPoolsSubBT_sound slices_27_ok) autos_27_ok bk_27_6_ok chk_27_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_27_ok : forestRootCheck R_27 G_27 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_27_in : bucketContainsBT bk_27_7 R_27 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_27 : Lower R_27 G_27 8 := lower_of_forestBT root_27_ok bk_27_7_ok root_27_in
def G_28 : Nat := 0xee88ee00ee000000ee88ee00ee000000
def R_28 : List Nat := varsOf 59
lemma low_28_ok : carryOK [(0,2),(0,1)] R_28 G_28 R_23 G_23 = true := by decide +kernel
lemma low_28 : Lower R_28 G_28 8 := carry_of low_28_ok low_23
def G_29 : Nat := 0xfaa0fa00fa000000faa0fa00fa000000
def R_29 : List Nat := varsOf 61
lemma low_29_ok : carryOK [(0,1)] R_29 G_29 R_23 G_23 = true := by decide +kernel
lemma low_29 : Lower R_29 G_29 8 := carry_of low_29_ok low_23
def G_30 : Nat := 0xfe008000fe008000fe008000fe008000
def R_30 : List Nat := varsOf 31
lemma low_30_ok : carryOK [(4,5)] R_30 G_30 R_24 G_24 = true := by decide +kernel
lemma low_30 : Lower R_30 G_30 7 := carry_of low_30_ok low_24
def G_31 : Nat := 0xfee8fe00fee8fe00fee8fe00fee8fe00
def R_31 : List Nat := varsOf 31
lemma low_31_ok : carryOK [(4,5)] R_31 G_31 R_25 G_25 = true := by decide +kernel
lemma low_31 : Lower R_31 G_31 8 := carry_of low_31_ok low_25
def G_32 : Nat := 0xffeeff00ff008800ffeeff00ff008800
def R_32 : List Nat := varsOf 59
lemma low_32_ok : carryOK [(0,2),(0,1)] R_32 G_32 R_27 G_27 = true := by decide +kernel
lemma low_32 : Lower R_32 G_32 8 := carry_of low_32_ok low_27
def G_33 : Nat := 0xfffaff00ff00a000fffaff00ff00a000
def R_33 : List Nat := varsOf 61
lemma low_33_ok : carryOK [(0,1)] R_33 G_33 R_27 G_27 = true := by decide +kernel
lemma low_33 : Lower R_33 G_33 8 := carry_of low_33_ok low_27
def G_34 : Nat := 0xfee8fe00fe008000fee8fe00fe008000
def R_34 : List Nat := varsOf 63
def pos_34 : List Nat := [15,15,15,15,25,25,25,26,26,26,27,27,28,28,28,29,29,30,30,31,41,41,41,42,42,42,43,43,44,44,44,45,45,46,46,47,51,51,51,51,53,53,53,53,54,54,54,54,55,55,57,57,58,58,60,60,15,15,15,15,15,15,25,25,25,25,25,25,25,25,25,26,26,26,26,26,26,26,26,26,28,28,28,28,28,28,28,28,28,41,41,41,41,41,41,41,41,41,42,42,42,42,42,42,42,42,42,44,44,44,44,44,44,44,44,44,51,51,51,51,51,51,51,53,53,53,53,53]
def neg_34 : List Nat := [14,13,11,7,24,17,9,24,18,10,19,11,24,20,12,21,13,22,14,23,40,33,9,40,34,10,35,11,40,36,12,37,13,38,14,39,50,49,35,19,52,49,37,21,52,50,38,22,39,23,56,49,56,50,56,52,23,39,49,50,52,56,11,13,14,23,39,49,50,52,56,11,13,14,23,39,49,50,52,56,11,13,14,23,39,49,50,52,56,11,13,14,23,39,49,50,52,56,11,13,14,23,39,49,50,52,56,11,13,14,23,39,49,50,52,56,11,13,14,23,39,52,56,11,13,14,23,39]
def fmask_34 : Nat := fullMask 128
def base_34 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfff00003fe00007fff0f0ff98c798c7f,0xd9b1d8ec763b1d8ec70b0ee98c698c6e),(0xcccccccccccccccccccccccccccccccc,0x7f007fc0000ff803f33f0fe0f8e0f8f,0xe9d2e974ba5d2e974b23e0de0f0e0f0d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf80ff80001ff00003fc3ff0ff00ff00f,0xf3e4f2793c9e4f279383dd0fe00fe00b),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffc000fffffffff,0x3c783c1e0f0783c1e05400055ad55ad7),(0xffff0000ffff0000ffff0000ffff0000,0xfff0000001ffffffc0fffff0000ffff0,0x468f47a3d1e8f47a3dfebbb0000ab5b0),(0xffffffff00000000ffffffff00000000,0xfffffffffe00000000fffffffff00000,0x870f87c3e1f0f87c3efd777ab5b00000)]
def steps_34 : List (Nat × Nat × Nat) := [(2,4,5),(1,4,5),(0,4,5),(3,3,4),(2,3,4),(2,0,4),(0,0,4),(3,0,4),(1,0,1),(3,0,3),(2,0,3),(0,3,4),(0,0,3),(2,0,1),(1,3,4),(1,0,4),(1,0,3),(0,0,1),(3,4,5),(3,3,7),(0,3,7),(1,6,3),(3,9,0),(1,9,0),(3,0,20),(0,0,20),(3,17,5),(2,20,5),(1,17,5),(3,1,5),(3,13,3),(3,11,3),(1,11,3),(3,3,21),(0,3,5),(3,12,3),(1,12,3),(0,20,5),(1,1,4),(3,1,3),(0,22,4),(2,1,4),(3,15,4),(0,2,4),(0,1,4),(3,1,4),(1,1,3),(3,0,1),(0,1,3),(3,2,3),(0,3,21),(3,23,4),(2,2,4),(3,19,4),(2,2,3),(1,2,3),(0,2,3),(0,14,3),(3,2,4),(3,19,3),(3,9,5),(3,13,5),(3,12,5),(1,2,4),(1,19,3),(3,6,3),(2,14,3),(3,16,4),(0,9,5),(2,1,3),(3,23,3),(1,13,3),(2,0,17),(0,1,5),(1,0,17),(0,17,5),(0,14,4),(3,18,4),(1,23,3),(1,0,26),(1,10,9),(1,24,17),(3,81,4),(2,1,40),(1,1,56),(1,12,40),(3,35,3),(1,12,79),(3,58,14),(1,47,16),(3,16,44),(3,47,22),(0,22,44),(1,6,18),(3,1,20),(0,1,20),(3,18,20),(1,51,18),(1,49,3),(3,15,7),(1,47,18),(0,2,5),(1,60,23),(1,15,50),(1,75,18),(1,9,2),(3,18,52),(1,58,3),(3,15,44),(3,18,22),(1,51,15),(3,19,7),(1,55,19),(3,9,2),(2,1,17),(1,9,19),(1,6,15),(2,1,56),(1,35,13),(3,19,20),(1,1,37),(1,19,17),(3,6,14),(2,2,17),(1,2,17),(2,1,37),(1,64,3),(1,47,15),(1,64,19),(3,64,5),(3,49,5),(1,19,49),(1,23,62),(0,2,20),(1,60,19),(0,61,4),(1,58,19),(3,49,3),(2,0,26),(3,19,69),(1,19,62),(1,18,50),(3,64,3),(3,2,5),(3,60,4),(3,9,14),(1,64,23),(3,58,3),(0,14,20),(3,8,7),(0,14,69),(1,23,49),(2,14,17),(1,23,17),(3,55,14),(3,63,2),(3,64,14),(1,6,23),(3,23,7),(2,14,49),(1,1,40),(3,2,20),(1,9,18),(2,14,62),(3,62,4),(3,32,0),(3,16,7),(3,60,14),(0,14,61),(3,18,44),(1,32,0),(0,14,7),(3,23,14),(1,63,2),(3,23,20),(3,19,61),(0,3,69),(1,9,23),(3,23,69),(1,6,19),(3,18,7),(1,13,40),(3,55,4),(3,3,69),(3,23,61),(1,35,12),(1,55,23),(1,58,23),(0,22,7),(3,74,7),(2,0,87),(1,0,87),(3,12,166),(1,1,91),(3,93,2),(0,93,2),(2,1,26),(1,1,26),(2,1,194),(3,147,5),(0,147,2),(1,18,79),(3,1,194),(0,115,1),(1,115,4),(3,115,1),(2,115,1),(1,19,26),(3,19,111),(3,32,2),(3,19,130),(1,64,40),(1,49,40),(3,1,91),(0,93,3),(0,147,5),(0,61,7),(1,6,62),(3,62,7),(1,9,62),(3,62,20),(3,62,61),(2,2,37),(0,14,111),(1,65,49),(1,1,194),(2,128,2),(1,128,2),(2,14,26),(1,177,3),(0,1,194),(2,14,66),(0,177,3),(2,14,119),(1,19,153),(3,154,2),(2,14,81),(1,32,2),(0,14,130),(3,158,5),(0,158,5),(0,154,2),(3,158,2),(2,158,2),(2,0,153),(1,158,2),(0,158,2),(0,14,104),(3,55,7),(2,177,2),(2,14,40),(0,1,91),(1,82,107),(1,23,26),(3,177,2),(1,50,107),(1,129,23),(1,15,79),(3,23,130),(1,23,182),(2,177,3),(1,6,55),(1,115,1),(3,60,7),(2,14,182),(1,23,119),(3,128,2),(1,177,2),(2,14,135),(3,177,3),(3,24,14),(0,178,3),(1,63,49),(0,14,132),(3,76,61),(1,19,119),(0,178,4),(1,129,19),(3,93,3),(3,178,4),(1,154,2),(3,128,3),(0,177,2),(3,23,111),(1,89,12),(0,178,2),(2,14,153),(2,1,91),(2,178,2),(3,178,3),(0,128,3),(2,154,2),(3,129,14),(2,14,141),(1,16,26),(3,147,2),(1,178,3),(2,115,4),(2,178,4),(2,178,3),(0,128,2),(1,178,4),(1,178,2),(3,178,2),(1,0,195),(1,257,2),(0,2,231),(1,236,2),(2,147,107),(1,147,107),(2,268,2),(1,209,2),(3,115,7),(0,115,7),(3,47,115),(3,220,2),(1,19,87),(3,18,261),(1,23,215),(3,2,235),(3,238,4),(3,238,2),(2,273,3),(2,14,87),(2,14,215),(1,158,40),(0,251,5),(3,2,231),(2,178,17),(0,14,217),(2,165,40),(1,55,177),(0,160,7),(0,268,2),(2,1,153),(2,14,222),(1,128,62),(1,177,62),(3,23,243),(2,227,4),(1,227,4),(3,227,14),(0,227,14),(3,177,61),(0,169,20),(3,294,4),(1,23,87),(1,60,177),(0,14,243),(0,108,7),(3,277,4),(0,138,7),(2,0,195),(1,178,17),(3,6,160),(3,19,243),(3,309,3),(1,19,215),(0,173,7),(0,115,44),(3,285,5),(1,294,3),(0,14,225),(0,3,307),(3,115,44),(0,251,3),(1,304,3),(1,9,178),(0,178,20),(1,238,2),(2,157,40),(3,309,4),(1,304,2),(1,55,128),(3,209,2),(1,309,3),(0,169,7),(3,277,2),(3,304,2),(3,9,178),(1,285,3),(3,282,3),(3,282,5),(3,178,20),(3,304,3),(1,47,115),(3,305,4),(0,174,7),(0,302,4),(1,256,49),(3,285,3),(3,257,2),(1,277,2),(1,282,3),(0,273,3),(0,14,218),(3,295,4),(3,6,138),(3,6,169),(3,236,2),(3,294,3),(3,3,307),(0,2,235),(3,257,199),(1,303,211),(3,212,210),(3,303,268),(3,209,210),(3,209,268),(3,288,273),(2,14,195),(3,252,251),(3,345,14),(0,14,346),(1,23,195),(1,23,238),(1,241,23),(3,247,286),(3,23,286),(3,212,7),(3,277,20),(1,385,2),(3,32,178),(1,32,178),(1,309,17),(3,23,235),(3,23,273),(3,385,2),(3,238,235),(1,285,40),(3,209,7),(1,282,40),(1,6,295),(3,277,7),(3,294,20),(3,211,7),(1,6,277),(1,6,309),(3,305,7),(3,309,7),(1,9,309),(1,9,277),(3,295,7),(1,9,294),(0,302,7),(1,19,195),(3,306,233),(0,268,7),(1,23,288),(1,6,294),(1,294,17),(3,291,308),(3,294,7),(3,18,231),(3,236,231),(3,309,20),(3,428,2),(1,428,2),(1,414,4),(2,414,4),(3,457,20)]
def W_34 : BT Decor := buildWiresBT 9 base_34 steps_34
def autosL_34 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(0,1)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)],[(4,5),(1,2)],[(4,5),(0,1)],[(4,5),(0,2),(0,1)]]
def autos_34 : BT (List (Nat × Nat)) := btOfList 4 autosL_34
def slicesL_34 : List (Option (Nat × Nat)) := [some (subcubeFast 16 8,6),some (subcubeFast 4 3,4),some (subcubeFast 2 5,4),some (subcubeFast 1 2,5),some (subcubeFast 2 1,5),some (subcubeFast 32 8,6),some (subcubeFast 1 48,4),some (subcubeFast 8 32,5),some (subcubeFast 0 1,8),some (subcubeFast 1 16,5),some (subcubeFast 0 3,5),some (subcubeFast 0 6,5),some (subcubeFast 4 2,5),some (subcubeFast 0 5,5),some (subcubeFast 16 0,7),some (subcubeFast 1 4,5),some (subcubeFast 0 8,7),some (subcubeFast 2 48,4),some (subcubeFast 1 6,4),some (subcubeFast 32 0,7),some (subcubeFast 8 48,4),some (subcubeFast 0 2,8),some (subcubeFast 4 48,4),some (subcubeFast 0 4,8),some (subcubeFast 2 0,8),some (subcubeFast 2 16,5),some (subcubeFast 1 0,8),some (subcubeFast 4 1,5),some (subcubeFast 0 32,8),some (subcubeFast 0 48,7),some (subcubeFast 4 0,8),some (subcubeFast 0 16,8),some (subcubeFast 4 16,5),some (subcubeFast 1 32,5),some (subcubeFast 2 4,5),some (subcubeFast 8 16,5),some (subcubeFast 2 32,5),some (subcubeFast 8 0,6),some (subcubeFast 4 32,5)]
def slices_34 : BT (Option (Nat × Nat)) := btOfList 6 slicesL_34
def ps_34 : BT (Option PoolSpec) := btOfList 9 [some (0,[(0,0,1),(1,0,1),(3,23,14)]),some (1,[]),some (0,[(1,1,194),(3,2,231)]),some (0,[(1,1,194),(0,2,231)]),some (0,[(1,115,1),(2,268,2)]),some (2,[]),some (3,[]),some (0,[(1,115,1),(0,268,2)]),some (4,[]),some (0,[(0,115,1),(1,115,1),(3,209,268)]),some (5,[(0,115,1),(1,115,1),(3,209,268)]),some (0,[(2,0,1),(3,0,1)]),some (6,[]),some (7,[]),some (8,[(3,3,4),(0,9,5),(1,4,5),(3,74,7)]),some (9,[]),some (0,[(2,1,194),(3,1,194)]),some (10,[]),some (5,[(0,0,1),(1,0,1),(3,23,154)]),some (11,[]),some (8,[(0,4,5),(1,4,5),(3,8,7)]),some (0,[(0,0,1),(1,0,1)]),some (12,[]),some (13,[]),some (14,[(0,0,1),(1,0,1),(3,23,14)]),some (15,[]),some (16,[(0,0,1),(1,0,1),(3,23,14)]),some (0,[(0,115,1),(1,115,1)]),some (0,[(2,115,1),(3,115,1)]),some (17,[]),some (18,[]),some (5,[(0,0,1),(1,0,1),(3,23,14)]),some (16,[(0,0,1),(1,0,1),(3,23,14),(1,4,5)]),some (0,[(1,1,194),(3,18,231)]),some (19,[(0,0,1),(1,0,1),(3,23,14)]),some (20,[]),some (21,[(3,3,4),(0,9,5),(1,4,5),(3,74,7)]),some (22,[]),some (23,[(3,3,4),(0,9,5),(1,4,5),(3,74,7)]),some (0,[]),some (24,[]),some (25,[]),some (21,[]),some (0,[(0,1,194),(1,236,2)]),some (26,[]),some (5,[(2,115,1),(3,115,1)]),some (5,[(1,115,1),(2,268,2)]),some (0,[(3,1,194)]),some (0,[(2,1,194)]),some (0,[(1,1,194)]),some (0,[(0,1,194)]),some (27,[]),some (5,[]),some (0,[(3,115,1)]),some (0,[(0,115,1)]),some (5,[(0,115,1),(1,115,1)]),some (0,[(2,0,1)]),some (21,[(0,4,5),(1,4,5),(3,8,7)]),some (0,[(2,115,1)]),some (19,[(2,0,1),(3,0,1)]),some (14,[(2,0,1),(3,0,1)]),some (16,[(2,0,1),(3,0,1),(1,4,5)]),some (5,[(2,0,1),(3,0,1)]),some (16,[(2,0,1),(3,0,1)]),some (28,[]),some (29,[]),some (29,[(1,0,1),(2,14,26)]),some (14,[]),some (29,[(1,0,1),(2,14,87)]),some (8,[]),some (30,[]),some (31,[]),some (23,[]),some (32,[]),some (23,[(0,4,5),(1,4,5),(3,8,7)]),some (0,[(1,0,1)]),some (5,[(1,115,1),(0,268,2)]),some (0,[(1,115,1)]),some (33,[]),some (14,[(0,0,1),(1,0,1)]),some (8,[(2,4,5),(3,4,5)]),some (29,[(1,0,1),(2,14,17)]),some (8,[(0,4,5),(1,4,5),(0,3,7)]),some (0,[(0,0,1)]),some (34,[]),some (8,[(3,3,4),(0,9,5),(1,4,5)]),some (16,[(0,0,1),(1,0,1),(1,4,5)]),some (8,[(1,4,5)]),some (8,[(0,3,4),(1,17,5)]),some (8,[(2,3,4),(3,3,4)]),some (8,[(2,3,4),(3,3,4),(1,10,9)]),some (8,[(1,3,4)]),some (16,[(0,0,1),(1,0,1)]),some (5,[(0,0,1),(1,0,1)]),some (8,[(0,3,4),(0,17,5),(3,81,4)]),some (8,[(0,3,4),(3,17,4),(1,17,5)]),some (8,[(0,4,5),(1,4,5)]),some (8,[(1,3,4),(2,20,5)]),some (8,[(0,3,4),(3,17,5)]),some (8,[(0,3,4),(1,3,4),(3,17,20)]),some (8,[(0,3,4),(3,4,5),(1,24,17)]),some (8,[(3,3,4),(2,4,5),(3,6,3)]),some (8,[(0,3,4),(1,23,17),(3,17,5)]),some (8,[(0,3,4),(3,17,4)]),some (23,[(0,4,5),(1,4,5),(0,3,7)]),some (8,[(0,2,3),(1,3,4)]),some (16,[(0,0,1),(1,0,1),(3,23,154)]),some (19,[(0,0,1),(1,0,1)]),some (8,[(3,3,4),(3,9,5),(2,4,5)]),some (8,[(1,3,4),(0,20,5)]),some (8,[(0,3,4),(1,23,17),(1,17,5)]),some (8,[(0,3,4),(1,3,4),(0,20,5)]),some (0,[(0,1,194),(3,236,2)]),some (16,[]),some (21,[(0,3,4),(3,4,5),(1,24,17)]),some (23,[(0,3,4),(3,4,5),(1,24,17)]),some (35,[]),some (21,[(0,3,5)]),some (19,[]),some (29,[(1,1,40),(3,12,166)]),some (0,[(1,1,40)]),some (8,[(0,3,5),(1,12,40)]),some (36,[]),some (29,[(1,12,40),(1,1,91)]),some (37,[]),some (0,[(2,1,26)]),some (8,[(1,4,5),(0,3,7)]),some (0,[(1,1,26)]),some (5,[(0,115,1)]),some (5,[(3,115,1)]),some (5,[(2,115,1)]),some (23,[(3,3,4),(2,4,5),(3,6,3)]),some (14,[(2,0,1)]),some (23,[(3,3,4),(0,9,5),(1,4,5)]),some (16,[(2,0,1),(1,4,5)]),some (14,[(2,0,1),(3,19,111)]),some (5,[(2,0,1)]),some (23,[(0,3,4),(1,3,4),(3,17,20)]),some (19,[(2,0,1)]),some (21,[(0,3,4),(3,17,5)]),some (24,[(0,3,4),(3,17,5)]),some (23,[(0,3,4),(0,17,5),(3,81,4)]),some (23,[(0,3,4),(3,17,5)]),some (30,[(0,3,4),(3,17,5)]),some (23,[(0,3,4),(1,0,17),(3,17,5)]),some (26,[(0,3,4),(3,17,5)]),some (38,[]),some (23,[(0,3,4),(1,17,5)]),some (23,[(0,3,4)]),some (23,[(0,3,5)]),some (23,[(0,3,5),(1,49,40)]),some (29,[(1,12,40),(3,1,91)]),some (16,[(2,0,1)]),some (19,[(0,0,4)]),some (0,[(0,1,5)]),some (5,[(2,0,1),(1,55,19)]),some (23,[(1,4,5),(0,3,7)]),some (0,[(2,0,1),(1,55,19)]),some (23,[(1,4,5)]),some (21,[(0,4,5),(1,4,5)]),some (21,[(1,3,4),(0,20,5)]),some (21,[(0,3,4),(1,17,5)]),some (23,[(2,3,4),(3,3,4),(1,10,9)]),some (21,[(1,3,4),(2,20,5)]),some (8,[(3,3,4)]),some (14,[(0,0,1)]),some (5,[(1,0,1)]),some (8,[(2,3,4)]),some (8,[(2,3,4),(3,10,3)]),some (26,[(0,3,4),(3,17,4)]),some (14,[(1,0,1)]),some (8,[(2,4,5)]),some (31,[(1,0,1),(2,14,26)]),some (28,[(1,0,1),(2,14,26)]),some (8,[(0,3,4),(1,23,17)]),some (21,[(1,4,5)]),some (29,[(1,0,1)]),some (21,[(0,4,5),(1,4,5),(0,3,7)]),some (28,[(1,0,1),(3,3,4)]),some (19,[(1,0,1)]),some (23,[(3,3,4),(3,9,5),(2,4,5)]),some (16,[(1,0,1),(1,4,5)]),some (0,[(2,0,26)]),some (23,[(2,3,4),(3,3,4)]),some (21,[(1,3,4)]),some (8,[(0,3,5)]),some (23,[(0,3,4),(1,3,4),(0,20,5)]),some (8,[(0,3,4)]),some (26,[(0,3,4),(2,14,17)]),some (21,[(0,3,4)]),some (24,[(0,3,4),(2,14,17)]),some (26,[(0,3,4),(2,1,17)]),some (8,[(0,3,4),(2,1,17)]),some (24,[(0,3,4),(2,0,17)]),some (23,[(0,3,4),(2,0,17),(2,1,17)]),some (19,[(0,2,4)]),some (16,[(1,0,1)]),some (23,[(3,3,4),(1,9,62)]),some (31,[(1,0,1),(2,14,49)]),some (0,[(3,55,7)]),some (5,[(3,55,7)]),some (23,[(0,4,5),(1,4,5)]),some (23,[(1,3,4),(2,20,5)]),some (23,[(1,3,4),(0,20,5)]),some (8,[(0,3,4),(1,2,17),(3,17,5)]),some (21,[(1,4,5),(0,3,7)]),some (8,[(0,4,5)]),some (23,[(0,3,4),(2,0,17),(3,17,5)]),some (5,[(3,55,4)]),some (21,[(2,4,5),(3,4,5)]),some (23,[(2,4,5),(3,4,5)]),some (21,[(2,3,4),(3,3,4)]),some (23,[(1,4,5),(3,3,7)]),some (26,[(0,3,5),(2,14,40)]),some (24,[(0,3,5),(2,14,40)]),some (5,[(0,0,1)]),some (23,[(1,4,5),(3,62,7)]),some (0,[(3,62,7)]),some (8,[(0,3,4),(2,2,17)]),some (19,[(0,0,1)]),some (24,[(0,3,4),(2,2,17)]),some (26,[(0,1,5),(1,15,79)]),some (8,[(0,3,4),(1,19,17),(3,17,5)]),some (23,[(0,3,4),(3,17,4),(1,17,5)]),some (23,[(0,3,4),(2,0,17),(1,17,5)]),some (23,[(2,4,5)]),some (16,[(0,0,1)]),some (5,[(1,115,1)]),some (23,[(0,3,4),(1,0,17),(1,17,5)]),some (21,[(2,4,5)]),some (8,[(2,4,5),(1,6,3)]),some (23,[(1,3,4),(3,62,20)]),some (8,[(1,4,5),(3,3,7)]),some (23,[(2,4,5),(1,6,62)]),some (8,[(0,3,4),(3,4,5)]),some (21,[(0,3,4),(3,4,5)]),some (8,[(0,3,4),(0,4,5)]),some (5,[(3,62,4)]),some (8,[(0,3,4),(1,3,4)]),some (8,[(2,4,5),(3,6,3)]),some (16,[(0,0,1),(1,4,5)]),some (8,[(3,3,4),(2,4,5)]),some (8,[(3,3,4),(1,4,5)]),some (26,[(0,3,4),(2,2,17)]),some (8,[(0,3,4),(0,17,5)]),some (19,[(3,2,4)]),some (31,[(1,0,1),(2,14,17)]),some (23,[(1,4,5),(3,60,7)]),some (8,[(3,3,4),(3,9,5)]),some (0,[(2,1,40)]),some (31,[(1,0,1)]),some (23,[(0,3,4),(2,0,17)]),some (0,[(1,0,26)]),some (29,[(1,0,26)]),some (8,[(3,3,4),(0,9,5)]),some (29,[(1,0,1),(2,14,40)]),some (24,[(0,3,4),(3,17,4)]),some (31,[(1,0,26)]),some (28,[(1,0,26)]),some (5,[(2,0,17)]),some (23,[(0,3,4),(3,4,5)]),some (29,[(1,0,17)]),some (5,[(1,0,17)]),some (23,[(2,3,4),(3,10,3)]),some (28,[(1,0,1)]),some (29,[(1,12,40)]),some (26,[(0,1,5)]),some (23,[(3,3,4),(1,4,5)]),some (23,[(0,3,4),(3,17,4)]),some (5,[(3,2,4)]),some (24,[(0,0,3)]),some (23,[(1,49,3)]),some (23,[(0,3,4),(0,4,5)]),some (26,[(0,3,4)]),some (23,[(3,3,4),(2,4,5)]),some (21,[(3,3,4)]),some (24,[(3,3,4)]),some (30,[(0,3,4),(2,1,17)]),some (5,[(2,1,17)]),some (30,[(0,3,4),(2,0,17)]),some (23,[(3,3,4),(0,9,5)]),some (24,[(0,2,4),(1,49,3)]),some (23,[(3,3,4),(3,9,5)]),some (31,[(1,0,1),(3,6,14)]),some (23,[(0,3,4),(0,17,5)]),some (30,[(0,3,4),(3,17,4)]),some (30,[(0,3,4)]),some (23,[(0,3,4),(1,0,17)]),some (8,[(3,11,3),(2,1,37)]),some (23,[(3,49,5)]),some (23,[(0,3,4),(1,3,4)]),some (30,[(0,61,4)]),some (28,[(1,0,1),(0,14,4)]),some (21,[(0,4,5)]),some (21,[(2,3,4)]),some (5,[(0,2,4)]),some (23,[(0,4,5)]),some (26,[(0,1,4)]),some (0,[(0,2,5)]),some (23,[(2,4,5),(1,6,3)]),some (31,[(1,0,1),(1,6,3)]),some (0,[(3,2,5)]),some (24,[(0,0,3),(3,18,4)]),some (30,[(0,0,3),(3,18,4)]),some (24,[(0,0,4),(3,12,3)]),some (8,[(3,12,3)]),some (30,[(0,0,4),(3,12,3)]),some (26,[(3,3,4)]),some (30,[(3,3,4)]),some (23,[(3,3,4)]),some (23,[(2,3,4)]),some (26,[(0,3,5)]),some (24,[(0,3,5)]),some (23,[(2,4,5),(3,6,3)]),some (23,[(3,58,3)]),some (24,[(0,3,4)]),some (21,[(0,3,4),(2,0,17)]),some (29,[(1,0,1),(2,14,49)]),some (29,[(1,1,40)]),some (8,[(0,3,4),(1,19,17)]),some (8,[(3,3,4),(1,9,18)]),some (31,[(1,2,3)]),some (23,[(1,3,4)]),some (8,[(0,3,4),(1,2,17)]),some (24,[(0,2,4),(3,49,3)]),some (30,[(0,3,69)]),some (24,[(0,2,3),(3,62,4)]),some (26,[(0,14,4)]),some (24,[(0,14,4)]),some (23,[(3,60,4)]),some (30,[(0,3,5)]),some (24,[(0,0,4)]),some (30,[(0,0,4)]),some (29,[(1,0,3)]),some (28,[(1,0,3)]),some (30,[(0,0,3)]),some (24,[(0,2,4)]),some (30,[(0,1,4)]),some (30,[(0,1,3)]),some (30,[(2,0,3)]),some (24,[(2,0,3)]),some (28,[(1,2,3)]),some (26,[(2,1,3)]),some (30,[(2,1,3)]),some (24,[(2,2,3)]),some (30,[(0,1,5)])]
lemma gp_34 : goodPairs G_34 pos_34 neg_34 := goodPairs_of (by decide +kernel)
lemma base_34_ok : ∀ x ∈ base_34, faithful pos_34 neg_34 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_34_ok : btAll (fun x => faithful pos_34 neg_34 x ∧ x.1 < 2^128) W_34 := buildWiresBT_faithful base_34_ok
set_option maxRecDepth 500000 in
lemma autos_34_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_34 = G_34) autos_34 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_34_0_ok : sliceDirectCheck 16 8 0 R_34 G_34 R_7 G_7 = true := by decide +kernel
lemma sl_34_0 : Slice R_34 G_34 (subcubeFast 16 8) 6 := slice_fast_direct sl_34_0_ok low_7
lemma sl_34_1_ok : sliceDirectCheck 4 3 0 R_34 G_34 R_0 G_0 = true := by decide +kernel
lemma sl_34_1 : Slice R_34 G_34 (subcubeFast 4 3) 4 := slice_fast_direct sl_34_1_ok low_0
lemma sl_34_2_ok : sliceDirectCheck 2 5 0 R_34 G_34 R_0 G_0 = true := by decide +kernel
lemma sl_34_2 : Slice R_34 G_34 (subcubeFast 2 5) 4 := slice_fast_direct sl_34_2_ok low_0
lemma sl_34_3_ok : sliceDirectCheck 1 2 0 R_34 G_34 R_8 G_8 = true := by decide +kernel
lemma sl_34_3 : Slice R_34 G_34 (subcubeFast 1 2) 5 := slice_fast_direct sl_34_3_ok low_8
lemma sl_34_4_ok : sliceDirectCheck 2 1 0 R_34 G_34 R_8 G_8 = true := by decide +kernel
lemma sl_34_4 : Slice R_34 G_34 (subcubeFast 2 1) 5 := slice_fast_direct sl_34_4_ok low_8
lemma sl_34_5_ok : sliceDirectCheck 32 8 0 R_34 G_34 R_17 G_17 = true := by decide +kernel
lemma sl_34_5 : Slice R_34 G_34 (subcubeFast 32 8) 6 := slice_fast_direct sl_34_5_ok low_17
lemma sl_34_6_ok : sliceDirectCheck 1 48 0 R_34 G_34 R_4 G_4 = true := by decide +kernel
lemma sl_34_6 : Slice R_34 G_34 (subcubeFast 1 48) 4 := slice_fast_direct sl_34_6_ok low_4
lemma sl_34_7_ok : sliceDirectCheck 8 32 0 R_34 G_34 R_10 G_10 = true := by decide +kernel
lemma sl_34_7 : Slice R_34 G_34 (subcubeFast 8 32) 5 := slice_fast_direct sl_34_7_ok low_10
lemma sl_34_8_ok : sliceDirectCheck 0 1 0 R_34 G_34 R_27 G_27 = true := by decide +kernel
lemma sl_34_8 : Slice R_34 G_34 (subcubeFast 0 1) 8 := slice_fast_direct sl_34_8_ok low_27
lemma sl_34_9_ok : sliceDirectCheck 1 16 0 R_34 G_34 R_16 G_16 = true := by decide +kernel
lemma sl_34_9 : Slice R_34 G_34 (subcubeFast 1 16) 5 := slice_fast_direct sl_34_9_ok low_16
lemma sl_34_10_ok : sliceDirectCheck 0 3 0 R_34 G_34 R_9 G_9 = true := by decide +kernel
lemma sl_34_10 : Slice R_34 G_34 (subcubeFast 0 3) 5 := slice_fast_direct sl_34_10_ok low_9
lemma sl_34_11_ok : sliceDirectCheck 0 6 0 R_34 G_34 R_20 G_20 = true := by decide +kernel
lemma sl_34_11 : Slice R_34 G_34 (subcubeFast 0 6) 5 := slice_fast_direct sl_34_11_ok low_20
lemma sl_34_12_ok : sliceDirectCheck 4 2 0 R_34 G_34 R_18 G_18 = true := by decide +kernel
lemma sl_34_12 : Slice R_34 G_34 (subcubeFast 4 2) 5 := slice_fast_direct sl_34_12_ok low_18
lemma sl_34_13_ok : sliceDirectCheck 0 5 0 R_34 G_34 R_21 G_21 = true := by decide +kernel
lemma sl_34_13 : Slice R_34 G_34 (subcubeFast 0 5) 5 := slice_fast_direct sl_34_13_ok low_21
lemma sl_34_14_ok : sliceDirectCheck 16 0 0 R_34 G_34 R_24 G_24 = true := by decide +kernel
lemma sl_34_14 : Slice R_34 G_34 (subcubeFast 16 0) 7 := slice_fast_direct sl_34_14_ok low_24
lemma sl_34_15_ok : sliceDirectCheck 1 4 0 R_34 G_34 R_19 G_19 = true := by decide +kernel
lemma sl_34_15 : Slice R_34 G_34 (subcubeFast 1 4) 5 := slice_fast_direct sl_34_15_ok low_19
lemma sl_34_16_ok : sliceDirectCheck 0 8 0 R_34 G_34 R_26 G_26 = true := by decide +kernel
lemma sl_34_16 : Slice R_34 G_34 (subcubeFast 0 8) 7 := slice_fast_direct sl_34_16_ok low_26
lemma sl_34_17_ok : sliceDirectCheck 2 48 0 R_34 G_34 R_3 G_3 = true := by decide +kernel
lemma sl_34_17 : Slice R_34 G_34 (subcubeFast 2 48) 4 := slice_fast_direct sl_34_17_ok low_3
lemma sl_34_18_ok : sliceDirectCheck 1 6 0 R_34 G_34 R_0 G_0 = true := by decide +kernel
lemma sl_34_18 : Slice R_34 G_34 (subcubeFast 1 6) 4 := slice_fast_direct sl_34_18_ok low_0
lemma sl_34_19_ok : sliceDirectCheck 32 0 0 R_34 G_34 R_30 G_30 = true := by decide +kernel
lemma sl_34_19 : Slice R_34 G_34 (subcubeFast 32 0) 7 := slice_fast_direct sl_34_19_ok low_30
lemma sl_34_20_ok : sliceDirectCheck 8 48 0 R_34 G_34 R_1 G_1 = true := by decide +kernel
lemma sl_34_20 : Slice R_34 G_34 (subcubeFast 8 48) 4 := slice_fast_direct sl_34_20_ok low_1
lemma sl_34_21_ok : sliceDirectCheck 0 2 0 R_34 G_34 R_33 G_33 = true := by decide +kernel
lemma sl_34_21 : Slice R_34 G_34 (subcubeFast 0 2) 8 := slice_fast_direct sl_34_21_ok low_33
lemma sl_34_22_ok : sliceDirectCheck 4 48 0 R_34 G_34 R_2 G_2 = true := by decide +kernel
lemma sl_34_22 : Slice R_34 G_34 (subcubeFast 4 48) 4 := slice_fast_direct sl_34_22_ok low_2
lemma sl_34_23_ok : sliceDirectCheck 0 4 0 R_34 G_34 R_32 G_32 = true := by decide +kernel
lemma sl_34_23 : Slice R_34 G_34 (subcubeFast 0 4) 8 := slice_fast_direct sl_34_23_ok low_32
lemma sl_34_24_ok : sliceDirectCheck 2 0 0 R_34 G_34 R_29 G_29 = true := by decide +kernel
lemma sl_34_24 : Slice R_34 G_34 (subcubeFast 2 0) 8 := slice_fast_direct sl_34_24_ok low_29
lemma sl_34_25_ok : sliceDirectCheck 2 16 0 R_34 G_34 R_14 G_14 = true := by decide +kernel
lemma sl_34_25 : Slice R_34 G_34 (subcubeFast 2 16) 5 := slice_fast_direct sl_34_25_ok low_14
lemma sl_34_26_ok : sliceDirectCheck 1 0 0 R_34 G_34 R_23 G_23 = true := by decide +kernel
lemma sl_34_26 : Slice R_34 G_34 (subcubeFast 1 0) 8 := slice_fast_direct sl_34_26_ok low_23
lemma sl_34_27_ok : sliceDirectCheck 4 1 0 R_34 G_34 R_19 G_19 = true := by decide +kernel
lemma sl_34_27 : Slice R_34 G_34 (subcubeFast 4 1) 5 := slice_fast_direct sl_34_27_ok low_19
lemma sl_34_28_ok : sliceDirectCheck 0 32 0 R_34 G_34 R_31 G_31 = true := by decide +kernel
lemma sl_34_28 : Slice R_34 G_34 (subcubeFast 0 32) 8 := slice_fast_direct sl_34_28_ok low_31
lemma sl_34_29_ok : sliceDirectCheck 0 48 0 R_34 G_34 R_6 G_6 = true := by decide +kernel
lemma sl_34_29 : Slice R_34 G_34 (subcubeFast 0 48) 7 := slice_fast_direct sl_34_29_ok low_6
lemma sl_34_30_ok : sliceDirectCheck 4 0 0 R_34 G_34 R_28 G_28 = true := by decide +kernel
lemma sl_34_30 : Slice R_34 G_34 (subcubeFast 4 0) 8 := slice_fast_direct sl_34_30_ok low_28
lemma sl_34_31_ok : sliceDirectCheck 0 16 0 R_34 G_34 R_25 G_25 = true := by decide +kernel
lemma sl_34_31 : Slice R_34 G_34 (subcubeFast 0 16) 8 := slice_fast_direct sl_34_31_ok low_25
lemma sl_34_32_ok : sliceDirectCheck 4 16 0 R_34 G_34 R_12 G_12 = true := by decide +kernel
lemma sl_34_32 : Slice R_34 G_34 (subcubeFast 4 16) 5 := slice_fast_direct sl_34_32_ok low_12
lemma sl_34_33_ok : sliceDirectCheck 1 32 0 R_34 G_34 R_15 G_15 = true := by decide +kernel
lemma sl_34_33 : Slice R_34 G_34 (subcubeFast 1 32) 5 := slice_fast_direct sl_34_33_ok low_15
lemma sl_34_34_ok : sliceDirectCheck 2 4 0 R_34 G_34 R_18 G_18 = true := by decide +kernel
lemma sl_34_34 : Slice R_34 G_34 (subcubeFast 2 4) 5 := slice_fast_direct sl_34_34_ok low_18
lemma sl_34_35_ok : sliceDirectCheck 8 16 0 R_34 G_34 R_5 G_5 = true := by decide +kernel
lemma sl_34_35 : Slice R_34 G_34 (subcubeFast 8 16) 5 := slice_fast_direct sl_34_35_ok low_5
lemma sl_34_36_ok : sliceDirectCheck 2 32 0 R_34 G_34 R_13 G_13 = true := by decide +kernel
lemma sl_34_36 : Slice R_34 G_34 (subcubeFast 2 32) 5 := slice_fast_direct sl_34_36_ok low_13
lemma sl_34_37_ok : sliceDirectCheck 8 0 0 R_34 G_34 R_22 G_22 = true := by decide +kernel
lemma sl_34_37 : Slice R_34 G_34 (subcubeFast 8 0) 6 := slice_fast_direct sl_34_37_ok low_22
lemma sl_34_38_ok : sliceDirectCheck 4 32 0 R_34 G_34 R_11 G_11 = true := by decide +kernel
lemma sl_34_38 : Slice R_34 G_34 (subcubeFast 4 32) 5 := slice_fast_direct sl_34_38_ok low_11
set_option maxRecDepth 500000 in
lemma slices_34_ok : btAll (fun o => ∀ p, o = some p → Slice R_34 G_34 p.1 p.2) slices_34 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_34 G_34 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_34_0) (forall_cons (fun _ h => by cases h; exact sl_34_1) (forall_cons (fun _ h => by cases h; exact sl_34_2) (forall_cons (fun _ h => by cases h; exact sl_34_3) (forall_cons (fun _ h => by cases h; exact sl_34_4) (forall_cons (fun _ h => by cases h; exact sl_34_5) (forall_cons (fun _ h => by cases h; exact sl_34_6) (forall_cons (fun _ h => by cases h; exact sl_34_7) (forall_cons (fun _ h => by cases h; exact sl_34_8) (forall_cons (fun _ h => by cases h; exact sl_34_9) (forall_cons (fun _ h => by cases h; exact sl_34_10) (forall_cons (fun _ h => by cases h; exact sl_34_11) (forall_cons (fun _ h => by cases h; exact sl_34_12) (forall_cons (fun _ h => by cases h; exact sl_34_13) (forall_cons (fun _ h => by cases h; exact sl_34_14) (forall_cons (fun _ h => by cases h; exact sl_34_15) (forall_cons (fun _ h => by cases h; exact sl_34_16) (forall_cons (fun _ h => by cases h; exact sl_34_17) (forall_cons (fun _ h => by cases h; exact sl_34_18) (forall_cons (fun _ h => by cases h; exact sl_34_19) (forall_cons (fun _ h => by cases h; exact sl_34_20) (forall_cons (fun _ h => by cases h; exact sl_34_21) (forall_cons (fun _ h => by cases h; exact sl_34_22) (forall_cons (fun _ h => by cases h; exact sl_34_23) (forall_cons (fun _ h => by cases h; exact sl_34_24) (forall_cons (fun _ h => by cases h; exact sl_34_25) (forall_cons (fun _ h => by cases h; exact sl_34_26) (forall_cons (fun _ h => by cases h; exact sl_34_27) (forall_cons (fun _ h => by cases h; exact sl_34_28) (forall_cons (fun _ h => by cases h; exact sl_34_29) (forall_cons (fun _ h => by cases h; exact sl_34_30) (forall_cons (fun _ h => by cases h; exact sl_34_31) (forall_cons (fun _ h => by cases h; exact sl_34_32) (forall_cons (fun _ h => by cases h; exact sl_34_33) (forall_cons (fun _ h => by cases h; exact sl_34_34) (forall_cons (fun _ h => by cases h; exact sl_34_35) (forall_cons (fun _ h => by cases h; exact sl_34_36) (forall_cons (fun _ h => by cases h; exact sl_34_37) (forall_cons (fun _ h => by cases h; exact sl_34_38) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))
def bk_34_init : BT (List (List Nat)) := BT.empty
lemma bk_34_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 (0 - 1) xs.toFinset) bk_34_init := trivial
def nodes_34_0 : List NodeSpec := []
def P_34_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_0 : checkNodesBT W_34 G_34 fmask_34 P_34_0 autos_34 bk_34_init 0 nodes_34_0 = true := by decide +kernel
def bk_34_0 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_0
set_option maxRecDepth 500000 in
lemma bk_34_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 0 xs.toFinset) bk_34_0 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_init_ok chk_34_0
def nodes_34_1 : List NodeSpec := []
def P_34_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_1 : checkNodesBT W_34 G_34 fmask_34 P_34_1 autos_34 bk_34_0 1 nodes_34_1 = true := by decide +kernel
def bk_34_1 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_1
set_option maxRecDepth 500000 in
lemma bk_34_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 1 xs.toFinset) bk_34_1 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_0_ok chk_34_1
def nodes_34_2 : List NodeSpec := [([155,457,3],[],[])]
def P_34_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_2 : checkNodesBT W_34 G_34 fmask_34 P_34_2 autos_34 bk_34_1 2 nodes_34_2 = true := by decide +kernel
def bk_34_2 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_2
set_option maxRecDepth 500000 in
lemma bk_34_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 2 xs.toFinset) bk_34_2 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_1_ok chk_34_2
def nodes_34_3 : List NodeSpec := [([454,400,4,5],[],[]),([155,178,383,3],[],[]),([457,3,4,43],[],[]),([457,3,8,7],[],[0]),([155,294,309,3],[],[0]),([33,457,3,4],[],[]),([155,291,308,3],[],[0]),([10,9,457,5],[],[]),([6,24,457,3],[],[0]),([466,3,4,5],[],[]),([155,178,398,3],[],[]),([32,457,3,4],[],[]),([457,3,4,34],[],[])]
def P_34_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_3 : checkNodesBT W_34 G_34 fmask_34 P_34_3 autos_34 bk_34_2 3 nodes_34_3 = true := by decide +kernel
def bk_34_3 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_3
set_option maxRecDepth 500000 in
lemma bk_34_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 3 xs.toFinset) bk_34_3 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_2_ok chk_34_3
def nodes_34_4 : List NodeSpec := [([18,236,312,4,5],[],[]),([303,414,2,4,5],[],[]),([23,238,408,4,5],[],[]),([297,422,3,4,5],[],[]),([155,192,14,2,3],[],[]),([227,23,177,4,5],[],[]),([155,169,23,2,3],[],[]),([23,288,400,4,5],[],[0]),([169,23,2,26,8],[],[]),([32,178,462,3,4],[],[]),([32,178,463,3,4],[],[]),([415,23,3,4,5],[],[]),([155,55,178,2,3],[0],[]),([460,18,2,4,5],[],[]),([155,178,62,2,3],[0],[]),([414,2,4,210,5],[],[]),([434,23,2,4,5],[],[]),([178,62,222,4,5],[0],[]),([345,227,178,4,5],[],[]),([227,178,4,346,5],[],[]),([178,295,2,26,8],[],[]),([178,383,3,4,43],[],[]),([155,277,178,2,3],[0],[0]),([414,2,4,464,5],[],[]),([32,178,383,3,4],[],[]),([14,2,3,195,420],[],[]),([155,178,295,2,3],[0],[]),([6,24,291,308,3],[],[0]),([6,24,178,398,3],[],[0]),([295,2,444,4,5],[0],[]),([10,9,294,309,5],[],[0]),([178,398,3,8,7],[],[0]),([211,425,2,4,5],[],[]),([10,9,178,383,5],[],[]),([10,9,178,398,5],[],[]),([155,291,178,2,3],[],[0]),([33,178,398,3,4],[],[]),([309,440,3,4,5],[],[0]),([32,178,398,3,4],[],[]),([178,398,3,4,34],[],[]),([155,178,309,2,3],[],[0]),([454,273,3,4,5],[],[0]),([6,24,294,309,3],[],[0]),([10,9,178,427,5],[],[]),([309,458,3,4,5],[],[]),([294,309,3,8,7],[],[0]),([294,461,3,4,5],[],[0]),([33,294,309,3,4],[],[0]),([178,383,3,4,34],[],[]),([294,309,3,4,34],[],[0]),([294,309,3,4,43],[],[0]),([6,24,178,383,3],[],[0]),([10,457,3,4,5],[],[0]),([32,294,309,3,4],[],[0]),([227,23,419,4,5],[],[]),([6,457,3,4,5],[],[0]),([178,383,3,8,7],[],[0]),([155,178,2,308,3],[],[0]),([178,62,2,26,8],[],[]),([414,2,4,5,7],[0],[]),([291,308,3,8,7],[],[0]),([178,398,3,4,43],[],[]),([33,291,308,3,4],[],[0]),([33,178,383,3,4],[],[]),([227,178,4,5,7],[0],[]),([457,3,8,4,5],[],[0]),([23,393,62,4,5],[],[]),([10,9,291,308,5],[],[0]),([178,2,3,195],[],[]),([457,3,4,20,5],[1],[0]),([291,308,3,4,43],[],[0]),([457,17,3,4,5],[],[0]),([457,3,4,5,7],[],[0]),([155,294,178,2,3],[],[0]),([465,414,2,4,5],[],[]),([32,291,308,3,4],[],[0]),([423,23,3,4,5],[],[]),([10,9,178,433,5],[],[]),([291,308,3,4,34],[],[0]),([9,457,3,4,5],[],[0])]
def P_34_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [0,1]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_4 : checkNodesBT W_34 G_34 fmask_34 P_34_4 autos_34 bk_34_3 4 nodes_34_4 = true := by decide +kernel
def bk_34_4 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_4
set_option maxRecDepth 500000 in
lemma bk_34_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 4 xs.toFinset) bk_34_4 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_3_ok chk_34_4
def nd_34_5_0 : List NodeSpec := [([409,0,2,3,4,5],[],[]),([333,18,1,194,4,5],[2],[]),([18,1,312,194,4,5],[3],[0]),([115,410,1,2,4,5],[],[]),([115,1,411,2,4,5],[],[]),([303,212,211,2,4,5],[],[0]),([316,115,1,4,5,7],[4],[]),([115,1,339,4,5,7],[5,6,7],[]),([303,316,115,1,4,5],[],[]),([115,1,412,2,4,5],[],[]),([209,318,1,2,4,5],[],[]),([115,413,1,2,4,5],[],[]),([303,209,268,2,4,5],[],[0]),([209,268,2,4,210,5],[],[0]),([115,414,2,4,5],[1,9,10],[0,1]),([155,55,19,53,2,3],[11],[0]),([319,211,1,2,4,5],[6],[]),([155,19,53,62,2,3],[11],[0]),([115,1,339,4,210,5],[5,6],[]),([19,53,62,2,26,8],[],[0]),([345,227,19,53,4,5],[],[0]),([0,1,238,408,4,5],[],[0]),([415,0,1,3,4,5],[],[0]),([416,0,1,2,3,195],[],[]),([358,1,14,2,3,195],[12],[]),([0,1,417,3,4,5],[],[]),([155,0,1,160,2,3],[],[]),([227,0,1,177,4,5],[],[0]),([227,0,1,418,4,5],[],[]),([227,0,1,419,4,5],[],[0]),([0,1,393,62,4,5],[],[0]),([155,169,0,1,2,3],[],[0]),([211,318,1,2,4,5],[6],[]),([0,1,2,3,195,420],[],[0]),([155,0,1,2,138,3],[],[]),([0,1,288,400,4,5],[],[0]),([266,275,23,2,4,5],[],[0]),([325,23,177,3,4,5],[],[]),([23,238,2,235,4,5],[],[0]),([327,23,177,3,4,5],[],[]),([23,177,375,3,4,5],[],[]),([421,177,2,3,4,5],[],[]),([23,177,2,400,4,5],[],[0]),([23,288,273,3,4,5],[],[0]),([14,2,26,3,259,8],[12],[]),([23,14,2,3,195],[12,14],[0]),([155,118,0,1,2,3],[],[]),([10,9,239,23,2,5],[],[]),([422,154,2,3,4,5],[15],[0]),([423,0,1,3,4,5],[],[0]),([297,241,23,3,4,5],[],[0]),([424,154,2,3,4,5],[1],[]),([204,208,18,2,4,5],[16],[0]),([23,247,286,3,4,5],[1],[0]),([297,374,2,3,4,5],[],[]),([374,2,286,3,4,5],[17,18,12],[]),([32,330,23,2,3,4],[],[]),([14,2,3,87,159,5],[],[]),([376,14,2,3,4,5],[],[]),([6,24,192,14,2,3],[],[0]),([192,177,2,3,4,5],[],[]),([10,9,192,14,2,5],[],[]),([115,1,425,2,4,5],[],[0]),([192,14,2,3,4,43],[],[]),([349,23,2,3,4,5],[],[]),([0,236,312,3,4,5],[19],[0]),([155,23,14,62,2,3],[20,21],[0]),([227,19,53,4,346,5],[],[0]),([23,14,62,2,26,8],[],[0]),([23,177,62,61,4,5],[],[0]),([9,294,309,3,4,5],[],[0]),([23,393,2,3,4,5],[17],[0]),([155,0,1,2,146,3],[],[]),([345,227,23,14,4,5],[],[0]),([227,23,14,4,346,5],[22],[0]),([348,227,23,4,5],[1],[]),([23,174,62,4,5,7],[23,21],[0]),([178,2,351,3,5,7],[24],[]),([6,24,169,23,2,3],[],[0]),([303,115,1,339,4,5],[],[]),([25,169,23,2,4,5],[],[]),([178,426,2,3,4,5],[15,22,25],[]),([169,23,2,26,4,5],[],[0]),([316,115,1,4,210,5],[],[]),([227,19,53,4,5,7],[11],[0]),([326,23,177,2,3,5],[],[]),([33,169,23,2,3,4],[],[]),([169,23,2,3,4,34],[],[]),([60,55,23,177,4,5],[],[0]),([9,178,383,3,4,5],[],[0]),([9,178,2,71,5],[12],[]),([9,178,427,3,4,5],[],[0]),([192,154,2,3,4,5],[],[]),([33,55,178,2,3,4],[26],[]),([10,9,178,373,2,5],[24],[]),([294,309,3,8,4,5],[],[0]),([178,2,17,3,43],[12,0],[]),([212,211,2,4,210,5],[],[0]),([178,2,188,3,5,7],[24],[]),([86,178,2,3,5],[0],[]),([226,178,2,3,4,5],[15],[]),([23,14,62,222,4,5],[21],[0]),([32,428,178,2,3,4],[],[0]),([178,398,17,3,4,5],[5,17],[0]),([155,178,2,3],[12,0],[0]),([32,178,429,2,3,4],[],[]),([129,32,178,2,3,4],[],[]),([129,178,2,3,4,34],[],[]),([178,2,308,3,8,7],[],[0]),([178,2,3,430,4,5],[],[]),([178,2,26,3,8],[0,12],[0]),([334,32,178,2,3,4],[],[]),([18,236,2,231,4,5],[],[0]),([209,268,2,4,5,7],[27],[0]),([334,178,2,3,4,34],[],[]),([178,2,3,218,4,5],[15],[]),([6,24,55,178,2,3],[0],[0]),([212,211,2,4,5,7],[6,28],[0]),([348,227,23,3,4,5],[1],[]),([209,115,339,4,5],[1],[]),([32,178,2,3,359,4],[],[]),([431,177,2,3,4,5],[],[]),([32,169,23,2,3,4],[],[]),([267,178,2,3,4,5],[],[]),([178,2,3,359,4,34],[],[]),([178,2,254,3,4,5],[],[]),([10,9,169,23,2,5],[],[]),([55,178,2,3,8,7],[0,12],[0]),([178,2,3,130,4,34],[],[]),([10,9,55,178,2,5],[],[]),([108,177,2,3,4,5],[],[]),([55,178,2,3,4,43],[26],[]),([9,86,178,2,5],[15],[]),([178,402,2,3,5,7],[24],[]),([32,55,178,2,3,4],[0],[]),([350,23,2,3,4,5],[],[]),([55,178,2,3,4,34],[0,12],[]),([432,177,2,3,4,5],[],[]),([60,178,2,26,4,5],[0],[]),([60,55,178,4,5,7],[0],[0])]
def P_34_5_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [0,1,2,3,4,5,6,7,9,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_5_0 : checkNodesBT W_34 G_34 fmask_34 P_34_5_0 autos_34 bk_34_4 5 nd_34_5_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_5_0 : ∀ ns ∈ nd_34_5_0, Impossible G_34 5 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_4_ok chk_34_5_0
def nd_34_5_1 : List NodeSpec := [([19,53,62,222,4,5],[11],[0]),([169,23,2,3,4,43],[],[]),([10,9,178,119,2,5],[24],[]),([6,24,178,62,2,3],[0],[0]),([23,2,343,3,4,5],[17],[]),([23,177,2,188,3,5],[],[]),([178,223,2,3,4,5],[],[]),([19,53,2,3,195],[12,29],[0]),([9,178,433,3,4,5],[],[0]),([178,62,2,26,4,5],[25],[0]),([434,0,1,2,4,5],[],[0]),([224,178,2,3,4,5],[],[]),([209,115,339,3,4,5],[30],[]),([374,154,2,17,3,5],[12],[]),([178,62,2,3,8,7],[0,12],[0]),([178,2,225,3,4,5],[15],[]),([33,178,62,2,3,4],[26],[]),([33,192,14,2,3,4],[],[]),([23,177,408,3,4,5],[],[0]),([32,178,62,2,3,4],[0],[]),([115,414,2,3,4,5],[8],[]),([10,9,385,178,2,5],[],[0]),([178,62,61,4,5,7],[0],[0]),([227,178,4,5],[1,0,31],[0,1]),([170,178,2,3,5,7],[24],[]),([178,2,3,435,4,5],[15],[]),([32,192,14,2,3,4],[],[]),([115,436,1,2,4,5],[],[]),([178,2,308,3,4,34],[],[0]),([178,2,3,437,4,5],[15],[]),([178,383,3,8,4,5],[],[0]),([178,438,2,3,4,5],[],[]),([25,178,295,2,4,5],[17],[]),([178,62,2,3,4,43],[26],[]),([178,2,3,87,5],[0,12],[]),([414,2,4,5],[1,0,31],[0,1]),([178,295,2,26,4,5],[17],[0]),([32,178,2,3,130,4],[],[]),([33,178,295,2,3,4],[26],[]),([32,178,295,2,3,4],[0],[]),([178,295,2,3,4,34],[0,12],[]),([32,294,178,2,3,4],[],[0]),([178,2,26,302,4,5],[0],[]),([10,9,178,295,2,5],[],[]),([178,439,2,3,4,5],[],[]),([19,1,2,3,195,310],[],[]),([14,2,3,87,352,5],[],[]),([10,9,277,178,2,5],[],[0]),([6,294,309,3,4,5],[],[0]),([33,277,178,2,3,4],[26],[0]),([209,319,1,2,4,5],[6],[]),([6,24,178,309,2,3],[],[0]),([414,2,3,4,5],[0,1,31],[]),([155,55,23,14,2,3],[15,21],[0]),([291,308,3,8,4,5],[],[0]),([178,2,440,3,4,5],[15],[0]),([277,2,302,4,5,7],[0],[0]),([25,178,62,2,4,5],[25],[]),([32,178,2,308,3,4],[],[0]),([6,178,383,3,4,5],[],[0]),([115,441,1,2,4,5],[],[]),([155,192,0,1,2,3],[],[0]),([178,398,3,8,4,5],[],[0]),([178,383,3,4,20,5],[5,17,22],[0]),([442,178,2,3,4,5],[],[]),([0,1,2,146,26,8],[],[]),([10,9,178,62,2,5],[],[]),([9,178,398,3,4,5],[],[0]),([169,23,2,3,8,7],[],[0]),([178,443,2,3,4,5],[],[]),([178,2,3,444,4,5],[0],[0]),([10,178,398,3,4,5],[],[0]),([6,24,178,295,2,3],[0],[0]),([178,62,2,3,4,34],[0,12],[]),([178,383,17,3,4,5],[],[0]),([178,398,3,4,20,5],[5,1],[0]),([6,178,398,3,4,5],[5,17],[0]),([382,23,2,3,4,5],[],[]),([178,445,2,3,4,5],[],[]),([178,309,2,3,8,7],[],[0]),([178,446,2,3,4,5],[22],[]),([178,2,3,222,4,5],[0],[0]),([328,23,177,2,4,5],[],[]),([192,14,2,3,4,34],[],[]),([10,9,178,309,2,5],[],[0]),([178,447,2,3,4,5],[15],[]),([32,277,178,2,3,4],[0],[0]),([32,344,14,2,3,4],[],[]),([33,178,309,2,3,4],[],[0]),([178,448,2,3,4,5],[],[]),([341,0,1,62,4,5],[],[]),([255,260,23,3,4,5],[],[0]),([178,2,17,3,87,5],[12,31],[]),([291,178,2,3,4,43],[],[0]),([6,24,277,178,2,3],[0],[0]),([33,291,178,2,3,4],[],[0]),([178,309,2,3,4,43],[],[0]),([449,178,2,3,4,5],[],[]),([178,2,3,450,4,5],[0],[]),([291,308,3,4,20,5],[5,1],[0]),([10,9,178,2,308,5],[],[0]),([32,178,309,2,3,4],[],[0]),([0,1,2,3,195,451],[],[]),([10,294,309,3,4,5],[],[0]),([294,309,17,3,4,5],[],[0]),([452,0,1,3,4,5],[],[]),([33,294,178,2,3,4],[],[0]),([192,14,2,3,8,7],[],[0]),([115,1,453,2,4,5],[],[]),([10,9,178,2,111,5],[],[]),([294,178,2,3,4,43],[],[0]),([178,2,3,269,4,5],[0],[]),([6,24,291,178,2,3],[],[0]),([178,309,2,3,4,34],[],[0]),([454,177,2,3,4,5],[],[0]),([178,356,2,3,5,7],[24],[]),([455,178,2,3,4,5],[],[]),([169,0,1,2,26,8],[],[0]),([277,178,2,3,4,34],[0,12],[0]),([33,178,2,308,3,4],[],[0]),([178,2,3,217,4,5],[15],[]),([294,309,3,4,20,5],[25,22],[0]),([227,23,14,4,5,7],[22,21],[0]),([178,2,3,456,4,5],[],[]),([457,3,4,5],[1],[0,1]),([6,291,308,3,4,5],[5,22],[0]),([32,291,178,2,3,4],[],[0]),([178,2,308,3,4,43],[],[0]),([178,2,458,3,4,5],[],[0]),([74,178,2,3,7],[32,12],[0]),([88,178,2,3,5],[],[]),([291,178,2,3,4,34],[],[0]),([277,178,2,3,8,7],[0,12],[0]),([178,383,3,4,5,7],[17,5],[0]),([10,9,289,14,2,5],[],[]),([10,9,294,178,2,5],[],[0]),([9,178,2,3,34],[12],[]),([294,178,2,3,8,7],[12,24],[0]),([291,308,17,3,4,5],[5,22],[0]),([178,295,2,3,4,43],[26],[])]
def P_34_5_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [0,1,5,6,8,11,12,15,17,21,22,24,25,26,29,30,31,32]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_5_1 : checkNodesBT W_34 G_34 fmask_34 P_34_5_1 autos_34 bk_34_4 5 nd_34_5_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_5_1 : ∀ ns ∈ nd_34_5_1, Impossible G_34 5 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_4_ok chk_34_5_1
def nd_34_5_2 : List NodeSpec := [([178,398,3,4,5,7],[],[0]),([294,178,2,3,4,34],[12,24],[0]),([6,24,178,2,308,3],[],[0]),([459,1,2,194,4,5],[33],[]),([10,291,308,3,4,5],[],[0]),([10,9,291,178,2,5],[],[0]),([227,178,3,4,5],[0,1,31],[]),([460,0,2,3,4,5],[],[0]),([6,24,294,178,2,3],[],[0]),([294,309,3,4,5,7],[25],[0]),([32,178,215,2,3,4],[],[]),([32,178,2,243,3,4],[],[]),([178,295,2,3,8,7],[0,12],[0]),([291,178,2,3,8,7],[],[0]),([277,178,2,3,4,43],[26],[0]),([6,178,2,3,66],[12,34],[0]),([178,461,2,3,4,5],[15],[0]),([10,178,383,3,4,5],[],[0]),([291,308,3,4,5,7],[],[0]),([9,291,308,3,4,5],[],[0]),([305,295,2,4,5,7],[0],[0])]
def P_34_5_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [0,1,12,15,24,25,26,31,33,34]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_5_2 : checkNodesBT W_34 G_34 fmask_34 P_34_5_2 autos_34 bk_34_4 5 nd_34_5_2 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_5_2 : ∀ ns ∈ nd_34_5_2, Impossible G_34 5 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_4_ok chk_34_5_2
def nodes_34_5 : List NodeSpec := nd_34_5_0 ++ nd_34_5_1 ++ nd_34_5_2
def bk_34_5 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_5
set_option maxRecDepth 500000 in
lemma bk_34_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 5 xs.toFinset) bk_34_5 :=
  buildBucketsBT_of_mem (forall_append (forall_append (mem_34_5_0) mem_34_5_1) mem_34_5_2)
def nd_34_6_0 : List NodeSpec := [([0,1,2,3,195,310],[14,35,29,37,39,36,38],[0,2]),([0,257,2,3,199,4,5],[19],[0]),([0,1,311,3,91,4,5],[41,19],[]),([0,1,312,3,194,4,5],[42,3],[0]),([0,236,2,3,231,4,5],[19],[0]),([293,219,0,2,3,4,5],[],[0]),([0,1,313,3,194,4,5],[19,40,43],[]),([314,0,1,2,3,4,5],[],[]),([0,1,2,315,3,4,5],[44],[]),([212,211,2,3,4,5],[1,28,45,8],[0]),([316,115,1,3,4,5],[4,25,46,6],[]),([209,115,268,2,3,4,5],[30],[0]),([115,1,317,3,4,5],[30,8],[]),([208,18,1,2,194,4,5],[47],[0]),([204,18,1,2,194,4,5],[48],[0]),([18,1,2,194,231,4,5],[49,13,15],[0]),([18,236,1,2,194,4,5],[50],[0]),([115,318,1,2,4,5],[13,15,8,6,51,25],[0,2]),([319,115,1,2,4,5],[13,15,8,6,51,25],[0,2]),([320,115,1,2,4,5],[15,8,51,25,52,13],[]),([115,211,1,2,4,5,7],[8,13,6,53],[0]),([303,115,211,1,2,4,5],[],[0]),([115,211,1,2,4,210,5],[15,39,8,6],[0]),([303,212,115,1,2,4,5],[15,39,6,8],[0]),([321,0,1,93,3,4,5],[],[]),([212,115,1,2,4,210,5],[],[0]),([212,115,211,2,4,5],[1,8,28,45],[0,1]),([316,115,1,4,5],[25,6,4,46],[0,1]),([115,1,268,2,4,210,5],[8,6,39,15],[0]),([209,115,1,2,4,5,7],[8,13,54],[0]),([303,209,115,1,2,4,5],[15,39,6,8],[0]),([209,268,2,4,5],[1,8,27,55],[0]),([19,1,2,26,3,85,8],[13,12],[]),([0,1,2,26,3,213,8],[12],[]),([19,0,1,2,3,195],[12,35,14,29,38,37,39],[0]),([10,9,0,1,2,281,5],[],[]),([10,9,0,1,214,2,5],[],[]),([0,1,2,3,87,322,5],[],[]),([283,0,1,2,3,4,34],[],[]),([32,0,1,216,2,3,4],[],[]),([0,1,216,2,3,4,34],[],[]),([209,115,268,2,4,5],[1,8,27,55],[0,1]),([0,1,2,3,87,127,5],[],[]),([10,9,118,0,1,2,5],[],[]),([118,0,1,2,3,4,34],[],[]),([140,0,1,2,26,4,5],[56],[]),([155,19,0,1,62,2,3],[57,13,41,56],[0]),([19,0,1,62,2,26,8],[13,41],[0]),([212,115,1,2,4,5,7],[6,13,58],[0]),([209,115,1,2,4,210,5],[],[0]),([19,0,1,62,222,4,5],[56],[0]),([227,19,0,1,4,5,7],[22,5,56],[0]),([6,24,0,1,2,146,3],[],[0]),([25,0,1,2,146,4,5],[],[]),([0,1,2,146,26,4,5],[],[0]),([0,1,2,146,3,8,7],[],[0]),([10,9,0,1,2,146,5],[],[]),([33,0,1,2,146,3,4],[],[]),([19,1,2,3,87,197,5],[],[]),([0,1,2,146,3,4,43],[],[]),([0,1,2,146,3,4,34],[],[]),([155,19,53,2,3],[12,41,11],[0]),([19,53,2,26,3,8],[12,11,41],[0]),([6,19,53,2,3,66],[12,29,59],[0]),([74,19,53,2,3,7],[12,61,29],[0]),([10,9,19,53,2,111,5],[],[0]),([9,86,19,53,2,5],[15,41],[0]),([19,53,2,17,3,87,5],[12,62],[0]),([19,53,2,3,87,5],[12,11,41],[0]),([19,53,2,17,3,43],[12,11,41],[0]),([86,19,53,2,3,5],[11,15,41],[0]),([32,19,53,2,243,3,4],[],[0]),([9,19,53,2,3,34],[12,29],[0]),([129,19,53,2,3,4,34],[],[0]),([323,0,1,2,3,4,5],[],[]),([19,53,2,3,130,4,34],[],[0]),([19,53,2,3,217,4,5],[15],[0]),([19,53,2,254,3,4,5],[],[0]),([10,9,55,19,53,2,5],[],[0]),([33,55,19,53,2,3,4],[63],[0]),([55,19,53,2,3,4,34],[11,12],[0]),([60,55,19,53,4,5,7],[11],[0]),([19,53,223,2,3,4,5],[],[0]),([25,19,53,62,2,4,5],[25],[0]),([19,53,62,2,26,4,5],[25],[0]),([19,53,62,2,3,8,7],[11,12],[0]),([19,53,2,225,3,4,5],[15],[0]),([19,53,62,2,3,4,43],[63],[0]),([19,53,62,61,4,5,7],[11],[0]),([0,1,306,233,3,4,5],[],[0]),([266,275,0,1,2,4,5],[],[0]),([32,0,1,2,324,3,4],[],[]),([267,23,14,2,3,4,5],[17,40],[0]),([232,272,0,1,3,4,5],[],[0]),([325,0,1,177,3,4,5],[],[0]),([0,1,238,2,235,4,5],[],[0]),([326,0,1,177,2,3,5],[],[0]),([327,0,1,177,3,4,5],[],[0]),([255,260,0,1,3,4,5],[],[0]),([328,0,1,177,2,4,5],[],[0]),([178,2,153,3,4,5],[12,22,17,8],[]),([234,0,1,2,26,3,8],[66,39],[]),([6,24,55,19,53,2,3],[11],[0]),([10,294,178,2,3,4,5],[15,0],[0]),([10,9,0,1,229,2,5],[],[]),([129,23,14,2,3,4,34],[],[0]),([297,241,0,1,3,4,5],[],[0]),([23,14,2,3,222,4,5],[17,40,21],[0]),([0,1,247,286,3,4,5],[22],[0]),([224,19,53,2,3,4,5],[],[0]),([277,178,2,17,3,4,5],[0,15,17,8],[0]),([329,0,1,2,3,87,5],[68,67],[]),([32,330,0,1,2,3,4],[],[0]),([32,0,1,298,2,3,4],[67],[]),([212,211,2,4,5],[1,8,28,45],[0]),([158,0,1,2,3,87,5],[52,65],[]),([0,1,2,3,331,4,5],[69],[]),([249,0,1,248,3,4,5],[],[0]),([178,285,2,40,3,4,5],[24,34,15],[0]),([158,0,1,2,332,3,4],[],[]),([333,0,1,3,194,4,5],[2],[0]),([334,178,2,17,3,4,5],[24,8],[0]),([0,1,335,2,3,4,5],[70,71],[]),([336,0,1,2,3,4,5],[],[]),([0,1,337,2,3,4,5],[72],[]),([155,55,0,1,14,2,3],[20,74,57,15,41,73,75],[0]),([0,1,177,2,188,3,5],[],[0]),([6,24,0,1,160,2,3],[],[0]),([55,19,53,2,3,8,7],[11,12],[0]),([0,1,338,2,3,4,5],[],[]),([115,1,339,4,5],[6,51,7,76],[0,1]),([32,19,53,215,2,3,4],[],[0]),([294,309,3,4,5],[25,22],[0,1]),([262,0,1,2,3,4,34],[67,65],[]),([250,340,14,2,3,4,5],[40],[]),([0,1,160,2,3,8,7],[67,65],[0]),([115,1,268,2,4,5,7],[6,15,77,13,8,52],[0]),([267,19,53,2,3,4,5],[],[0]),([33,0,1,160,2,3,4],[],[]),([0,1,160,2,3,4,43],[],[])]
def P_34_6_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [0,1,2,3,4,5,6,7,8,11,12,13,14,15,17,19,20,21,22,24,25,27,28,29,30,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,61,62,63,65,66,67,68,69,70,71,72,73,74,75,76,77]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_6_0 : checkNodesBT W_34 G_34 fmask_34 P_34_6_0 autos_34 bk_34_5 6 nd_34_6_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_6_0 : ∀ ns ∈ nd_34_6_0, Impossible G_34 6 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_5_ok chk_34_6_0
def nd_34_6_1 : List NodeSpec := [([60,19,53,2,26,4,5],[11],[0]),([32,0,1,160,2,3,4],[],[]),([0,1,160,2,3,4,34],[67,65],[]),([341,0,1,2,3,4,5],[],[0]),([14,2,40,3,159,4,5],[15,78,79],[]),([0,1,2,342,3,4,5],[69,70],[]),([0,1,2,343,3,4,5],[69,44,40,70,72],[0]),([0,1,14,2,3,195],[14,36,35,37,38,39],[0,3]),([155,0,1,14,62,2,3],[13,75,73,20,74],[0]),([14,2,157,40,3,4,5],[17,15,79],[0]),([32,344,0,1,2,3,4],[],[0]),([0,1,177,62,61,4,5],[72],[0]),([345,227,0,1,14,4,5],[73,22],[0]),([227,0,1,14,4,346,5],[73,22,39],[0]),([227,0,1,347,4,5],[23,22,39,73,52,13],[]),([227,0,1,14,4,5,7],[73,75,13,22,52],[0]),([348,227,0,1,4,5],[22,23,39,73,52,13],[0]),([6,24,23,14,62,2,3],[80,21],[0]),([9,291,178,2,3,4,5],[22,5],[0]),([170,19,53,2,3,5,7],[60],[0]),([23,14,2,188,3,5,7],[79],[0]),([0,1,174,62,4,5,7],[23,75],[0]),([169,0,1,2,3,8,7],[67,65],[0]),([10,9,169,0,1,2,5],[],[0]),([10,9,0,1,2,138,5],[],[]),([60,55,0,1,177,4,5],[],[0]),([33,169,0,1,2,3,4],[],[0]),([169,0,1,2,3,4,43],[],[0]),([10,178,309,2,3,4,5],[22,15,0,25],[0]),([349,0,1,2,3,4,5],[],[0]),([115,1,339,3,4,5],[7,6,51,76],[0]),([350,0,1,2,3,4,5],[],[0]),([178,2,351,3,4,5],[0,17,25,78,34],[0]),([0,1,2,26,3,259,8],[12],[0]),([10,9,289,0,1,2,5],[],[0]),([0,1,2,3,87,352,5],[71,39],[0]),([9,178,309,2,3,4,5],[22,24,25],[0]),([329,0,1,2,17,3,5],[81],[]),([155,55,19,0,1,2,3],[15,13,20,56],[0]),([10,178,62,2,3,4,5],[0,15],[0]),([0,1,353,2,3,4,5],[72],[]),([32,264,0,1,2,3,4],[],[]),([6,24,192,0,1,2,3],[],[0]),([23,14,2,26,3,8],[12,21,82],[0]),([192,0,1,2,3,8,7],[],[0]),([32,0,1,2,146,3,4],[],[]),([19,53,2,3,218,4,5],[15],[0]),([10,9,192,0,1,2,5],[],[0]),([33,192,0,1,2,3,4],[],[0]),([212,115,211,2,3,4,5],[8],[0]),([170,178,2,3,4,5],[0,22,17,8,78,34],[0]),([192,0,1,2,3,4,43],[],[0]),([19,53,62,2,3,4,34],[11,12],[0]),([255,23,177,2,3,4,5],[],[0]),([10,9,0,1,2,271,5],[],[]),([32,0,1,2,138,3,4],[],[]),([23,0,1,62,222,4,5],[83],[0]),([227,23,0,1,4,346,5],[1,25,84],[0]),([32,0,1,354,2,3,4],[],[]),([74,23,14,2,3,7],[12,86,85],[0]),([355,0,1,2,3,4,5],[72],[]),([178,356,2,3,4,5],[0,17,22,25,78,34],[0]),([0,1,2,357,3,4,5],[69,42,72],[]),([10,9,19,53,62,2,5],[],[0]),([264,0,1,2,3,4,34],[],[]),([33,0,1,2,138,3,4],[],[]),([33,19,53,62,2,3,4],[63],[0]),([0,1,2,138,3,4,34],[],[]),([178,2,71,3,4,5],[0,12,17,8,22,25],[0]),([10,9,0,1,160,2,5],[],[]),([32,169,0,1,2,3,4],[],[0]),([266,23,177,2,3,4,5],[],[0]),([358,0,1,2,3,195],[12,35,29,37,36,38],[0,2]),([23,177,2,3,235,4,5],[15,87,78],[0]),([19,53,2,188,3,5,7],[60],[0]),([23,14,62,2,3,4,34],[21,88,12],[0]),([10,9,23,14,2,111,5],[15],[0]),([260,23,177,2,3,4,5],[],[0]),([23,288,177,2,3,4,5],[15],[0]),([227,19,53,4,5],[22,23,11,62],[0,1]),([9,294,178,2,3,4,5],[25,24],[0]),([155,23,14,2,3],[12,20,21],[0]),([9,239,23,2,3,4,5],[],[0]),([9,289,14,2,3,4,5],[],[0]),([10,9,23,14,119,2,5],[79,89],[0]),([9,86,23,14,2,5],[21,15,90],[0]),([297,23,154,2,3,4,5],[],[0]),([23,154,2,286,3,4,5],[93,12,91],[0]),([23,247,154,2,3,4,5],[1],[0]),([33,118,0,1,2,3,4],[],[]),([169,0,1,2,26,4,5],[],[0]),([23,14,2,17,3,87,5],[12,93],[0]),([32,118,0,1,2,3,4],[],[]),([88,23,14,2,3,5],[12,94],[0]),([9,23,14,2,3,34],[12,95],[0]),([144,1,14,2,26,3,8],[12,13],[]),([234,60,0,1,2,4,5],[],[]),([129,32,23,14,2,3,4],[],[0]),([78,1,298,2,3,4,5],[],[]),([241,23,154,2,3,4,5],[15,1],[0]),([226,23,14,2,3,4,5],[69,15],[0]),([32,23,14,2,3,130,4],[],[0]),([0,1,2,138,3,4,43],[],[]),([9,192,14,2,3,4,5],[],[0]),([23,14,2,3,130,4,34],[],[0]),([178,2,17,3,359,4,5],[24,17],[0]),([24,14,2,17,3,159,5],[12],[0]),([6,24,55,23,14,2,3],[15,21],[0]),([0,1,360,2,3,4,5],[],[]),([32,14,2,3,159,4,5],[],[]),([32,262,0,1,2,3,4],[],[]),([14,2,3,159,130,4,5],[],[]),([23,14,2,3,217,4,5],[15],[0]),([55,19,53,2,3,4,43],[63],[0]),([23,14,2,3,218,4,5],[15,17],[0]),([32,0,1,361,2,3,4],[],[]),([23,253,2,3,4,5],[22,92,17],[]),([178,362,2,3,4,5],[5,22,24,15,34,78],[]),([23,14,2,254,3,4,5],[],[0]),([19,53,2,3,222,4,5],[11],[0]),([33,55,23,14,2,3,4],[15,92],[0]),([55,23,14,2,3,4,43],[15,92],[0]),([32,55,23,14,2,3,4],[12,21],[0]),([32,0,1,2,363,3,4],[],[]),([178,2,3,4,34],[12,0],[0]),([55,23,14,2,3,4,34],[12,21],[0]),([55,14,157,3,4,5],[22,25,15],[]),([0,1,298,2,3,4,34],[67],[]),([6,192,14,2,3,4,5],[25,1],[0]),([192,14,2,3,4,5,7],[23],[0]),([192,14,2,3,4,20,5],[1,25],[0]),([0,1,364,2,3,4,5],[70],[]),([291,308,3,4,5],[22,25],[0,1]),([23,14,2,3,269,4,5],[21],[0]),([178,2,3,132,4,5],[5,26,24,15,34,78],[]),([60,55,23,14,4,5,7],[22,21],[0]),([9,55,178,2,3,4,5],[26],[0]),([23,177,2,3,61,4,5],[],[0]),([25,23,14,62,2,4,5],[25],[0]),([178,62,2,3,4,20,5],[1,5,26],[0])]
def P_34_6_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [0,1,5,6,7,8,11,12,13,14,15,17,20,21,22,23,24,25,26,29,34,35,36,37,38,39,40,42,44,51,52,56,60,62,63,65,67,69,70,71,72,73,74,75,76,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_6_1 : checkNodesBT W_34 G_34 fmask_34 P_34_6_1 autos_34 bk_34_5 6 nd_34_6_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_6_1 : ∀ ns ∈ nd_34_6_1, Impossible G_34 6 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_5_ok chk_34_6_1
def nd_34_6_2 : List NodeSpec := [([23,14,62,2,26,4,5],[25],[0]),([224,23,14,2,3,4,5],[69],[0]),([129,32,19,53,2,3,4],[],[0]),([291,178,2,3,4,20,5],[5,22,17],[0]),([155,23,0,1,62,2,3],[15,73,41,74,20,57,83],[0]),([55,23,154,2,3,4,5],[15,1,92],[0]),([227,0,1,347,3,4,5],[22],[]),([23,14,62,2,3,8,7],[21,96,12],[0]),([33,23,14,62,2,3,4],[97,92],[0]),([32,23,14,62,2,3,4],[98,21],[0]),([155,55,23,0,1,2,3],[74,15,73,83],[0]),([178,2,81,3,4,5],[24,12,17,8,22,25],[0,1]),([23,174,62,4,5],[22,23,25,21,93],[0]),([365,115,1,2,4,5],[12,6,51,25],[]),([178,2,308,3,8,4,5],[25,1],[0]),([170,23,14,2,3,5,7],[79],[0]),([6,169,23,2,3,4,5],[1,5],[0]),([178,366,2,3,4,5],[31,12,25,22],[]),([169,23,2,3,8,4,5],[],[0]),([178,309,2,17,3,4,5],[22,24,25],[0]),([178,2,3,367,4,5],[17,25,24,15,34,78],[]),([6,24,169,0,1,2,3],[],[0]),([10,169,23,2,3,4,5],[],[0]),([86,23,14,2,3,5],[21,15,99],[0]),([19,1,2,3,87,80,5],[],[]),([0,1,368,2,3,4,5],[],[]),([55,23,177,2,3,4,5],[15,78],[0,1]),([23,14,2,3,87,5],[12,100,21],[0]),([178,2,369,3,4,5],[12,8,22,25],[]),([169,23,2,3,4,20,5],[5,1],[0]),([32,178,2,17,3,4,5],[31,12],[]),([169,23,2,17,3,4,5],[1,5],[0]),([6,178,2,308,3,4,5],[1,8,25],[0]),([9,23,14,2,71,5],[12,101],[0]),([6,24,178,2,3],[78,15,0],[0]),([178,2,3,27,4,5],[12,26,17,8,22,25],[]),([294,178,2,3,4,20,5],[25,17,15,8,22],[0]),([227,19,53,3,4,5],[11,22,23,62],[0]),([32,14,2,3,159,4],[102],[]),([9,178,2,3,4,5],[12,103,17,8,22,25],[]),([227,23,14,4,5],[22,25,21,93],[0,1]),([291,178,2,3,4,5,7],[5,17],[0]),([189,178,2,3,4,5],[12,25,17,8],[]),([115,370,1,2,4,5],[12,6,51,25],[]),([178,2,26,3,4,5],[15,78,31,0,17,8,22,25],[0]),([19,53,2,3,269,4,5],[11],[0]),([158,0,1,371,2,4,5],[72],[]),([196,1,14,2,3,87,5],[15],[]),([74,178,2,3,4,5],[24,12,34,17,8,22,25],[0]),([227,19,0,1,4,346,5],[22,5],[0]),([6,9,178,2,3,5],[0,12],[0]),([60,55,178,4,5],[1,25,0,31],[0]),([178,2,3,66,4,5],[31,12,17,8,22,25],[0]),([348,227,0,1,3,4,5],[23,22],[0]),([178,2,3,372,4,5],[12,17,22,25],[]),([178,2,3,113,4,5],[12,22,17,8],[]),([9,178,119,2,3,4,5],[24,25],[0]),([55,23,14,2,3,8,7],[12,21],[0]),([178,2,17,3,4,34],[24,12],[0,1]),([9,178,373,2,3,4,5],[24,17],[0]),([178,62,3,61,4,5],[0,1,31],[0]),([178,2,17,3,4,5],[24,12,17,8,22,25],[1]),([23,14,223,2,3,4,5],[],[0]),([118,0,1,2,3,8,7],[],[0]),([305,295,2,3,4,5],[0,31,1,8],[0]),([167,178,3,4,5],[5,12],[]),([178,2,17,3,8,5],[12,0],[]),([32,178,2,17,3,4],[24,12,31],[0]),([374,2,3,4,5],[1,12],[]),([178,2,17,40,3,4,5],[12,0,34],[]),([32,178,2,3,4],[31,12,24],[0]),([32,23,14,2,243,3,4],[12],[0]),([9,277,178,2,3,4,5],[26],[0]),([9,178,2,17,3,5],[31,15,24],[0]),([55,178,2,3,8,4,5],[0,12],[0]),([0,1,177,375,3,4,5],[],[0]),([129,178,2,17,3,4,5],[24,25],[0]),([178,2,182,3,4,5],[12,25,17,8],[]),([9,178,2,3,5,7],[31,12],[0]),([277,178,2,3,4,5,7],[15,17,78,8],[0,1]),([178,2,135,3,4,5],[31,5,12],[]),([178,49,2,40,3,4,5],[24,34,15],[0]),([294,178,2,3,8,4,5],[25,12,24],[0]),([178,148,2,3,4,5],[25,24,15,17,8,34,78],[]),([10,291,178,2,3,4,5],[15,5,22],[0]),([178,139,3,4,5],[1,12],[]),([169,23,2,3,4,5,7],[22,23],[0]),([376,0,1,2,3,4,5],[],[0]),([178,377,2,3,4,5],[0,8,22,78,34],[]),([23,177,62,2,3,4,5],[],[0]),([10,9,178,2,5],[12,24],[0]),([136,178,2,3,4,5],[31,1,12],[]),([23,0,1,62,2,26,8],[15,41,73,104],[0]),([0,1,14,62,222,4,5],[75,73,52,13],[0]),([143,178,2,3,4,5],[22,24,15,17,8,34,78],[]),([277,178,2,3,8,4,5],[0,12],[0]),([178,2,3,104,4,5],[1,26,24,15,34,78],[]),([55,178,2,3,4,20,5],[1,5,26],[0]),([64,178,2,40,3,4,5],[24,34,15],[0]),([345,227,19,0,1,4,5],[22,5],[0]),([234,0,1,62,2,4,5],[72],[]),([178,378,3,4,5],[12,25,17],[]),([6,24,0,1,2,138,3],[],[0]),([209,268,2,3,4,5],[1,27,55,8],[0]),([178,295,2,3,4,20,5],[1,5,26],[0]),([118,0,1,2,3,4,43],[],[]),([55,178,49,3,4,5],[1,25,31,15],[]),([9,178,62,2,3,4,5],[26],[0]),([60,178,2,3,4,5,7],[0,15],[0]),([32,283,0,1,2,3,4],[],[]),([178,2,17,3,130,4,5],[24,22],[0]),([178,2,3,61,4,5,7],[0,15],[0]),([178,2,3,302,4,5,7],[0,15],[0]),([0,1,379,2,3,4,5],[44,40,72],[]),([6,55,178,2,3,4,5],[0,25,22,15],[0]),([178,2,3,141,4,5],[0,5,31,78],[]),([115,380,1,3,4,5],[8,51],[]),([6,178,62,2,3,4,5],[0,22,25,15],[0]),([6,24,118,0,1,2,3],[],[0]),([10,9,239,0,1,2,5],[],[0]),([9,178,2,111,3,4,5],[24,22],[0]),([178,62,2,17,3,4,5],[0,15,22,25],[0]),([305,178,2,3,4,5,7],[0,15],[0]),([192,14,2,3,8,4,5],[],[0]),([9,169,23,2,3,4,5],[],[0]),([277,178,2,3,4,20,5],[1,5,26],[0]),([64,178,62,3,4,5],[1,25,31,15],[]),([23,14,62,61,4,5,7],[21,22],[0]),([178,2,3,381,4,5],[8,22,24,15,34,78],[]),([32,19,53,2,3,130,4],[],[0]),([25,169,0,1,2,4,5],[],[0]),([382,0,1,2,3,4,5],[],[0]),([178,383,3,4,5],[22,17],[0,1]),([178,384,3,4,5],[12,22,17],[]),([9,385,178,2,3,4,5],[24,8],[0]),([178,2,3,8,7],[12,0],[0]),([23,238,177,2,3,4,5],[15,78],[0,1]),([23,174,62,3,4,5],[21,22,25,93],[]),([303,115,1,268,2,4,5],[],[0]),([0,1,14,62,2,26,8],[37,104,39],[0])]
def P_34_6_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [0,1,5,6,8,11,12,13,15,17,20,21,22,23,24,25,26,27,31,34,37,39,40,41,44,51,52,55,57,62,69,72,73,74,75,78,79,83,92,93,96,97,98,99,100,101,102,103,104]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_6_2 : checkNodesBT W_34 G_34 fmask_34 P_34_6_2 autos_34 bk_34_5 6 nd_34_6_2 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_6_2 : ∀ ns ∈ nd_34_6_2, Impossible G_34 6 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_5_ok chk_34_6_2
def nd_34_6_3 : List NodeSpec := [([178,62,2,3,4,5,7],[15,22,78,25],[0,1]),([178,2,3,386,4,5],[26,8,24,15,22,25,34,78],[]),([6,178,295,2,3,4,5],[0,8,17,15],[0]),([9,19,53,2,71,5],[12,29],[0]),([282,178,2,40,3,4,5],[24,34,15],[0]),([178,2,308,3,4,20,5],[1,8,25],[0]),([178,387,2,3,4,5],[17,24,15,22,25,34,78],[]),([178,388,2,3,4,5],[31,12,25,22],[]),([55,108,14,3,4,5],[22,25],[]),([389,2,3,4,5],[5,12],[]),([9,178,295,2,3,4,5],[26],[0]),([10,9,23,14,62,2,5],[89],[0]),([23,154,62,2,3,4,5],[1,105,92],[0]),([32,0,1,244,2,3,4],[67],[]),([374,154,2,3,4,5],[12,1,106],[0]),([178,2,390,3,4,5],[12,17,22,25],[]),([115,391,1,2,4,5],[15,8,51,25,52,13],[]),([23,154,2,17,3,5],[21,12],[0]),([32,55,19,53,2,3,4],[11],[0]),([178,2,3,150,4,5],[0,1,31,78],[]),([10,178,295,2,3,4,5],[0,15],[0]),([6,23,14,2,3,66],[12,107,108],[0]),([108,14,2,3,4,5,7],[22,21],[0]),([33,178,2,3,4],[78,15,26],[0]),([6,291,178,2,3,4,5],[22,5],[0]),([178,295,2,17,3,4,5],[0,15,8,17],[0]),([282,295,2,3,4,5],[17,8,31,15],[]),([23,14,2,225,3,4,5],[15,17],[0]),([345,227,23,0,1,4,5],[25,1],[0]),([305,295,2,4,5],[1,8,0,31],[0]),([78,1,14,2,3,87,5],[15],[]),([23,177,2,273,3,4,5],[15,87,78],[0]),([178,2,3,392,4,5],[0,1,31,78],[]),([0,1,288,273,3,4,5],[],[0]),([0,1,393,2,3,4,5],[69,44,72],[0]),([178,2,3,394,4,5],[0,8,31,25,22,78],[]),([6,277,178,2,3,4,5],[0,17,8,15],[0]),([275,23,177,2,3,4,5],[],[0]),([0,1,2,3,87,159,5],[],[0]),([178,2,17,3,20,5],[0,12],[0]),([10,9,178,2,3,5],[12,26],[0]),([9,178,2,308,3,4,5],[25,1],[0]),([23,14,62,2,3,4,43],[109,92],[0]),([169,0,1,2,3,4,34],[67,65],[0]),([277,285,2,3,4,5],[17,8,31,15],[]),([0,1,2,395,3,4,5],[72],[]),([204,208,0,2,3,4,5],[16],[0]),([23,0,1,2,3,195],[12,29,35,38,37,39],[0]),([277,2,3,302,4,5],[0,1,31],[0]),([0,1,2,138,3,8,7],[],[0]),([227,23,14,3,4,5],[1,21,93,25],[0]),([396,178,2,3,4,5],[8,24,15,22,25,34,78],[]),([397,0,1,3,91,4,5],[41],[]),([60,23,177,2,3,4,5],[15],[0]),([178,2,3,4,43],[12,26],[0]),([0,1,173,2,26,4,5],[75],[]),([178,398,3,4,5],[25,17],[0,1]),([178,2,308,17,3,4,5],[1,8,25],[0]),([178,2,3,399,4,5],[26,17,24,15,22,25,34,78],[]),([25,178,2,3,4,5],[26,15,78,17,8,22,25],[0]),([14,2,3,159,4,34],[12,79,110],[]),([10,9,55,23,14,2,5],[15],[0]),([0,1,177,2,400,4,5],[72],[0]),([6,178,309,2,3,4,5],[22,78,25],[0]),([178,309,2,3,8,4,5],[22,12,24,25],[0]),([0,1,401,2,3,4,5],[69,44,72,71],[]),([192,0,1,2,3,4,34],[],[0]),([23,14,2,17,3,43],[12,21,111],[0]),([32,178,2,3,4,5],[12,34,17,8,22,25],[]),([226,19,53,2,3,4,5],[15],[0]),([178,62,61,4,5],[1,25,0,31],[0]),([178,2,308,3,4,5,7],[25,1],[0]),([0,1,244,2,3,4,34],[67],[]),([32,192,0,1,2,3,4],[],[0]),([55,178,2,3,4,5,7],[15,25,78,22],[0,1]),([178,402,2,3,4,5],[0,8,22,25,78,34],[0]),([178,309,2,3,4,20,5],[8,22,15,17,25],[0]),([60,23,14,2,26,4,5],[15,21],[0]),([291,178,2,3,8,4,5],[22,5],[0]),([32,23,14,215,2,3,4],[107,98],[0]),([178,295,2,3,4,5,7],[8,15,78,17],[0,1]),([10,192,14,2,3,4,5],[],[0]),([277,2,302,4,5],[1,8,0,31],[0]),([0,1,2,403,3,4,5],[],[]),([192,14,2,17,3,4,5],[15,25,1],[0]),([32,19,53,62,2,3,4],[11],[0]),([6,24,19,53,62,2,3],[11],[0]),([178,2,188,3,4,5],[0,25,17,8,78,34],[0]),([78,1,276,2,17,3,5],[12],[]),([404,0,1,2,3,4,5],[],[]),([405,0,1,3,194,4,5],[112],[]),([10,277,178,2,3,4,5],[0,15],[0]),([178,2,406,3,4,5],[17,25,24,15,34,78],[]),([178,62,2,3,8,4,5],[0,12],[0]),([88,19,53,2,3,5],[12,29],[0]),([144,202,14,2,3,4,5],[40],[]),([23,174,2,3,4,5,7],[23,21],[0]),([10,178,2,308,3,4,5],[25,1],[0]),([407,178,2,3,4,5],[12,8,22,25],[]),([10,55,178,2,3,4,5],[0,15],[0]),([294,178,2,17,3,4,5],[24,17,15,8],[0]),([6,294,178,2,3,4,5],[17,24,8,15],[0]),([178,309,2,3,4,5,7],[8,22,15,17,25],[0]),([294,178,2,3,4,5,7],[15,78,25],[0,1]),([291,178,2,17,3,4,5],[22,5],[0]),([14,2,26,3,259,4,5],[15,78],[0]),([178,295,2,3,8,4,5],[0,12],[0]),([60,55,178,3,4,5],[0,1,31,25],[0]),([0,1,177,408,3,4,5],[113],[0]),([55,178,2,17,3,4,5],[0,15,25,22],[0]),([234,0,1,2,3,4,5],[],[]),([252,0,1,251,3,4,5],[],[0]),([227,23,0,1,4,5,7],[1,25,84,83],[0]),([10,9,19,53,119,2,5],[60],[0]),([24,178,2,17,3,5],[12,31],[0])]
def P_34_6_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [0,1,5,8,11,12,13,15,16,17,21,22,23,24,25,26,29,31,34,35,37,38,39,40,41,44,51,52,60,65,67,69,71,72,75,78,79,83,84,87,89,92,93,98,105,106,107,108,109,110,111,112,113]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_6_3 : checkNodesBT W_34 G_34 fmask_34 P_34_6_3 autos_34 bk_34_5 6 nd_34_6_3 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_6_3 : ∀ ns ∈ nd_34_6_3, Impossible G_34 6 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_5_ok chk_34_6_3
def nodes_34_6 : List NodeSpec := nd_34_6_0 ++ nd_34_6_1 ++ nd_34_6_2 ++ nd_34_6_3
def bk_34_6 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_6
set_option maxRecDepth 500000 in
lemma bk_34_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 6 xs.toFinset) bk_34_6 :=
  buildBucketsBT_of_mem (forall_append (forall_append (forall_append (mem_34_6_0) mem_34_6_1) mem_34_6_2) mem_34_6_3)
def nd_34_7_0 : List NodeSpec := [([0,1,2,3,195],[39,35],[0,3,2,4,5,6]),([196,0,1,2,3,87,5],[15,116,39,65,41,73,114,115],[0,2]),([0,1,2,3,87,197,5],[100,116,39,65,41,73,114,115],[0,2]),([78,0,1,2,3,87,5],[116,15,65,52,41,73,114,115],[0,2]),([89,0,1,2,3,187,4,5],[40,117,118],[]),([198,0,1,2,40,3,4,5],[120,40,119],[]),([0,1,2,3,91,166,4,5],[78,122,42,121,118],[]),([0,1,2,3,91,199,4,5],[123,121,42,40,39],[0]),([200,0,1,93,2,3,4,5],[5,70],[]),([0,1,201,93,2,3,4,5],[5,6,70],[]),([155,15,0,1,2,3],[35,20,39,57,41,74,73],[5,6]),([16,202,0,1,2,26,4,5],[41,125,124],[]),([16,0,1,2,26,203,4,5],[41,15,127,126,124],[]),([204,0,1,2,3,194,4,5],[42,40,48],[0]),([205,0,1,147,2,3,4,5],[12,118],[]),([0,1,206,147,2,3,4,5],[5,15,70],[]),([13,1,207,2,3,4,5],[35,8,52],[]),([208,0,1,2,3,194,4,5],[40,42,47],[0]),([209,115,1,2,3,4,5],[5,54,128,6],[0]),([18,1,2,194,4,5],[13,39],[5,6,0,2]),([115,1,2,4,5,7],[13,39,8,6,51,25],[0,2,5,6]),([155,18,0,1,2,3],[12,39,57,41,74,73],[5,6]),([47,115,1,2,4,5],[5,12],[0]),([115,1,2,4,44,5],[1,12],[0]),([115,1,2,4,210,5],[12,39,8,6,51,25],[0,2,5,6]),([115,211,1,2,4,5],[5,53,129,1,15,13],[0,1]),([212,115,1,2,4,5],[1,58,130,8,15,13],[0,1]),([19,1,2,26,3,85,4,5],[124,15,78],[0]),([0,1,2,26,3,213,4,5],[15,78],[0]),([155,19,0,1,2,3],[12,57,56,74,73,13],[0]),([19,0,1,2,26,3,8],[12,56,41,13,82,104,73],[0]),([9,19,0,1,2,71,5],[12,116,39,29,101,37,131],[0]),([74,19,0,1,2,3,7],[12,134,29,85,37,133],[0]),([212,115,1,2,3,4,5],[1,58,130,8,13],[0]),([9,0,1,214,2,3,4,5],[135,25,70],[0]),([19,0,1,2,17,3,87,5],[12,67,136],[0]),([86,19,0,1,2,3,5],[15,56,41,99,52,137,73,65],[0]),([32,19,0,1,215,2,3,4],[139,13,138,140],[0]),([88,19,0,1,2,3,5],[12,116,39,29,94,37,141],[0]),([129,32,19,0,1,2,3,4],[37,12,142],[0]),([32,19,0,1,2,3,130,4],[142,12,143],[0]),([0,1,216,2,17,3,4,5],[25,67,23,70],[0]),([24,19,1,2,17,3,80,5],[12],[0]),([32,0,1,2,3,127,4,5],[118,65],[]),([32,19,1,2,3,80,4],[145,98,13,144,67,29],[]),([0,1,2,3,127,4,34],[12,132,146,147,88],[]),([129,0,1,2,3,127,4,5],[70,148],[]),([0,1,2,40,3,127,4,5],[15,118,78,132],[]),([19,0,1,2,3,217,4,5],[73,15,8,149],[0]),([19,0,1,2,3,218,4,5],[15,8,150,146],[0]),([219,0,1,2,3,91,4,5],[151,40,39,42],[0]),([0,1,2,137,40,3,4,5],[8,15,22,132],[]),([6,24,55,19,0,1,2,3],[15,13,80,56],[0]),([55,19,0,1,2,3,8,7],[12,56,13,96],[0]),([33,55,19,0,1,2,3,4],[15,13,97,152],[0]),([55,19,0,1,2,3,4,43],[15,13,109,152],[0]),([19,0,1,2,188,3,5,7],[132],[0]),([0,1,220,93,2,3,4,5],[154,5,6,153,124],[0]),([6,118,0,1,2,3,4,5],[25,8,22],[0]),([118,0,1,2,3,4,5,7],[25,8,22],[0]),([0,1,221,147,2,3,4,5],[12,39,118],[]),([118,0,1,2,3,8,4,5],[25,67,65,22],[0]),([9,118,0,1,2,3,4,5],[22,25,73,67],[0]),([10,118,0,1,2,3,4,5],[25,22],[0]),([118,0,1,2,17,3,4,5],[25,22],[0]),([118,0,1,49,3,4,5],[22,25,155,71],[]),([60,19,0,1,2,26,4,5],[73,56,15,156],[0]),([60,118,0,1,3,4,5],[22,25,157,155],[]),([60,55,19,0,1,4,5,7],[22,5,56],[0]),([19,0,1,2,3,222,4,5],[8,44,42,158,73,56],[0]),([19,0,1,2,3,130,4,34],[147,78,37],[0]),([0,1,181,2,3,4,5,7],[8,25,22,56],[]),([19,0,1,223,2,3,4,5],[44,8],[0]),([25,19,0,1,62,2,4,5],[25,13,41],[0]),([19,0,1,62,2,26,4,5],[41,25,124],[0]),([89,0,1,2,3,91,4,5],[40,117,118],[]),([224,19,0,1,2,3,4,5],[8,42],[0]),([19,0,1,62,2,3,8,7],[159,56,12,13,41],[0]),([19,0,1,2,225,3,4,5],[15,8],[0]),([19,0,1,62,2,3,4,43],[160,13,41,152],[0]),([226,19,0,1,2,3,4,5],[8,42,15],[0]),([19,0,1,62,2,3,4,34],[161,56,12,124,122],[0]),([227,19,0,1,4,5],[5,22,56,136],[0,1]),([170,19,0,1,2,3,5,7],[132],[0]),([6,0,1,2,146,3,4,5],[8,22,25],[0]),([0,1,2,146,3,4,5,7],[22,8,25],[0]),([0,1,2,146,3,8,4,5],[22,65,67,25],[0]),([10,0,1,2,146,3,4,5],[25,22],[0]),([0,1,2,146,3,4,20,5],[25,8,22],[0]),([9,86,19,0,1,2,5],[15,56,41,90,52,162,73,65],[0]),([19,53,2,71,3,4,5],[12,11,122,22,25],[0]),([209,115,1,2,4,5],[5,54,128,1,15,13],[0,1]),([19,53,2,3,27,4,5],[12,63,122,22,25],[0]),([6,9,19,53,2,3,5],[11,12,29],[0]),([19,53,2,3,66,4,5],[62,12,29,22,25],[0]),([9,19,53,119,2,3,4,5],[60,25],[0]),([9,19,53,2,111,3,4,5],[60,22],[0]),([10,9,19,53,2,5],[12,41,60],[0]),([19,53,2,17,3,4,5],[12,60,41,22,25],[0,1]),([167,19,53,3,4,5],[12,23],[0]),([19,53,139,3,4,5],[12,41,22],[0]),([55,19,0,1,2,3,4,34],[12,56,124,88],[0]),([24,19,53,2,17,3,5],[12,62,41],[0]),([9,0,1,2,146,3,4,5],[22,25,116,67],[0]),([32,19,53,2,17,3,4,5],[62,12],[0]),([32,19,53,2,3,4,5],[12,59,29,22,25],[0]),([32,19,53,2,17,3,4],[60,12,98,62,145],[0]),([19,53,2,3,4,34],[12,122,11],[0]),([23,0,1,62,2,26,4,5],[15,41,73,25,156],[0]),([10,169,0,1,2,3,4,5],[39,71],[0]),([9,19,53,2,3,4,5],[12,103,22,25],[0]),([33,19,0,1,62,2,3,4],[163,13,41,152],[0]),([58,64,23,14,3,5],[12,22,25],[]),([64,19,53,2,40,3,4,5],[60,59,15],[0]),([19,53,148,2,3,4,5],[25,23,60,15,78,59],[0]),([131,228,0,1,2,3,4,5],[40,6,25,70],[5]),([19,53,2,153,3,4,5],[12,22,41],[0]),([189,19,53,2,3,4,5],[12,23],[0]),([9,23,14,62,2,3,4,5],[92,164],[0]),([19,53,49,2,40,3,4,5],[60,59,15],[0]),([0,1,2,157,40,3,4,5],[118,17,64,15,165],[0]),([136,19,53,2,3,4,5],[62,12,51],[0]),([170,19,53,2,3,4,5],[11,22,51,78,59],[0]),([6,55,19,53,2,3,4,5],[11,25,22,15],[0]),([55,19,53,2,3,4,5,7],[15,25,78,22],[0,1]),([45,115,1,2,4,5],[1,39,52,8,69],[]),([9,0,1,229,2,3,4,5],[67,23,70],[0]),([55,19,53,2,3,4,20,5],[5,30,22,63],[0]),([55,19,53,2,17,3,4,5],[11,15,25,22],[0]),([227,0,1,14,4,5],[23,22,75,166,73,13],[0,1]),([60,55,19,53,4,5],[22,23,11,62],[0]),([25,19,53,2,3,4,5],[63,15,41,78,22,25],[0]),([19,53,2,3,150,4,5],[11,22,51,62,78],[0]),([19,53,2,3,113,4,5],[12,22,41],[0]),([60,55,19,53,3,4,5],[11,25,23,62],[0]),([10,23,14,62,2,3,4,5],[21,15,167],[0]),([23,14,2,17,3,4,5],[12,79,168,17,25,22],[0,1]),([19,53,2,3,61,4,5,7],[11,15],[0]),([19,53,62,2,3,4,5,7],[15,22,78,25],[0,1]),([19,53,62,3,61,4,5],[11,22,23,62],[0])]
def P_34_7_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [1,5,6,8,11,12,13,15,17,20,21,22,23,25,29,30,35,37,39,40,41,42,44,47,48,51,52,53,54,56,57,58,59,60,62,63,64,65,67,69,70,71,73,74,75,78,79,80,82,85,88,90,92,94,96,97,98,99,100,101,103,104,109,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_7_0 : checkNodesBT W_34 G_34 fmask_34 P_34_7_0 autos_34 bk_34_6 7 nd_34_7_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_7_0 : ∀ ns ∈ nd_34_7_0, Impossible G_34 7 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_6_ok chk_34_7_0
def nd_34_7_1 : List NodeSpec := [([9,23,14,2,3,4,5],[12,103,22,25],[0]),([19,53,62,61,4,5],[22,23,11,62],[0]),([0,1,2,230,3,4,5],[116,22,44,69,118,64],[]),([32,0,1,2,3,159,4,5],[118,65],[0]),([9,19,53,2,17,3,5],[62,15,60,169,103],[0]),([0,1,2,3,194,231,4,5],[49,13,87,15,42,40],[0]),([232,0,1,128,2,3,4,5],[70,72],[0]),([0,1,128,2,233,3,4,5],[12,171,72,70,170],[0]),([234,0,1,2,26,3,4,5],[172,173,39,69],[0]),([19,53,2,17,3,8,5],[12,11,29],[0]),([14,2,17,3,159,4,5],[21,174,12,1],[0]),([234,0,1,2,3,4,5],[44,69,64,40,71,70,72,67,118],[0]),([144,1,14,2,26,3,4,5],[124,15,6,78,69],[0]),([14,2,157,3,4,5],[22,12,17,21],[0]),([0,1,177,2,3,235,4,5],[15,87,175,78,113,124],[0]),([0,236,1,2,3,194,4,5],[13,15,42,40,50],[0]),([155,0,1,14,2,3],[20,176,57,75,73,74,13],[0]),([0,1,14,2,26,3,8],[75,82,177,176,13,73,104],[0,3]),([23,14,2,3,113,4,5],[12,22],[0]),([9,0,1,14,2,71,5],[12,29,116,39,37,52,131],[0]),([6,23,14,62,2,3,4,5],[1,21,25,171,15],[0]),([6,0,1,14,2,3,66],[108,178,179,29,12,37,13,39,180],[0]),([32,23,14,2,3,4],[12,98,93,140,79],[0]),([60,0,1,177,2,3,4,5],[70,113,87,15,175,41,72,124],[0]),([237,0,1,2,3,4,5],[166,64,67,70,72,44,69],[]),([10,19,53,62,2,3,4,5],[11,15],[0]),([60,19,53,2,3,4,5,7],[11,15],[0]),([0,1,238,177,2,3,4,5],[41,78,113,124],[0,1]),([19,53,2,135,3,4,5],[12,62,23],[0]),([74,0,1,14,2,3,7],[85,181,178,12,29,35,37,133],[0]),([144,0,1,2,26,3,8],[12,13,182,41,73,177,104],[0,2]),([0,1,128,62,2,3,4,5],[70,72,75],[0]),([9,239,0,1,2,3,4,5],[67,22,72],[0]),([0,1,2,153,3,240,4,5],[44],[]),([74,19,53,2,3,4,5],[12,60,29,59,22,25],[0]),([10,9,0,1,14,119,2,5],[116,170,73,89,183],[0]),([19,53,2,3,132,4,5],[25,63,23,60,15,78,59],[0]),([241,0,1,154,2,3,4,5],[73,15,91,184,72],[0]),([0,1,14,2,17,3,87,5],[100,176,116,166,114],[0,3]),([0,1,2,3,187,166,4,5],[15,185,122,42,118],[]),([0,1,14,2,17,3,43],[75,111,176,15,41,73,186],[0]),([32,0,1,14,215,2,3,4],[13,179,98],[0]),([242,0,1,2,3,4,5],[69,67,65,118,44,70,72],[]),([10,9,19,0,1,2,111,5],[15,116,89],[0]),([9,19,53,2,3,5,7],[62,12,41],[0]),([129,0,1,14,2,3,4,34],[146,88,147,67,116],[0]),([19,53,2,182,3,4,5],[12,23],[0]),([32,0,1,14,2,243,3,4],[98,139,13,145,140],[0]),([192,0,1,2,3,4,5,7],[17,25,84],[0]),([0,1,14,2,3,130,4,34],[147,37,88,67],[0]),([0,1,244,2,17,3,4,5],[23,67,19,25,84,70],[0]),([0,1,14,62,2,26,4,5],[73,13,25,156,39,52],[0]),([158,32,0,1,2,3,4,5],[118,65],[]),([23,14,62,2,17,3,4,5],[1,25,21,15,187],[0]),([158,0,1,2,3,4,34],[81,170,88,146,147,78],[]),([158,0,1,2,3,245,4,5],[81,118,170],[]),([246,158,0,1,2,3,4,5],[81,118],[]),([0,1,247,154,2,3,4,5],[73,72],[0]),([158,0,1,248,2,3,4,5],[72,70,187,188,189,190],[0]),([249,158,0,1,2,3,4,5],[70,72],[0]),([250,1,14,2,153,3,4,5],[6,124,15,69],[0]),([158,0,1,2,251,3,4,5],[187,81,72,70,170],[0]),([10,9,55,19,0,1,2,5],[15,124,89],[0]),([32,19,53,2,3,4],[12,98,62,145,60],[0]),([252,158,0,1,2,3,4,5],[72,70],[0]),([78,120,14,2,3,4,5],[192,191,193,194,124,67],[]),([0,1,14,2,3,218,4,5],[69,15,42,40,39,116,195,146],[0]),([0,1,253,2,3,4,5],[51,22,67,71,118,64,196],[0]),([23,14,139,3,4,5],[12,22],[0]),([0,1,14,2,225,3,4,5],[69,15,42,116,40,73,197],[0]),([165,0,1,2,40,3,4,5],[22,5,118,30,198,170],[0]),([9,192,0,1,2,3,4,5],[73,67],[0]),([55,0,1,128,2,3,4,5],[72,75,12,70],[0]),([129,19,0,1,2,3,4,34],[146,78,147],[0]),([0,1,14,2,254,3,4,5],[13,73,69,158,199,200],[0]),([32,19,0,1,2,243,3,4],[12,13,98],[0]),([55,0,1,14,2,3,8,7],[96,75,201,12,37,159,41],[0]),([33,55,0,1,14,2,3,4],[97,202,163,15,41,73,196],[0]),([23,94,2,3,4,5],[12,22],[]),([55,0,1,14,2,3,4,43],[109,203,160,15,41,73,196],[0]),([18,0,1,2,26,8],[13,39,15,41,73],[5,6]),([255,0,1,177,2,3,4,5],[70,72],[0]),([32,0,1,14,2,3,130,4],[204,142],[0]),([55,0,1,154,2,3,4,5],[91,196,72,184,15,41,70],[0]),([144,202,0,1,2,3,4,5],[40,205,44,126],[0]),([10,9,19,53,2,3,5],[12,63,41],[0]),([55,19,53,49,3,4,5],[22,23,62,15],[0]),([32,55,0,1,14,2,3,4],[98,142,139,145,140,143,75],[0]),([23,14,62,2,3,8,4,5],[21,12,206],[0]),([165,55,0,1,3,4,5],[23,52,22],[]),([78,32,1,14,2,3,4],[145,98,13,140,207,67],[]),([0,1,14,2,188,3,5,7],[116,170,13,208],[0]),([6,24,55,0,1,14,2,3],[80,210,209,15,41,73,75],[0]),([10,9,55,0,1,14,2,5],[89,183,211,15,41,73],[0]),([0,1,160,2,3,4,5,7],[71,23,64,67,118,22],[0]),([0,1,160,2,3,8,4,5],[67,65],[0]),([9,0,1,160,2,3,4,5],[67,73],[0]),([0,1,160,2,17,3,4,5],[67,23,22,71],[0]),([6,24,23,14,2,3],[78,15,80,21],[0]),([60,0,1,14,2,26,4,5],[75,13,73,52,15,41],[0]),([55,0,1,173,3,4,5],[23,22,39,52],[]),([6,24,0,1,14,62,2,3],[13,75,73,80,210],[0]),([10,9,0,1,14,2,111,5],[89,183,211,15,41,73],[0]),([25,0,1,14,62,2,4,5],[13,73,113,25,212],[0]),([0,1,177,62,2,3,4,5],[70,124,72,113],[0]),([33,0,1,14,62,2,3,4],[13,196,73,97,202],[0]),([0,1,154,62,2,3,4,5],[105,196,70,72],[0]),([0,1,14,62,2,3,4,34],[116,75,146,88,147,12],[0]),([158,0,1,62,2,3,4,5],[23,70,75],[]),([0,1,2,146,17,3,4,5],[25,22,8],[0]),([256,0,1,49,2,3,4,5],[67,71,185,213,117,214],[0]),([23,0,1,2,17,3,87,5],[12,67,215],[0]),([6,169,0,1,2,3,4,5],[22,67,5,30,71],[0]),([10,55,23,14,2,3,4,5],[21,15],[0]),([9,86,0,1,14,2,5],[75,15,41,52,73,162,65],[0]),([0,257,1,2,3,91,4,5],[116,41,78,42,39],[0]),([169,0,1,2,3,8,4,5],[67,65],[0]),([9,169,0,1,2,3,4,5],[67,116],[0]),([115,54,1,2,4,5],[5,39,52,1,69],[]),([0,1,2,258,3,4,5],[22,69,64,72,44,124,113],[]),([0,1,63,2,132,4,5],[23,116,42],[]),([0,1,2,26,3,259,4,5],[15,78],[0]),([10,9,23,0,1,119,2,5],[15,73,41,165,183,89,211],[0]),([9,86,23,0,1,2,5],[15,83,41,52,162,73,65],[0]),([178,2,3,4,20,5],[12,26,17,8,22,25],[0]),([260,0,1,177,2,3,4,5],[72,70],[0]),([178,2,3,8,4,5],[12,0,17,8,22,25],[0,1]),([23,14,2,26,3,4,5],[15,78,126,93,21,25,22,17],[0]),([224,0,1,14,2,3,4,5],[13,73,69,216,217],[0]),([23,0,1,2,17,3,43],[12,83,41,186,73],[0]),([158,129,0,1,2,3,4,5],[218,148,70],[]),([227,0,1,14,3,4,5],[30,75,166,5,13],[0]),([23,14,2,3,132,4,5],[92,25,23,79,15,17,78,107],[0]),([32,23,0,1,215,2,3,4],[12,37,29,219,142,98,139],[0]),([158,32,0,1,2,3,4],[98,37,67,145,142],[]),([18,0,1,2,261,3,4,5],[44,1],[0]),([262,0,1,2,17,3,4,5],[220,67,72,71],[0]),([12,1,263,2,3,4,5],[35,221,8],[]),([32,0,1,2,3,127,4],[12,39,222,65,37,142,98,118],[]),([23,0,1,2,3,130,4,34],[147,78,37],[0])]
def P_34_7_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [0,1,5,6,8,11,12,13,15,17,19,20,21,22,23,25,26,29,30,35,37,39,40,41,42,44,49,50,51,52,57,59,60,62,63,64,65,67,69,70,71,72,73,74,75,78,79,80,81,82,83,84,85,87,88,89,91,92,93,96,97,98,100,103,104,105,107,108,109,111,113,114,116,117,118,122,124,126,131,133,139,140,142,143,145,146,147,148,156,158,159,160,162,163,165,166,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_7_1 : checkNodesBT W_34 G_34 fmask_34 P_34_7_1 autos_34 bk_34_6 7 nd_34_7_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_7_1 : ∀ ns ∈ nd_34_7_1, Impossible G_34 7 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_6_ok chk_34_7_1
def nd_34_7_2 : List NodeSpec := [([6,24,55,23,0,1,2,3],[210,15,73,83],[0]),([19,0,1,2,254,3,4,5],[44,8],[0]),([264,0,1,2,17,3,4,5],[67,25,70],[0]),([9,19,0,1,2,3,34],[12,116,39,29,95,37,223],[0]),([0,1,2,3,159,4,34],[12,29,146,147,165],[0]),([0,1,2,40,3,159,4,5],[15,65,78,165],[0]),([0,1,2,182,3,265,4,5],[40],[]),([19,53,2,17,40,3,4,5],[12,11,59],[0]),([266,0,1,177,2,3,4,5],[124,113],[0]),([23,0,1,2,3,218,4,5],[15,17],[0]),([78,1,14,2,3,4,34],[12,88,170,122,224,124],[]),([19,53,62,2,3,4,20,5],[5,30,22,63],[0]),([267,23,0,1,2,3,4,5],[40,17,225,146],[0]),([33,55,23,0,1,2,3,4],[202,15,73,226],[0]),([55,23,0,1,2,3,4,43],[203,15,73,226],[0]),([55,0,1,157,3,4,5],[25,52,22,15],[0]),([115,1,268,2,3,4,5],[1,77,227,8],[0]),([129,32,0,1,14,2,3,4],[37,98,142,67],[0]),([169,23,2,3,4,5],[1],[0,1]),([23,174,2,3,4,5],[25,23,21,93],[0]),([19,1,2,3,80,4,34],[12,88,132,228,124,122],[]),([23,0,1,2,188,3,5,7],[165],[0]),([9,19,53,62,2,3,4,5],[63],[0]),([19,0,1,62,61,4,5,7],[5,22,56],[0]),([0,1,14,2,3,269,4,5],[73,75,13,69,52],[0]),([270,0,1,2,182,3,4,5],[69,72,39],[]),([9,0,1,2,271,3,4,5],[67,116],[0]),([272,0,1,128,2,3,4,5],[78,171,229,72,70],[0]),([10,192,0,1,2,3,4,5],[71,39],[0]),([0,1,177,2,273,3,4,5],[15,87,175,78,72,70],[0]),([23,14,2,3,27,4,5],[12,92,230,22,25],[0]),([226,0,1,14,2,3,4,5],[73,69,15,231],[0]),([0,1,14,62,2,3,4,43],[13,196,73,109,203],[0]),([192,0,1,2,3,4,20,5],[1,25,84],[0]),([10,55,19,53,2,3,4,5],[11,15],[0]),([192,0,1,2,17,3,4,5],[25,1],[0]),([19,0,1,2,17,3,43],[12,56,41,111,186,73],[0]),([10,9,19,0,1,62,2,5],[211,124,41],[0]),([60,23,0,1,2,26,4,5],[15,83],[0]),([23,0,1,2,3,269,4,5],[40,17,83],[0]),([60,55,23,0,1,4,5,7],[1,25,84,83],[0]),([108,0,1,2,3,4,5,7],[17,71,83,64,118,25,84],[0]),([25,23,14,2,3,4,5],[92,15,232,78,22,25],[0]),([24,0,1,2,17,3,127,5],[12],[0]),([24,0,1,2,17,3,159,5],[12],[0]),([55,108,0,1,3,4,5],[25,84,39,52,22],[0]),([19,53,2,17,3,20,5],[12,11,41],[0]),([274,0,1,2,3,4,5],[166,64,72,67,44,69],[]),([33,19,53,2,3,4],[15,41,78,63],[0]),([23,0,1,2,3,222,4,5],[17,40,44,83],[0]),([23,0,1,223,2,3,4,5],[40,17,233,73],[0]),([0,1,2,138,17,3,4,5],[25,67,15,22],[0]),([224,23,0,1,2,3,4,5],[17,40,44],[0]),([19,53,2,3,8,7],[12,41,11],[0]),([275,0,1,177,2,3,4,5],[113,124],[0]),([115,1,268,2,4,5],[1,77,227,8,15,13],[0,1]),([23,0,1,62,2,3,4,43],[15,73,41,203,109,160,226],[0]),([178,2,17,3,4,5],[12,0,17,8,22,25],[0,1]),([23,0,1,62,2,3,8,7],[12,73,83,41,201,96,159],[0]),([0,1,276,2,17,3,5],[176,166,234,235],[0,3]),([277,178,2,3,4,5],[1,8,15,78],[0,1]),([23,0,1,2,254,3,4,5],[40,17],[0]),([33,23,0,1,62,2,3,4],[15,73,41,202,97,163,226],[0]),([0,1,14,223,2,3,4,5],[13,69],[0]),([0,1,14,2,3,222,4,5],[69,75,42,44,40,73,52,13],[0]),([169,0,1,2,17,3,4,5],[30,5,22,67,71],[0]),([6,24,19,53,2,3],[78,41,11],[0]),([23,0,1,62,2,3,4,34],[12,146,83,122,147,88,161],[0]),([226,23,0,1,2,3,4,5],[17,15,40,73,231],[0]),([9,0,1,14,2,3,34],[95,176,170,116,12,29,39,37,223],[0]),([0,1,2,278,3,4,5],[116,22,69,44,118,64],[]),([0,1,279,2,3,4,5],[196,72,67,70,71,118,64,44,69],[]),([32,23,0,1,62,2,3,4],[12,37,29,142,98,139,83],[0]),([163,14,2,3,4,5],[1,12],[]),([227,23,0,1,3,4,5],[1,25,83,215,84],[0]),([19,0,1,2,3,87,5],[12,56,116,100,41,115,73],[0]),([10,9,55,23,0,1,2,5],[183,15,73],[0]),([23,0,1,62,61,4,5,7],[25,1,84,83],[0]),([280,0,1,2,3,4,5],[124,70,44,40,67,71,118,64],[]),([55,0,1,14,2,3,4,34],[88,75,147,12,161,116,122,146],[0]),([6,0,1,2,138,3,4,5],[64,17,25,22],[0]),([9,0,1,2,138,3,4,5],[116,67],[0]),([0,1,147,107,2,3,4,5],[70,6,8],[0]),([32,23,0,1,2,243,3,4],[142,12,143],[0]),([6,192,0,1,2,3,4,5],[25,1],[0]),([9,55,19,53,2,3,4,5],[63],[0]),([0,1,160,2,3,4,20,5],[23,22,25,84,71],[0]),([9,0,1,2,281,3,4,5],[22,5],[0]),([0,1,174,62,4,5],[22,23,75,166],[0]),([10,0,1,2,138,3,4,5],[71,39],[0]),([23,14,2,17,3,8,5],[12,21,236],[0]),([23,0,1,2,225,3,4,5],[15,17,197,73],[0]),([170,0,1,14,2,3,5,7],[170,73,237,13],[0]),([55,19,53,2,3,8,4,5],[11,12],[0]),([24,158,0,1,2,17,3,5],[81,52],[0]),([158,0,1,2,3,130,4,5],[72,73],[]),([282,178,2,3,4,5],[1,12,0,8],[0]),([23,14,2,17,3,20,5],[21,12,238],[0]),([0,1,2,138,3,4,20,5],[25,17,84,22],[0]),([23,14,2,71,3,4,5],[12,21,239,22,25],[0]),([25,23,0,1,62,2,4,5],[15,41,73,25,212],[0]),([64,178,2,3,4,5],[5,12,0,22],[0]),([74,23,0,1,2,3,7],[12,240,29,37,133],[0]),([24,23,14,2,17,3,5],[12,93,234],[0]),([23,14,2,3,8,7],[12,96,21],[0]),([9,23,14,2,111,3,4,5],[79,22,15],[0]),([6,9,23,14,2,3,5],[21,12,241],[0]),([32,55,23,0,1,2,3,4],[142,12,143,83],[0]),([9,23,14,2,3,5,7],[12,93,242],[0]),([0,1,174,62,3,4,5],[23,75,22,166],[0]),([58,178,2,3,4,5],[12,1],[0]),([10,9,23,14,2,5],[12,89,79],[0]),([283,0,1,2,17,3,4,5],[243,8],[0]),([23,14,2,17,40,3,4,5],[12,21,107],[0,1]),([0,1,173,2,3,4,5,7],[64,75,22],[0]),([23,0,1,2,3,217,4,5],[15,17],[0]),([284,0,1,93,2,3,4,5],[154,124],[]),([178,285,2,3,4,5],[5,12,0,1],[0]),([60,23,14,2,3,4,5,7],[21,15,22],[0]),([167,23,14,3,4,5],[12,23],[0]),([78,32,1,14,2,3,4,5],[13,12],[]),([55,23,14,2,17,3,4,5],[15,21,25,1],[0]),([23,154,2,3,4,5],[12,92,91],[0]),([178,49,2,3,4,5],[1,12,0,25],[0]),([227,23,0,1,4,5],[1,25,83,215,84],[0,1]),([6,19,53,62,2,3,4,5],[11,22,25,15],[0]),([23,14,2,17,3,4,34],[12,79,88],[0,1]),([23,14,2,3,4,43],[12,109,92],[0]),([189,23,14,2,3,4,5],[12,23],[0]),([0,1,154,2,286,3,4,5],[166,91,12,25,184,84,70],[0]),([169,0,1,2,3,4,5,7],[71,22,64,67,118,23],[0]),([32,23,14,2,17,3,4],[79,12,98,140,93],[0]),([178,2,3,61,4,5],[5,0,31,22,15,78],[0,1]),([23,177,2,3,4,5],[15,78],[0]),([23,14,2,3,104,4,5],[1,92,79,15,78,107],[0]),([64,19,53,62,3,4,5],[25,22,23,62,15],[0]),([129,19,53,2,17,3,4,5],[60,25],[0]),([23,14,2,81,3,4,5],[79,12,244,17,25,22],[0,1]),([32,19,1,2,3,80,4,5],[13],[]),([0,1,14,2,3,217,4,5],[37,69,245,15],[0])]
def P_34_7_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [0,1,5,6,8,11,12,13,15,17,21,22,23,25,29,30,31,37,39,40,41,42,44,52,56,59,60,62,63,64,65,67,69,70,71,72,73,75,77,78,79,81,83,84,87,88,89,91,92,93,95,96,97,98,100,107,109,111,113,115,116,118,122,124,132,133,139,140,142,143,146,147,154,159,160,161,163,165,166,170,171,175,176,183,184,186,196,197,201,202,203,210,211,212,215,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_7_2 : checkNodesBT W_34 G_34 fmask_34 P_34_7_2 autos_34 bk_34_6 7 nd_34_7_2 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_7_2 : ∀ ns ∈ nd_34_7_2, Impossible G_34 7 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_6_ok chk_34_7_2
def nd_34_7_3 : List NodeSpec := [([129,32,23,0,1,2,3,4],[37,12,142],[0]),([190,0,1,2,3,4,5,7],[17,25,84,83],[]),([33,23,14,2,3,4],[15,97,78,92],[0]),([129,23,14,2,17,3,4,5],[1,79,25,220],[0]),([64,23,14,62,3,4,5],[22,25,93,15],[0]),([32,23,14,2,3,4,5],[12,107,98,22,25],[0]),([180,14,2,3,4,5],[1,12],[0]),([19,53,2,3,4,43],[12,41,63],[0]),([19,53,2,3,141,4,5],[11,25,23,62,78],[0]),([192,0,1,2,3,8,4,5],[67,65],[0]),([23,14,2,17,3,130,4,5],[25,79,22],[0]),([158,55,0,1,2,3,4,5],[72,22,75,246],[]),([32,23,14,2,17,3,4,5],[12,93],[0]),([6,24,19,0,1,62,2,3],[209,13,41,56],[0]),([287,0,1,128,2,3,4,5],[75,124],[]),([19,0,1,2,3,269,4,5],[73,44,8,247,56],[0]),([60,55,0,1,14,4,5,7],[73,75,13,22,52],[0]),([129,23,0,1,2,3,4,34],[146,78,147],[0]),([64,23,14,2,40,3,4,5],[25,12,79,107,1],[0]),([23,14,49,2,40,3,4,5],[1,15,79,107,78],[0]),([88,0,1,14,2,3,5],[12,29,116,39,37,141,118],[0]),([23,14,148,2,3,4,5],[23,25,79,15,78,107],[0]),([55,23,0,1,2,3,4,34],[12,147,83,146],[0]),([23,14,2,182,3,4,5],[12,23],[0]),([23,14,62,61,4,5],[22,25,21,93],[0]),([6,23,0,1,2,3,66],[12,219,29,37,39,13,180],[0]),([6,178,2,3,4,5],[12,0,17,8,25,22],[0,1]),([140,0,1,2,3,4,5,7],[22,8,56],[0]),([23,14,2,153,3,4,5],[1,12],[0]),([0,1,288,177,2,3,4,5],[41,15,72,70],[0]),([9,289,0,1,2,3,4,5],[67,25,70],[0]),([23,14,2,3,66,4,5],[93,12,248,17,25,22],[0]),([178,2,3,4,69,5],[5,12],[0]),([23,14,2,135,3,4,5],[93,12,23,17],[0]),([10,9,0,1,14,62,2,5],[116,73,89,113,183],[0]),([0,1,177,2,3,61,4,5],[72,70],[0]),([55,23,14,2,3,4,20,5],[1,25,15,92],[0]),([184,14,2,3,4,5],[12,23],[]),([19,53,62,2,3,8,4,5],[11,12],[0]),([86,0,1,14,2,3,5],[75,15,41,52,73,137,65],[0]),([0,1,14,62,2,3,8,7],[37,75,13,96,201,12],[0]),([0,290,1,2,40,3,4,5],[249,42,41],[]),([291,178,2,3,4,5],[5,22],[0,1]),([292,0,1,2,153,3,4,5],[69],[]),([136,23,14,2,3,4,5],[93,12,22],[0]),([170,23,0,1,2,3,5,7],[1,165],[0]),([86,23,0,1,2,3,5],[15,83,41,52,137,73,65],[0]),([88,23,0,1,2,3,5],[12,29,116,39,37,141],[0]),([293,0,1,2,3,91,4,5],[41,42],[0]),([10,178,2,3,4,5],[12,0,8,17,25,22],[0]),([32,0,1,2,3,159,4],[140,12,67,37,142,102],[0]),([143,23,14,2,3,4,5],[1,79,15,78,107],[0]),([10,9,23,0,1,62,2,5],[15,73,41,183,89,211],[0]),([32,0,1,14,62,2,3,4],[124,75,37,98,142],[0]),([6,19,0,1,2,3,66],[12,138,29,108,37,39,13,180],[0]),([23,14,2,3,4,34],[12,88,21],[0]),([0,1,154,2,17,3,5],[75,176,238,15,41],[0]),([9,23,0,1,2,3,34],[12,29,116,39,37,223],[0]),([55,23,0,1,2,3,8,7],[12,201,83,73],[0]),([78,129,1,14,2,3,4,5],[220,6,251,67],[0]),([6,55,23,14,2,3,4,5],[25,21,1,15],[0]),([55,23,14,2,3,4,5,7],[15,25,22,78],[0,1]),([0,1,14,62,61,4,5,7],[75,73,13,52,22],[0]),([23,0,1,2,26,3,8],[12,83,41,13,104,73],[0]),([53,125,2,3,4,5],[5,12],[0]),([169,0,1,2,3,4,20,5],[30,5,22,71],[0]),([32,55,19,0,1,2,3,4],[12,124,98,56],[0]),([9,55,23,14,2,3,4,5],[92,15],[0]),([227,19,0,1,3,4,5],[5,22,56,136,25],[0]),([0,1,14,2,3,87,5],[100,176,114,75,116,52,73,115],[0,3]),([9,23,0,1,2,71,5],[12,29,116,39,37,131],[0]),([55,23,14,49,3,4,5],[22,25,93,15],[0]),([23,14,2,188,3,4,5],[21,23,25,78,107],[0]),([19,53,2,3,104,4,5],[22,63,51,60,15,78,59],[0]),([192,14,2,3,4,5],[23,25],[0,1]),([0,1,2,26,3,85,8],[13,82,252,253,41,73,177,104],[0,2]),([6,24,23,0,1,62,2,3],[15,73,41,210,80,209,83],[0]),([23,14,2,3,150,4,5],[1,21,93,78],[0]),([23,14,62,2,3,4,20,5],[1,25,91,92],[0]),([294,178,2,3,4,5],[25,17,15,78],[0,1]),([178,295,2,3,4,5],[5,1,15,78],[0,1]),([19,53,2,17,3,4,34],[12,60,29],[0,1]),([19,53,2,188,3,4,5],[11,25,23,78,59],[0]),([115,211,1,2,3,4,5],[5,53,129,6,13],[0]),([158,0,1,2,3,4,5],[69,67,44,71,70,72,118,64],[]),([23,14,62,3,61,4,5],[21,22,25,93],[0]),([0,1,296,128,2,3,4,5],[75,12,124],[]),([297,0,1,154,2,3,4,5],[25,84,70],[0]),([55,23,14,2,3,8,4,5],[21,12],[0]),([32,23,0,1,2,3,130,4],[142,12,143],[0]),([23,14,2,3,141,4,5],[21,25,23,93,17,78],[0]),([14,2,3,159,4,5],[1,12,21],[0]),([0,1,298,2,17,3,4,5],[51,67,22,72],[0,3]),([299,0,1,2,3,4,5],[75,71,72,118,64,44,69],[]),([10,9,19,0,1,119,2,5],[211,73,132,41],[0]),([178,2,3,4,5,7],[15,78,17,8,22,25],[0,1]),([108,14,2,3,4,5],[22,17,21,93],[0]),([0,1,2,26,300,4,5],[39,15,41,73],[]),([60,55,23,14,4,5],[25,22,21,93],[0]),([267,19,0,1,2,3,4,5],[44,8],[0]),([9,178,2,3,4,5],[12,31,24,17,8,22,25],[0]),([0,1,2,138,3,4,5,7],[64,17],[0]),([74,23,14,2,3,4,5],[12,79,254,107,22,25],[0]),([301,0,1,147,2,3,4,5],[5,6,70],[]),([178,2,3,302,4,5],[5,0,31,1,15,78],[0,1]),([60,55,23,14,3,4,5],[21,25,22,93],[0]),([24,78,1,14,2,17,3,5],[15,78],[0]),([178,62,2,3,4,5],[1,25,15,78],[0,1]),([19,53,2,17,3,130,4,5],[60,22],[0]),([143,19,53,2,3,4,5],[22,51,60,15,78,59],[0]),([23,14,2,3,61,4,5,7],[21,15,87,22],[0]),([32,19,0,1,62,2,3,4],[139,124,140,56],[0]),([10,0,1,160,2,3,4,5],[39,71],[0]),([19,53,2,81,3,4,5],[60,12,29,22,25],[0,1]),([0,1,2,3,87,80,5],[116,100,52,65,41,73,114,115],[0,2]),([303,115,1,2,4,5],[12,39,6,8,25,51],[0,2,5,6]),([55,178,2,3,4,5],[5,1,15,78],[0,1]),([6,0,1,160,2,3,4,5],[67,23,71],[0]),([0,1,174,2,3,4,5,7],[64,23,75],[0]),([118,0,1,2,3,4,20,5],[22,8,25],[0]),([10,9,23,14,2,3,5],[12,92,89],[0]),([292,0,1,2,3,4,5],[22,44,69,71,67,118,64],[]),([267,0,1,14,2,3,4,5],[69,42,13,44,40,39,116],[0]),([304,178,2,3,4,5],[12,1],[0]),([0,1,2,138,3,8,4,5],[67,65],[0]),([256,64,0,1,2,3,4,5],[72,73,255],[]),([305,178,2,3,4,5],[1,0,31,8,15,78],[0,1]),([60,178,2,3,4,5],[1,0,31,25,15,78],[0,1]),([55,0,1,177,2,3,4,5],[72,15,41,78,87,175,70],[0,1]),([9,23,14,2,17,3,5],[79,93,103,15,256],[0]),([23,0,1,2,3,87,5],[12,83,41,116,115,73],[0]),([19,53,2,26,3,4,5],[15,78,41,62,11,22,25],[0]),([270,0,1,2,3,4,5],[44,69,72,40,71,70,67,118,64],[]),([0,1,306,128,2,3,4,5],[72,70],[0]),([170,23,14,2,3,4,5],[1,21,78,107],[0]),([178,2,3,4,307,5],[5,12],[0]),([0,1,2,3,159,130,4,5],[73,72],[0]),([155,23,0,1,2,3],[12,41,83,74,73,13],[0]),([10,9,23,0,1,2,111,5],[183,15,73],[0]),([23,14,62,2,3,4,5,7],[22,15,78,87,25],[0,1])]
def P_34_7_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [0,1,5,6,8,11,12,13,15,17,21,22,23,24,25,29,30,31,37,39,40,41,42,44,51,52,53,56,59,60,62,63,64,65,67,69,70,71,72,73,74,75,78,79,80,82,83,84,87,88,89,91,92,93,96,97,98,100,102,103,104,107,108,113,114,115,116,118,124,129,131,132,136,137,138,139,140,141,142,143,146,147,165,175,176,177,180,183,201,209,210,211,219,220,223,238,246,247,248,249,251,252,253,254,255,256]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_7_3 : checkNodesBT W_34 G_34 fmask_34 P_34_7_3 autos_34 bk_34_6 7 nd_34_7_3 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_7_3 : ∀ ns ∈ nd_34_7_3, Impossible G_34 7 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_6_ok chk_34_7_3
def nd_34_7_4 : List NodeSpec := [([9,23,14,119,2,3,4,5],[79,25,164],[0]),([178,2,308,3,4,5],[1,25],[0,1]),([158,0,1,2,40,3,4,5],[81,118,170],[0]),([178,309,2,3,4,5],[5,22,15,78],[0,1]),([19,53,62,2,17,3,4,5],[11,15,22,25],[0])]
def P_34_7_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [1,5,11,15,22,25,78,79,81,118,164,170]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_7_4 : checkNodesBT W_34 G_34 fmask_34 P_34_7_4 autos_34 bk_34_6 7 nd_34_7_4 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_7_4 : ∀ ns ∈ nd_34_7_4, Impossible G_34 7 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_6_ok chk_34_7_4
def nodes_34_7 : List NodeSpec := nd_34_7_0 ++ nd_34_7_1 ++ nd_34_7_2 ++ nd_34_7_3 ++ nd_34_7_4
def bk_34_7 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_7
set_option maxRecDepth 500000 in
lemma bk_34_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 7 xs.toFinset) bk_34_7 :=
  buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (mem_34_7_0) mem_34_7_1) mem_34_7_2) mem_34_7_3) mem_34_7_4)
def nd_34_8_0 : List NodeSpec := [([0,1,2,26,3,85,4,5],[124,126,257,258,39,41,73,17,8,23,51,205,156,44],[0,2,3,4]),([0,1,2,26,3,8],[39,13,65],[0,3,2,4,5,6]),([74,0,1,2,3,7],[39,65],[0,3,2,4,5,6]),([10,9,28,0,1,2,5],[15,52,41,73,211,183],[5,6]),([10,9,0,29,1,2,5],[39,89,52,41,73,211,183],[5,6]),([9,86,0,1,2,5],[39,65],[0,3,2,4,5,6]),([0,1,2,17,3,87,5],[116,65,52],[0,3,2,4,5,6]),([0,1,2,3,87,5],[52,116,65],[0,3,2,4,5,6]),([0,1,2,17,3,43],[39,65],[0,3,2,4,5,6]),([86,0,1,2,3,5],[39,65],[0,3,2,4,5,6]),([88,0,1,2,3,5],[39,118],[0,3,2,4,5,6]),([78,32,0,1,2,3,4],[145,13,67,259,140,139,142,143],[0,2,5,6]),([78,0,1,2,3,4,34],[78,39,122,146,161,147],[0,2,5,6]),([24,0,1,2,17,3,80,5],[116,234,261,41,73,235,260],[0,2]),([32,0,1,2,3,80,4,5],[13,262,98,67,29,37,139,142],[0,2]),([0,1,2,3,80,4,34],[261,88,39,122,146,161,147],[0,2,5,6]),([89,13,0,1,2,40,3,4,5],[116,249,12,41,6],[0]),([0,1,14,2,17,3,4,5],[170,168,250,22,41,52,264,15,124,65,73,25,44,40,263,179],[0,1]),([35,36,0,1,2,3,4,5],[12,17,13,39,22,23,51,84],[]),([0,1,2,56,3,90,4,5],[116,13,8,39,73,23,6,19,22],[]),([89,12,0,1,2,40,3,4,5],[249,116,122,41,6,117],[0]),([0,1,2,40,3,91,4,5],[116,39,265,122,146,117,149,78],[0,2]),([12,0,92,1,2,3,4,5],[29,6,116,52,25,19,22,73],[]),([60,23,0,1,2,3,4,5,7],[1,83,25,15,84],[0]),([0,1,93,2,3,4,5],[5,6,154,41,266,78,153,70,124],[0,4]),([9,23,0,1,2,3,5,7],[12,215,41,73,267],[0]),([33,15,0,1,2,3,4],[13,39,97,41,73,163,202],[5,6]),([0,1,94,2,3,4,5],[22,176,15,23,124,113],[0]),([32,15,0,1,2,3,4],[52,98,39,139,140,142,143],[5,6]),([0,1,14,2,17,3,4,34],[170,88,176,161,39,37,124,147],[0,3,1]),([15,0,1,2,3,4,34],[13,39,88,65,122,146,161,147],[5,6]),([47,51,15,0,2,3,5],[35,39,8,84,22],[]),([35,15,12,1,2,3,4,5],[35,6,39,25,51],[]),([9,23,0,1,2,3,4,5],[12,256,116,113,25,22,73,268],[0]),([0,48,1,2,3,5,7],[13,67,87],[5,6]),([64,0,1,14,62,3,4,5],[23,22,39,116,166,73,269,146,15],[0]),([16,0,1,2,26,4,5],[15,52,124,39,41,73],[0,5,6,2]),([95,0,1,2,3,4,5],[12,39,8,6,72,70],[]),([0,1,2,3,96,4,5],[12,39,6,70,72],[]),([16,15,1,2,4,44,5],[12,116,6,51,25],[0]),([47,0,1,2,3,46,5],[5,39,52],[]),([0,1,2,3,97,4,5],[5,39,12,118],[]),([0,1,2,3,98,4,5],[1,39,118,64],[]),([99,0,1,2,3,4,5],[13,39,78,40,42,72,70],[5,6]),([6,24,18,0,1,2,3],[15,39,41,73,209,210],[0,5,6]),([32,0,1,2,3,80,4],[98,13,67,262,140,139,143,142],[0,2,5,6]),([60,0,1,14,2,3,4,5,7],[75,13,87,15,73,22,52,175,41],[0]),([16,45,15,1,2,4,5],[6,124,39,52,51,25],[0]),([25,18,0,1,2,4,5],[15,13,113,41,73],[5,6]),([9,0,1,2,3,34],[39,65],[0,3,2,4,5,6]),([18,0,1,2,26,4,5],[13,15,69,41,73],[5,6,0]),([100,18,0,2,3,4,5],[15,52,6,19,22],[]),([60,19,0,1,2,3,4,5,7],[56,15,22,5,73,87,158],[0]),([18,0,101,2,3,4,5],[15,52,270,84,73],[]),([102,0,1,2,3,4,5],[15,52,40,42,70,72],[5,6]),([18,0,1,2,3,4,34],[13,39,78,65,122,146,161,147],[5,6]),([60,55,0,1,14,4,5],[22,23,75,166,73,13],[0]),([0,103,1,2,3,4,5],[29,6,39],[]),([19,0,1,2,3,104,4,5],[1,152,132,8,15,52,78,116,146,271,70,138],[0]),([47,51,18,0,2,3,5],[12,39,84,22],[]),([100,15,0,2,3,4,5],[116,17,52,19,22],[]),([15,12,79,1,2,3,4,5],[35,8,266,25,51],[0]),([0,105,1,2,3,4,5],[13,87,116,40,42,70,72],[5,6]),([106,0,1,2,3,4,5],[12,116,8,6,72,70],[]),([18,0,50,1,107,2,3,4,5],[1,25,6,8,84],[0,7]),([75,45,18,0,2,4,5],[6,39,52,22,84],[3]),([108,0,1,2,3,4,5],[1,83,215,25,71,64],[0]),([0,1,109,2,3,4,5],[5,39,64,118],[1]),([0,110,1,2,3,4,5],[17,39,52,70,72],[]),([9,19,0,1,2,111,3,4,5],[116,132,15,22,164],[0]),([112,0,1,2,3,4,5],[8,39,52,72,70],[]),([23,0,1,2,17,3,8,5],[12,83,29,37,272],[0]),([60,18,0,54,1,2,4,5],[124,39,52,22,51,8,6,84,25],[]),([23,0,1,2,3,113,4,5],[1,12],[0]),([13,18,79,1,2,3,4,5],[35,8,52,25,51],[0]),([19,53,2,17,3,4,5],[12,187,11,273,22,25],[0,1]),([18,54,1,2,22,4,5],[8,124,39,52,25,51],[0]),([0,114,1,2,3,4,5],[35,8,6,70,72],[]),([115,1,2,3,4,5],[39,52,69],[0,2,5,6]),([32,0,1,14,2,17,3,4],[170,98,139,166,176,13,65,143,142],[0,3]),([6,24,19,0,1,2,3],[78,15,209,56,73,13,210],[0]),([116,0,1,2,3,4,5],[1,39,41],[]),([0,1,14,2,26,3,4,5],[126,250,264,205,124,166,75,22,39,25,52,73,44,40,156],[0,3]),([25,19,0,1,2,3,4,5],[15,152,78,41,13,22,25,232,73,212],[0]),([19,0,1,2,26,3,4,5],[15,78,41,22,124,136,56,8,25,126,39,73,156],[0]),([83,0,1,2,3,5,7],[13,15,67],[5,6]),([0,1,117,2,3,4,5],[5,15,78],[]),([15,0,1,2,3,4,43],[116,52,109,41,73,160,203],[5,6]),([118,0,1,2,3,4,5],[25,22,84,44,71,67,64,118],[0,1]),([19,0,1,2,3,8,7],[12,159,56,73,13,201],[0]),([6,9,19,0,1,2,3,5],[12,56,29,37,241,274],[0]),([9,19,0,1,119,2,3,4,5],[116,132,275,25,276],[0]),([78,120,0,1,2,3,4,5],[191,193,39,13,189,84,25,187,278,259,277,279],[0,2,5]),([0,1,2,3,91,4,5],[265,39,121,78,40,42,70,72],[5,6,0,2]),([74,19,0,1,2,3,4,5],[12,132,29,35,22,138,25,254,37,113,280],[0]),([18,0,1,2,3,8,7],[13,39,15,65,41,73,159,201],[5,6,0]),([23,0,1,2,3,104,4,5],[1,226,281,15,165,78,219],[0]),([121,0,1,2,3,4,5],[5,116,118,64],[]),([32,23,0,1,2,3,4],[140,145,215,12,165,13,142,143,65],[0]),([10,9,19,0,1,2,3,5],[12,152,211,124,73,183],[0]),([122,0,1,2,3,4,5],[13,39,171,40,42,72,70],[5,6]),([35,0,48,1,2,3,4,5],[35,17,39,22,23,51,84],[]),([45,18,1,2,22,4,5],[6,39,52,25,51],[0]),([10,9,19,0,1,2,5],[12,211,132,116,73,183],[0]),([123,0,1,2,56,3,4,5],[13,41,1,8,23,84],[]),([35,41,0,1,2,3,4,5],[35,30,39],[]),([124,0,1,2,3,4,5],[1,15,122],[]),([19,0,1,2,17,3,4,5],[12,132,8,22,41,25,168,124,73,52,263],[0,1]),([0,1,125,2,3,4,5],[5,12,69,40],[0]),([0,1,2,37,3,126,4,5],[30,116,13,40],[]),([24,19,0,1,2,17,3,5],[12,136,41,13,234,73,260],[0]),([19,0,1,2,3,66,4,5],[12,136,8,22,29,25,248,37,282],[0]),([64,0,1,63,2,3,4,5],[35,23,19,73],[0]),([0,1,2,3,127,4,5],[5,12,56,273,118],[0]),([19,0,1,2,17,3,8,5],[12,56,29,37,236,272],[0]),([32,19,0,1,2,17,3,4,5],[12,136,13],[0]),([32,19,0,1,2,3,4,5],[12,138,139,13,22,25,37,39,142],[0]),([33,18,0,1,2,3,4],[15,52,41,73,163,202],[5,6]),([0,1,128,2,3,4,5],[12,229,75,264,171,70,72,124,283],[0,1]),([32,19,0,1,2,3,4],[145,139,136,12,132,13,142,143,65],[0]),([19,0,1,2,3,113,4,5],[12,22,116,52],[0]),([19,0,1,2,3,4,34],[12,161,56,146,147,124],[0]),([19,0,1,2,81,3,4,5],[12,132,8,22,29,25,39,244,37,124,284],[0,1]),([9,19,0,1,2,17,3,5],[136,169,132,15,256,103,268,285],[0]),([74,0,1,14,2,3,4,5],[254,170,196,179,29,22,12,35,37,25,280],[0]),([129,19,0,1,2,17,3,4,5],[243,132,73,51,25,148],[0]),([19,0,1,2,17,3,130,4,5],[5,25,148,132,15,286,22],[0]),([9,19,0,1,2,3,5,7],[12,136,41,242,73,267],[0]),([19,1,2,17,3,80,4,5],[56,273,187,12,8,17,287,41,51,23],[0]),([131,0,1,2,37,3,4,5],[41,13,6,288,25,73,84],[5,0]),([64,19,0,1,2,40,3,4,5],[12,5,37,149,132,138],[0]),([19,0,1,2,3,132,4,5],[5,152,25,132,15,73,78,72,138],[0]),([133,0,1,2,3,4,5],[5,116,12,118],[]),([134,0,1,2,3,4,5],[37,25,84,22],[]),([58,64,19,0,1,3,5],[12,25,22,39,116],[]),([19,0,1,2,135,3,4,5],[5,12,136,73,72],[0]),([136,19,0,1,2,3,4,5],[12,136,22,146,289],[0]),([9,0,1,2,71,5],[39,65],[0,3,2,4,5,6]),([0,1,2,137,3,4,5],[8,22,12,56],[0]),([6,55,19,0,1,2,3,4,5],[25,56,15,5,13,22,171],[0])]
def P_34_8_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [1,5,6,8,11,12,13,15,17,19,22,23,25,29,30,35,37,39,40,41,42,44,51,52,56,64,65,67,69,70,71,72,73,75,78,83,84,87,88,89,97,98,103,109,113,116,117,118,121,122,124,126,132,136,138,139,140,142,143,145,146,147,148,149,152,153,154,156,158,159,160,161,163,164,165,166,168,169,170,171,175,176,179,183,187,189,191,193,196,201,202,203,205,209,210,211,212,215,219,226,229,232,234,235,236,241,242,243,244,248,249,250,254,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_8_0 : checkNodesBT W_34 G_34 fmask_34 P_34_8_0 autos_34 bk_34_7 8 nd_34_8_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_8_0 : ∀ ns ∈ nd_34_8_0, Impossible G_34 8 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_7_ok chk_34_8_0
def nd_34_8_1 : List NodeSpec := [([55,19,0,1,2,3,4,5,7],[15,5,22,78,13,87],[0,1]),([0,1,2,138,3,4,5],[17,25,22,72,67,71,118,64],[0,1]),([10,55,19,0,1,2,3,4,5],[56,15,124,167],[0]),([19,0,1,2,17,3,20,5],[12,56,41,238,73,290],[0]),([55,19,0,1,2,3,4,20,5],[5,22,15,25,152,124,91],[0]),([60,55,19,0,1,3,4,5],[22,56,25,136,124],[0]),([23,0,1,2,17,3,20,5],[12,83,41,73,290],[0]),([0,1,63,49,2,3,4,5],[35,22,23,39,6],[0]),([60,55,19,0,1,4,5],[25,22,56,136,73,13],[0]),([19,0,1,139,3,4,5],[12,22,116,52],[0]),([140,0,1,2,3,4,5],[8,22,56,136],[0]),([19,0,1,2,3,141,4,5],[5,56,25,136,78,72,291],[0]),([58,0,1,82,2,3,5],[22,39,23,15,292],[]),([19,0,1,62,2,3,8,4,5],[56,37,29,293],[0]),([9,19,0,1,62,2,3,4,5],[152,116,275,276],[0]),([142,0,1,2,3,4,5],[12,22,113,124],[]),([10,19,0,1,62,2,3,4,5],[56,15,124,41,294],[0]),([0,1,14,2,3,61,4,5,7],[75,73,52,13,87,22,15],[0]),([143,19,0,1,2,3,4,5],[1,132,13,39,15,78,138,73,295],[0]),([9,55,19,0,1,2,3,4,5],[152,116,15,164],[0]),([6,24,15,0,1,2,3],[13,52,80,41,73,209,210],[0,5,6]),([19,0,1,62,2,3,4,20,5],[5,22,184,25,152,124,41],[0]),([47,18,1,2,22,4,5],[12,8,39,25,51],[0]),([55,0,1,14,2,3,8,4,5],[75,206,12,37,296,293,29],[0]),([19,0,1,62,3,61,4,5],[5,22,56,136],[0]),([144,0,1,2,26,3,4,5],[15,124,78,41,73,6,25,205,156,69],[0,2,3,4]),([35,13,18,1,2,3,4,5],[35,17,25,51],[]),([0,1,145,2,3,4,5],[12,22,84,124,113],[]),([19,0,1,62,61,4,5],[22,25,56,136,73,13],[0]),([143,0,1,14,2,3,4,5],[22,51,39,116,170,15,78,179,13,295],[0]),([0,1,2,146,3,4,5],[5,22],[0,1]),([6,19,53,2,3,4,5],[12,122,11,25,22],[0,1]),([0,1,14,2,17,3,20,5],[75,238,176,15,41,73,290],[0]),([19,53,2,3,8,4,5],[12,29,11,22,25],[0,1]),([6,19,0,1,62,2,3,4,5],[56,22,5,229,25,13,122,15],[0]),([0,1,147,2,3,4,5],[39,5,12,297,70,118,6],[1,0]),([19,53,2,3,4,20,5],[12,41,63,22,25,44,69],[0,3]),([58,19,53,2,3,4,5],[12,41,22],[0]),([19,53,2,3,4,69,5],[12,23],[0]),([55,19,53,2,3,4,5],[25,23,22,15,78],[0,1]),([60,19,53,2,3,4,5],[22,51,11,62,25,15,78],[0,1]),([19,53,2,3,61,4,5],[25,23,11,62,22,15,78],[0,1]),([19,0,1,148,2,3,4,5],[5,25,132,15,78,138],[0]),([19,53,49,2,3,4,5],[22,51,12,11,25],[0]),([19,53,62,2,3,4,5],[22,51,25,15,78],[0,1]),([0,1,59,107,2,3,4,5],[22,298,78,8,15,25,52,65],[]),([0,1,65,49,2,3,4,5],[35,22,15,39,8],[0]),([60,0,1,65,2,3,4,5],[116,22,13,25,8,113],[]),([19,0,1,2,17,40,3,4,5],[12,56,124,138,185,187],[0,1]),([6,24,0,1,14,2,3],[80,209,264,250,75,73,13,210],[0]),([0,1,14,2,3,27,4,5],[196,230,264,170,300,122,22,78,13,146,25,299],[0]),([0,1,14,148,2,3,4,5],[23,39,13,22,84,170,15,78,179,25,73,269],[0]),([25,0,1,14,2,3,4,5],[196,232,41,264,250,13,22,15,25,73,212],[0]),([0,1,14,2,3,8,7],[176,96,159,75,39,73,13,201],[0]),([149,57,0,1,2,3,4,5],[12,84,301],[]),([23,0,1,2,3,150,4,5],[1,83,215,78,146],[0]),([6,9,0,1,14,2,3,5],[75,241,178,29,12,35,37,274],[0]),([83,0,79,1,2,3,4,5],[12,302,13,39,52,84,22,25,303],[]),([9,0,1,14,2,3,5,7],[166,242,178,15,41,116,73,267],[0]),([41,0,79,1,2,3,4,5],[35,304,6,39,8,84,22,25,305,306],[]),([9,0,1,14,2,111,3,4,5],[116,170,164,275,309,22,307,276,308],[0]),([115,1,2,4,5],[39,52],[0,2,1,5,6,7]),([10,23,0,1,62,2,3,4,5],[83,15,73,41,310,167,294],[0]),([0,1,151,2,3,4,5],[35,164,275,72,70],[]),([23,14,2,3,4,5,7],[15,87,78,22,25],[0,1]),([10,9,15,0,1,2,5],[89,52,124,41,73,211,183],[5,6]),([55,19,0,1,49,3,4,5],[5,22,136,116,15],[0]),([10,9,0,1,14,2,3,5],[89,196,176,211,116,73,183],[0]),([19,0,1,2,17,3,4,34],[12,132,161,39,37,124,147],[0,1]),([33,0,1,14,2,3,4],[97,163,264,250,196,73,13,202],[0]),([152,0,1,2,3,4,5],[37,25,84],[]),([0,1,14,49,2,40,3,4,5],[22,185,5,39,116,30,117,195,170,65,179,311,312,250],[0]),([19,0,1,2,153,3,4,5],[12,1,124,8,39],[0]),([0,1,154,2,3,4,5],[176,91,184,196,70,72],[0]),([23,0,1,62,61,4,5],[1,25,83,215],[0]),([6,0,1,14,62,2,3,4,5],[75,22,73,5,30,13,12,171,225],[0]),([25,23,0,1,2,3,4,5],[15,226,78,41,13,25,22,73,212],[0]),([155,0,1,2,3],[65,39],[0,3,2,4,5,6]),([24,0,1,14,2,17,3,5],[166,234,176,235,13,73,260],[0,3]),([32,0,1,14,2,3,4,5],[179,98,176,139,13,22,37,25,39,142],[0]),([32,0,1,14,2,3,4],[98,139,166,176,170,13,143,142],[0]),([0,1,156,2,3,4,5],[23,176,22,84,124,113],[]),([0,1,14,2,3,4,34],[176,88,161,75,39,146,147,124],[0]),([32,18,0,1,2,3,4],[52,39,124,12,98,139,140,142,143],[5,6]),([23,0,1,2,3,132,4,5],[25,226,84,165,37,15,17,52,78,219],[0]),([0,1,2,157,3,4,5],[1,12,83,124,118],[0]),([9,0,1,14,2,3,4,5],[103,170,250,41,116,22,52,15,25,78,73,65,179,268],[0]),([0,1,14,2,71,3,4,5],[75,239,176,122,22,78,124,146,25,313],[0]),([9,0,1,14,2,17,3,5],[166,103,170,250,116,256,169,285,268],[0]),([23,0,1,2,3,4,34],[12,122,83,146,147,124],[0]),([23,0,1,2,153,3,4,5],[12,1,314,70],[0]),([0,1,14,62,2,17,3,4,5],[75,30,73,5,22,124,250,187,148],[0]),([32,23,0,1,2,17,3,4,5],[215,12,13],[0]),([129,0,1,14,2,17,3,4,5],[170,73,51,22,187,25,148],[0,3]),([64,19,53,2,3,4,5],[25,23,12,11,22],[0]),([158,0,1,2,17,3,4,5],[75,187,189,81,52,73,148],[0]),([0,1,2,17,3,159,4,5],[83,315,12,174,52,73,148,1],[0]),([158,0,1,2,3,4,5],[187,189,81,75,70,72,118],[0,1]),([0,1,160,2,3,4,5],[23,22,84,69,67,71,118,64],[0,1]),([78,1,14,2,17,3,4,5],[75,316,273,187,251,25,78],[0]),([161,0,1,63,2,3,4,5],[22,116,51,13,23],[]),([0,1,14,2,135,3,4,5],[30,166,170,5,65,15],[0]),([0,1,162,2,3,4,5],[37,23,22,84],[]),([19,0,1,62,2,3,4,5,7],[22,15,5,78,13,41,175],[0,1]),([0,1,14,2,3,113,4,5],[22,15,39,116,250,69,78,179,41,52,65],[0]),([163,0,1,2,3,4,5],[1,12],[0]),([164,0,1,2,3,4,5],[1,15,78],[]),([0,1,14,2,3,104,4,5],[51,196,22,170,52,15,116,146,78,179],[0]),([165,0,1,2,3,4,5],[22,51,75,317,124,118],[0]),([60,23,14,2,3,4,5],[1,21,93,25,15,78,40],[0,1]),([9,55,0,1,14,2,3,4,5],[196,116,164,275,309,307,276,308],[0]),([12,0,1,2,40,3,166,4,5],[120,116,117,78,312,185,41,318],[0]),([167,19,0,1,3,4,5],[12,19,116,52],[0]),([55,0,1,14,2,17,3,4,5],[75,22,23,116,187,25,84,189,250,148,273,315,286],[0]),([0,1,2,17,3,127,4,5],[56,12,189,319,52,73,148,5],[0]),([55,23,0,1,49,3,4,5],[1,25,215,70,15],[0]),([10,9,0,1,14,2,5],[89,176,211,170,116,73,183],[0]),([15,0,1,2,3,8,7],[13,39,96,65,41,73,159,201],[5,6,0]),([35,83,0,1,2,3,4,5],[12,30,13,39,65],[]),([23,14,2,3,8,4,5],[12,206,21,22,25],[0,1]),([0,168,1,2,3,4,5],[116,52,15,320,40,42,70,72],[5,6]),([169,0,1,2,3,4,5],[22,51,69,72,67,71,118,64],[0,1]),([58,64,0,1,14,3,5],[22,23,176,116,39],[0]),([170,19,0,1,2,3,4,5],[1,56,73,78,13,237,138],[0]),([0,1,14,62,61,4,5],[22,23,75,166,39,73,13],[0]),([0,1,14,2,3,150,4,5],[51,75,22,166,73,146,78],[0]),([32,171,0,1,2,3,4],[35,98,12,118,139,140,142,143],[5,6]),([0,1,2,3,172,4,5],[15,52,40,42,70,72],[5,6]),([0,1,173,2,3,4,5],[22,51,75,166,69,71,64],[0]),([136,23,0,1,2,3,4,5],[1,12,215],[0]),([72,0,1,62,2,4,5],[22,39,52,69],[]),([0,1,14,2,3,141,4,5],[30,75,166,5,37,78,321],[0]),([19,0,1,2,71,3,4,5],[12,56,122,22,25,239,124,146,313],[0]),([0,1,174,2,3,4,5],[23,75,84,22,166,69,71,64],[0]),([0,1,14,2,81,3,4,5],[244,170,29,22,179,12,39,37,124,25,44,40,284],[0,1]),([0,1,14,62,2,3,8,4,5],[75,37,12,13,206,296],[0]),([33,19,0,1,2,3,4],[15,78,163,152,73,13,202],[0]),([10,0,1,14,62,2,3,4,5],[75,73,15,124,167,310],[0]),([0,1,14,62,2,3,4,20,5],[30,73,5,196,22,124,91,322],[0]),([175,0,1,2,3,4,5],[12,6,116,70,72],[])]
def P_34_8_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [1,5,6,8,11,12,13,15,17,19,21,22,23,25,29,30,35,37,39,40,41,42,44,51,52,56,62,63,64,65,67,69,70,71,72,73,75,78,80,81,83,84,87,88,89,91,93,96,97,98,103,113,116,117,118,120,122,124,132,136,138,139,140,142,143,146,147,148,152,156,159,161,163,164,165,166,167,169,170,171,174,175,176,178,179,183,184,185,187,189,195,196,201,202,205,206,209,210,211,212,215,219,225,226,229,230,232,234,235,237,238,239,241,242,244,250,251,256,260,264,267,268,269,273,274,275,276,284,285,286,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_8_1 : checkNodesBT W_34 G_34 fmask_34 P_34_8_1 autos_34 bk_34_7 8 nd_34_8_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_8_1 : ∀ ns ∈ nd_34_8_1, Impossible G_34 8 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_7_ok chk_34_8_1
def nd_34_8_2 : List NodeSpec := [([32,0,176,1,2,3,4],[35,98,140,139,143,142],[5,6]),([167,0,1,14,3,4,5],[23,176,19,116,39],[0]),([24,23,0,1,2,17,3,5],[12,215,41,13,73,260],[0]),([0,1,14,2,17,3,130,4,5],[323,170,19,148,116,25,84,22],[0]),([0,48,79,1,2,3,4,5],[35,8,67,84,22,23,51],[]),([9,0,1,14,119,2,3,4,5],[116,170,73,164,25,309],[0]),([19,0,1,2,3,4,43],[12,160,152,73,116,203],[0]),([23,0,1,2,3,66,4,5],[12,215,29,17,25,37,22,282],[0]),([0,1,14,62,3,61,4,5],[23,75,22,166,13],[0]),([18,0,1,2,3,4,43],[15,52,41,73,160,203],[5,6]),([0,1,177,2,3,4,5],[87,175,250,264,70,72,124,113],[0]),([58,64,23,0,1,3,5],[12,84,39,116],[0]),([170,0,1,14,2,3,4,5],[22,75,51,73,78,237,13,179],[0]),([76,0,1,2,3,61,4,5],[25,13,84,116],[0]),([0,1,82,2,3,5,7],[39,292,87,175,22],[]),([15,0,101,2,3,4,5],[116,8,52,84,73],[]),([6,55,23,0,1,2,3,4,5],[83,25,15,1,225,146],[0]),([13,0,1,2,40,3,166,4,5],[116,120,12,185,318,41],[0]),([60,0,1,63,2,3,4,5],[116,22,13,51,23],[]),([6,55,0,1,14,2,3,4,5],[75,23,171,22,12,225,25,84,229,122,146,116],[0]),([178,2,3,4,5],[],[0,1]),([60,0,1,63,2,4,5],[22,35,51,23],[]),([0,1,63,2,179,3,4,5],[116,23,19,13,22],[]),([9,19,0,1,2,3,4,5],[12,22,41,116,113,169,25,103,73,268],[0]),([6,24,23,0,1,2,3],[78,41,83,73,13,210],[0]),([180,0,1,2,3,4,5],[1,12,69,42],[0]),([129,23,0,1,2,17,3,4,5],[220,165,73,1,25,148],[0]),([23,0,1,2,71,3,4,5],[12,83,122,25,124,146,22,313],[0]),([55,23,0,1,2,3,4,5,7],[25,1,15,158,84,78,73],[0,1]),([23,0,1,2,3,27,4,5],[12,226,122,13,25,146,22,299],[0]),([64,19,0,1,62,3,4,5],[5,22,136,15],[0]),([0,1,14,2,17,40,3,4,5],[75,124,250,185,187,65,52,117,189,264,179,311,273,312,315],[0,1]),([143,23,0,1,2,3,4,5],[1,324,165,15,78,219],[0]),([55,19,0,1,2,17,3,4,5],[15,56,25,5,22,124,187],[0]),([23,0,1,2,26,3,4,5],[15,78,41,215,124,83,25,22,17,73,156],[0]),([0,1,181,2,3,4,5],[25,56,84,22,136,44,71,64],[0]),([55,0,1,14,2,3,4,20,5],[23,91,22,73,322,184,196,25,84,15,41],[0]),([23,0,1,2,3,8,7],[12,41,83,73,13,201],[0]),([6,0,1,2,3,66],[39,118],[0,3,2,4,5,6]),([6,9,23,0,1,2,3,5],[12,83,29,37,274],[0]),([19,0,1,49,2,40,3,4,5],[15,78,5,132,146,138,149,185],[0]),([74,23,0,1,2,3,4,5],[12,165,29,35,219,25,37,113,22,280],[0]),([9,23,0,1,2,111,3,4,5],[116,165,309,15,22,308],[0]),([23,0,1,2,182,3,4,5],[12,84,124,17,39,72,325],[0]),([183,0,1,2,3,4,5],[1,116,118,64],[]),([23,0,1,62,2,3,8,4,5],[83,37,12,41,296,206,293],[0]),([23,0,1,2,17,3,4,5],[12,165,41,17,25,124,73,52,22,263],[0,1]),([184,0,1,2,3,4,5],[12,84,124,113],[0]),([9,23,0,1,119,2,3,4,5],[116,165,15,73,41,25,309,164,275],[0]),([23,0,1,139,3,4,5],[1,12],[0]),([32,23,0,1,2,3,4,5],[12,219,29,13,25,37,22,39,142],[0]),([185,0,1,2,3,4,5],[5,12],[]),([23,0,1,2,17,40,3,4,5],[12,83,124,219],[0,1]),([23,14,62,2,3,4,5],[1,25,15,78,69],[0,1]),([19,0,1,2,3,27,4,5],[12,152,122,22,13,25,230,146,299],[0]),([23,0,1,148,2,3,4,5],[25,84,165,13,39,15,78,219,73,269],[0]),([23,0,1,2,17,3,4,34],[12,165,29,39,37,124,147],[0,1]),([186,0,1,2,3,4,5],[13,15,40,42,70,72],[5,6]),([32,0,1,14,2,17,3,4,5],[166,176,98,170,139,13],[0,3]),([18,1,2,22,4,44,5],[12,39,6,51,25],[0]),([0,1,14,139,3,4,5],[22,176,51,116,39],[0]),([60,55,23,0,1,3,4,5],[1,83,25,215],[0]),([0,1,14,2,182,3,4,5],[23,176,124,84,42,39,15],[0]),([0,1,14,2,17,3,8,5],[75,236,12,264,29,52,37,65,250,272],[0]),([9,55,23,0,1,2,3,4,5],[226,116,309,15,308],[0]),([0,1,2,3,159,4,5],[1,12,83,315,118],[0]),([19,0,1,2,3,61,4,5,7],[5,56,22,15,158,73,41,175],[0]),([18,1,2,22,4,5,7],[13,39,8,6,51,25],[0,5,6]),([60,55,23,0,1,4,5],[1,25,83,215],[0]),([64,23,0,1,2,40,3,4,5],[12,165,1,39,37,219],[0]),([23,0,1,2,3,4,43],[12,41,226,73,116,203],[0]),([0,1,14,2,3,66,4,5],[166,248,29,22,170,12,37,65,25,44,40,282],[0]),([0,1,2,40,3,187,4,5],[12,116,39,122,146,117,149],[0,2]),([19,53,2,3,4,5,7],[15,41,78,22,25],[0,1]),([23,0,1,2,17,3,130,4,5],[165,148,25,15,286,22],[0]),([149,0,1,82,2,3,4,5],[23,301,176,146,22,41],[]),([55,23,0,1,2,3,8,4,5],[83,12,37,296],[0]),([55,23,0,1,2,17,3,4,5],[83,15,25,1,148,286],[0]),([19,0,1,2,188,3,4,5],[5,56,25,78,138],[0]),([189,23,0,1,2,3,4,5],[12,84,116,113],[0]),([55,0,1,14,2,3,4,5,7],[13,15,73,87,25,22,41,78,175,158,39,52],[0,1]),([23,0,1,49,2,40,3,4,5],[1,15,39,165,78,219],[0]),([64,76,0,1,2,3,4,5],[35,25,84,73],[]),([23,0,1,2,135,3,4,5],[12,215,84,17],[0]),([0,1,14,2,3,132,4,5],[30,196,170,5,37,52,15,78,179],[0]),([9,23,0,1,2,17,3,5],[215,256,165,169,15,268,285],[0]),([9,0,1,14,62,2,3,4,5],[196,116,73,164,309],[0]),([190,0,1,2,3,4,5],[1,83,25,215],[0]),([23,14,2,17,3,4,5],[12,187,21,315,22,25],[0,1]),([0,1,14,2,153,3,4,5],[22,176,51,124,39,44,40],[0,3]),([10,19,53,2,3,4,5],[12,41,11,25,22],[0]),([58,23,14,2,3,4,5],[12,22,69],[0]),([23,14,49,2,3,4,5],[1,12,21,25,40],[0]),([64,0,1,14,2,40,3,4,5],[23,37,245,176,39,25,22,84,170,179],[0]),([136,0,1,14,2,3,4,5],[22,166,51,170,146,15,65],[0]),([24,78,0,1,2,17,3,5],[15,39,78,65,52,41,73,235,260],[0,2]),([10,55,23,0,1,2,3,4,5],[83,15,124,310,73],[0]),([0,191,1,2,3,4,5],[30,29],[]),([55,19,0,1,2,3,8,4,5],[56,12,37,13,206],[0]),([167,23,0,1,3,4,5],[12,84,116,52],[0]),([0,1,14,2,3,4,43],[176,109,160,196,73,116,203],[0]),([47,16,15,1,2,4,5],[12,8,25,51],[0]),([6,23,14,2,3,4,5],[12,171,21,25,22,40],[0,1]),([19,0,1,2,182,3,4,5],[12,5],[0]),([32,23,0,1,2,17,3,4],[165,140,145,215,12,13,142,143],[0]),([55,0,1,14,49,3,4,5],[22,23,39,116,166,295,146,15],[0]),([55,23,0,1,2,3,4,20,5],[1,25,322,84,73,226,15],[0]),([23,0,1,2,188,3,4,5],[25,83,84,1,78,13,208,219],[0]),([192,0,1,2,3,4,5],[25,84,44,70,71,67,64,118],[0,1]),([170,23,0,1,2,3,4,5],[1,83,326,78,219],[0]),([0,1,63,62,2,4,5],[22,116,13,72,69],[]),([23,0,1,2,3,61,4,5,7],[15,25,1,83,41,84,87,175],[0]),([189,0,1,14,2,3,4,5],[23,176,116,52,84,42,15],[0]),([23,0,1,2,3,141,4,5],[25,83,84,215,17,78,37],[0]),([78,32,0,1,2,3,4,5],[12,259,13,29,37,139,142],[0,2]),([6,23,0,1,62,2,3,4,5],[83,41,1,25,73,78,225,171,229],[0]),([19,0,1,62,2,17,3,4,5],[5,22,15,56,25,124,189,315],[0]),([23,0,1,2,81,3,4,5],[12,165,29,17,39,25,37,124,22,284],[0,1]),([23,0,1,62,2,17,3,4,5],[15,83,1,25,73,41,148,187,189],[0]),([193,0,1,2,3,4,5],[12,22,84,113,124],[]),([60,55,0,1,14,3,4,5],[22,75,23,166,124],[0]),([23,14,2,3,4,20,5],[12,91,92,22,25,40],[0]),([64,23,0,1,62,3,4,5],[1,25,215,15],[0]),([23,0,1,62,3,61,4,5],[1,83,215,25],[0]),([23,0,1,62,2,3,4,20,5],[73,1,25,15,84,41,226,322,91,184],[0]),([32,19,0,1,2,17,3,4],[132,145,139,136,12,13,142,143],[0]),([0,1,14,2,188,3,4,5],[23,75,84,116,25,22,208,13,78,179],[0]),([23,14,2,3,61,4,5],[25,23,21,93,22,15,78,69],[0,1]),([10,9,23,0,1,2,3,5],[12,226,41,124,73,183],[0]),([10,23,14,2,3,4,5],[12,167,21,25,22],[0]),([10,9,18,0,1,2,5],[15,52,41,73,211,183],[5,6]),([0,1,63,2,3,61,4,5],[23,13,19,116,22],[]),([0,1,82,107,2,3,4,5],[22,298,23,12,52,292,69,327,42,328,72,250],[0]),([9,23,14,2,3,4,5],[12,164,93,276,79,22,25],[0]),([64,23,14,2,3,4,5],[25,23,12,21,22],[0]),([33,23,0,1,2,3,4],[15,41,78,226,73,13,202],[0]),([16,15,1,2,4,5,7],[13,39,8,6,51,25],[0,5,6]),([0,1,2,3,194,4,5],[39,87,52,40,42,70,72],[0,5,6,2]),([9,23,0,1,62,2,3,4,5],[226,116,15,73,41,309,164,275],[0]),([19,0,1,2,3,150,4,5],[1,56,136,73,78,146,329],[0])]
def P_34_8_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [1,5,6,8,11,12,13,15,17,19,21,22,23,25,29,30,35,37,39,40,41,42,44,51,52,56,64,65,67,69,70,71,72,73,75,78,79,83,84,87,91,92,93,98,103,109,113,116,117,118,120,122,124,132,136,138,139,140,142,143,145,146,147,148,149,152,156,158,160,164,165,166,167,169,170,171,175,176,179,183,184,185,187,189,196,201,202,203,206,208,210,211,215,219,220,225,226,229,230,235,236,237,245,248,250,256,259,260,263,264,268,269,272,273,274,275,276,280,282,284,285,286,292,293,295,296,298,299,301,308,309,310,311,312,313,315,318,322,323,324,325,326,327,328,329]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_8_2 : checkNodesBT W_34 G_34 fmask_34 P_34_8_2 autos_34 bk_34_7 8 nd_34_8_2 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_8_2 : ∀ ns ∈ nd_34_8_2, Impossible G_34 8 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_7_ok chk_34_8_2
def nd_34_8_3 : List NodeSpec := [([23,0,1,62,2,3,4,5,7],[1,15,25,73,41,78,84,158,87,175],[0,1]),([10,55,0,1,14,2,3,4,5],[75,15,124,73,167,41,294,310],[0]),([10,9,23,0,1,2,5],[12,41,165,116,73,183],[0]),([55,23,14,2,3,4,5],[25,23,22,15,78,40],[0,1]),([9,19,53,2,3,4,5],[12,164,62,307,60,22,25],[0]),([0,1,2,3,187,4,5],[12,39,71,40,42,70,72],[5,6]),([0,1,14,62,2,3,4,5,7],[13,22,73,15,39,78,23,87,52,158],[0,1]),([189,19,0,1,2,3,4,5],[12,25,84,116,113,22,23],[0]),([23,14,2,3,4,69,5],[12,23,40],[0])]
def P_34_8_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [1,12,13,15,22,23,25,39,40,41,42,52,60,62,70,71,72,73,75,78,84,87,113,116,124,158,164,165,167,175,183,294,307,310]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_8_3 : checkNodesBT W_34 G_34 fmask_34 P_34_8_3 autos_34 bk_34_7 8 nd_34_8_3 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_8_3 : ∀ ns ∈ nd_34_8_3, Impossible G_34 8 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_7_ok chk_34_8_3
def nodes_34_8 : List NodeSpec := nd_34_8_0 ++ nd_34_8_1 ++ nd_34_8_2 ++ nd_34_8_3
def bk_34_8 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_8
set_option maxRecDepth 500000 in
lemma bk_34_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 8 xs.toFinset) bk_34_8 :=
  buildBucketsBT_of_mem (forall_append (forall_append (forall_append (mem_34_8_0) mem_34_8_1) mem_34_8_2) mem_34_8_3)
def nd_34_9_0 : List NodeSpec := [([6,24,0,1,2,3],[64,71,39],[0,3,2,4,5,6]),([25,0,1,2,3,4,5],[113,71,64,44,69,42,40,72,70],[0,3,2,4,5,6]),([0,1,2,26,3,4,5],[71,64,124,39,52,44,69,40,42,70,72],[0,3,2,4,5,6]),([0,1,2,3,27,4,5],[65,113,44,69,40,42,70,72],[0,3,2,4,5,6]),([0,1,2,3,8,7],[65,39],[0,3,2,4,5,6]),([9,28,0,1,2,3,4,5],[116,52,164,15,275,276,309,308],[5,6,0]),([9,0,29,1,2,3,4,5],[116,52,164,276,275,308,309,44],[5,6,0]),([10,9,0,1,2,5],[65,67],[0,3,4,2,5,6]),([30,1,2,3,4,5],[65,69,113],[5,6,3,4]),([31,1,2,3,4,5],[65,44,113],[5,6,3,4]),([24,0,1,2,17,3,5],[52,67,65],[0,3,2,4,5,6]),([0,1,2,17,3,20,5],[39,65],[0,3,2,4,5,6]),([32,0,1,2,17,3,4,5],[13,52,65],[0,3,2,4,5,6]),([32,0,1,2,3,4,5],[52,65,44,69,42,40,72,70],[0,3,2,4,5,6]),([32,0,1,2,17,3,4],[67,52,13,65],[0,3,2,4,5,6]),([33,0,1,2,3,4],[64,71,113],[0,3,2,4,5,6]),([32,0,1,2,3,4],[52,65,67],[0,3,4,2,5,6]),([0,1,2,3,4,34],[65,39],[0,3,2,4,5,6]),([35,13,0,1,2,3,4,5],[1,65,39,52],[0,8]),([36,0,1,2,3,4,5],[39,69,13,40,42,70,72,118,64],[5,6,8,0,9,2]),([0,1,2,37,3,4,5],[65,44,124,39,40,42,70,72],[5,6,0,2]),([0,1,2,3,38,4,5],[65,113,44,40,42,70,72],[5,6]),([39,0,1,2,3,4,5],[65,113,69,40,42,72,70],[5,6]),([12,0,1,2,40,3,4,5],[39,65,78,185,116,6,25,331,332,118,117,312,149,330],[0,5,6,2]),([10,9,0,1,2,3,5],[65,113],[0,3,2,4,5,6]),([35,12,0,1,2,3,4,5],[30,65,39,52,42,40],[0,8]),([9,0,1,2,3,5,7],[52,71],[0,3,2,4,5,6]),([41,0,1,2,3,4,5],[39,44,13,40,42,70,72,118,64],[5,6,0,2]),([0,1,2,3,42,4,5],[39,44,52,40,42,70,72],[5,6]),([6,15,0,1,2,3,4,5],[13,39,171,17,8,23,51,122,146,44,71,229,225],[0,5,6]),([10,15,0,1,2,3,4,5],[13,39,167,65,41,73,294,310],[5,6,0]),([15,0,1,2,17,3,4,5],[13,39,187,65,44,17,8,23,51,189,315,148,286],[5,6,0]),([0,1,2,3,4,43],[65,113],[0,3,2,4,5,6]),([16,0,1,2,3,4,44,5],[12,30,39,65],[0]),([6,9,0,1,2,3,5],[39,65],[0,3,2,4,5,6]),([16,45,0,1,2,3,4,5],[30,39,52],[3,0]),([16,15,1,2,4,5],[44,69,39,52],[0,5,6,1,2,7]),([0,1,2,3,46,4,5],[39,69,52,333,42,40,72,70],[5,6,0,2]),([0,1,2,17,3,4,5],[65,67,124,113,44,69,42,40,72,70],[0,3,2,4,5,6,1]),([0,1,2,17,3,8,5],[39,65],[0,3,2,4,5,6]),([9,0,1,2,17,3,5],[52,67,71],[0,3,2,4,5,6]),([18,0,1,2,3,4,44,5],[12,30,116,42,44,40,69],[0]),([47,0,1,2,3,22,4,5],[5,39,333],[0]),([45,15,0,1,2,3,4,5],[116,13,8,6,40,42,113,44,69,23,51,19,22],[0,3]),([0,48,1,2,3,4,5],[39,69,35,40,42,72,70,64,118],[5,6,0,2]),([0,1,2,3,22,4,44,5],[1,333,39],[0]),([0,1,2,3,22,4,5,7],[39,334,87,41,8,17,73,51,23,175,158],[0,5,6]),([45,0,1,2,3,22,4,5],[17,39,52,23,51,22,19],[3,0]),([6,18,0,1,2,3,4,5],[13,39,78,44,6,25,122,146,69,71,270,335,229,225],[0,5,6]),([0,1,2,17,3,4,34],[39,65],[0,3,2,4,5,6,1]),([23,0,1,49,2,3,4,5],[1,12,336,83,25,70],[0]),([16,15,1,2,3,4,5],[39,52,69],[0,5,6,3,4,2]),([18,0,1,2,3,4,5,7],[13,15,71,44,64,41,73,6,25,69,175,158,270,335],[0,1,5,6]),([15,0,1,2,3,4,20,5],[116,52,91,41,73,8,17,51,23,44,184,322],[0,5,6,2]),([15,0,50,1,2,3,4,5],[5,39,69,13,65,52],[0,1]),([9,18,0,1,2,3,4,5],[116,52,15,164,275,276,309,308],[0,5,6]),([18,0,1,2,3,4,20,5],[15,52,41,73,6,25,44,69,184,322,270,335],[0,5,6,2]),([18,0,1,2,17,3,4,5],[13,39,15,187,65,44,69,6,25,189,315,148,286,270,335],[5,6,0]),([15,12,1,2,3,4,5],[39,69,35,52],[5,6,0,2]),([23,0,1,2,3,4,5,7],[15,78,41,40,1,44,73,13,64,25,39,69,42,158],[0,1]),([19,0,1,2,3,4,5,7],[15,175,78,73,13,64,22,25,39,40,158],[0,1]),([51,18,0,1,2,3,4,5],[30,39,44,13,52,65],[0,1]),([18,0,50,1,2,3,4,5],[39,297,5,12,6,25,65,52,42,337,335],[0,1]),([10,18,0,1,2,3,4,5],[15,13,39,65,41,73,294,310],[5,6,0]),([51,15,0,1,2,3,4,5],[1,39,69,13,52,65],[0,1]),([45,18,0,1,2,3,4,5],[30,13,116,44,69,42,40],[0]),([18,0,1,2,3,52,4,5],[30,39,52],[0,3]),([19,53,2,3,4,5],[44,69],[0,1]),([18,0,54,1,2,3,4,5],[13,116,8,6,69,44,39,42,40,84,25,338,335],[0,3]),([18,1,2,22,4,5],[44,69,39,52],[0,5,6,1,2,7]),([18,0,1,2,3,8,4,5],[12,39,65,29,37,293,296],[5,6,0]),([47,16,0,1,2,3,4,5],[12,39,8,6,65,25,84,73,339,42],[0]),([55,0,1,14,2,3,4,5],[23,22,84,69,72,116,39,40,25,42,13,52,44,70,250,264],[0,1]),([19,0,1,2,3,8,4,5],[12,293,56,37,39,35,65,22,25,296],[0,1]),([10,19,0,1,2,3,4,5],[12,294,56,39,71,25,22,73,124,310],[0]),([13,18,1,2,3,4,5],[39,44,12,52],[5,6,0,2]),([0,1,2,56,3,4,5],[65,69,124,39,40,42,70,72],[5,6,0,2]),([9,19,0,1,2,3,4,5],[307,136,275,12,132,116,22,25,67,65,309,308],[0]),([15,0,1,2,3,4,5,7],[13,87,39,15,71,52,64,41,73,8,17,51,23,44,175,158],[0,1,5,6]),([19,0,1,2,17,3,4,5],[273,189,12,56,22,25,65,67,124,52,69,148,286],[0,1]),([57,0,1,2,3,4,5],[39,1,44,40,12,70,72,64,118],[0]),([58,19,0,1,2,3,4,5],[12,22,42,70,116,39,40],[0]),([16,0,1,2,3,4,5,7],[15,52,41,73,64,6,25,175,158,340,339],[0,5,6]),([23,0,1,2,3,4,20,5],[12,41,226,40,65,1,44,73,116,25,69,42,322],[0]),([19,0,1,49,2,3,4,5],[1,12,56,44,70,65,25,72,69],[0,1]),([0,1,2,17,40,3,4,5],[39,124,65,118,185,311,187,273,117,312,189,315,149,330,148,286],[0,3,2,4,5,6]),([55,19,0,1,2,3,4,5],[25,22,84,44,116,39,23,72,15,78,13,52,69,40],[0,1]),([0,1,59,2,3,4,5],[39,5,44,42,12,70,72,64,118],[0]),([60,19,0,1,2,3,4,5],[1,56,136,44,70,25,15,78,73,146,69,72],[0,1]),([19,0,1,2,3,61,4,5],[5,56,25,136,72,42,22,15,78,70,40],[0,1]),([23,0,1,62,2,3,4,5],[1,40,70,13,39,25,44,73,15,78,52,72,69,42],[0,1]),([0,1,63,2,3,4,5],[35,69,42,70,72,67,71,118,64],[0,1]),([11,13,1,2,3,5],[65,69,39],[5,6,3,4]),([19,0,1,62,2,3,4,5],[1,42,13,39,25,70,73,15,78,52,40],[0,1]),([10,23,0,1,2,3,4,5],[12,41,83,39,71,1,25,73,124,310],[0]),([64,19,0,1,2,3,4,5],[5,12,25,56,72,22,44,70],[0]),([0,1,65,2,3,4,5],[5,35,44,42,70,72,67,71,118,64],[0,1]),([0,1,2,3,66,4,5],[52,65,69,44,42,40,72,70],[0,3,2,4,5,6]),([6,0,1,14,2,3,4,5],[176,171,229,75,39,23,22,146,13,44,40,225],[0,1]),([0,67,1,2,3,4,5],[52,65,69,42,40,72,70],[5,6]),([68,0,1,2,3,4,5],[52,65,44,40,42,72,70],[5,6]),([0,1,14,2,3,4,5,7],[87,264,250,175,73,13,22,23,39,158],[0,1]),([19,0,1,2,3,4,69,5],[12,25,84,22,44,23,65,116,39,69,40],[0]),([0,1,14,2,3,8,4,5],[176,206,293,75,37,35,39,22,23,296],[0,1]),([0,1,14,2,3,61,4,5],[23,75,22,84,166,39,25,69,40,321,341,250,264],[0,1]),([0,1,14,2,17,3,4,5],[187,189,176,75,67,22,23,65,124,52,44,40,286,148],[0,3,1]),([10,0,1,14,2,3,4,5],[176,167,294,75,39,22,23,73,124,310],[0]),([23,0,1,2,3,8,4,5],[12,29,83,39,65,37,35,1,25,296],[0,1]),([9,0,1,14,2,3,4,5],[164,166,275,176,170,116,22,23,67,308,309],[0]),([0,1,14,2,3,4,20,5],[176,91,184,196,73,116,22,23,44,40,322],[0]),([58,0,1,14,2,3,4,5],[22,176,15,23,41,69,116,39,44],[0]),([0,1,14,2,3,4,69,5],[23,176,84,22,69,40,15,42,116,39,44],[0]),([60,0,1,14,2,3,4,5],[22,51,75,166,39,69,23,42,73,146,44,40,250,264],[0,1]),([19,0,1,2,3,4,20,5],[12,184,152,65,44,73,116,22,25,69,40,322],[0]),([0,1,2,3,70,4,5],[39,44,42,52,70,72],[]),([0,1,2,71,3,4,5],[39,64,44,69,40,42,70,72],[0,3,2,4,5,6]),([0,1,14,49,2,3,4,5],[51,22,176,75,39,69,23,42,65,44,40],[0,1]),([6,23,0,1,2,3,4,5],[12,122,83,39,1,40,25,146,13,225],[0,1]),([58,23,0,1,2,3,4,5],[1,12,40,70,44,69,42,72],[0]),([64,23,0,1,2,3,4,5],[25,84,12,83,39,65,1,40],[0,1]),([55,23,0,1,2,3,4,5],[25,84,72,116,39,1,40,15,78,13,52,70],[0,1]),([72,0,1,2,3,4,5],[39,69,42,52,70,72],[0]),([9,15,0,1,2,3,4,5],[116,52,164,275,276,309,308],[0,5,6]),([0,1,2,3,73,4,5],[39,44,52,12,42,40,72,70,64],[5,6]),([47,18,0,1,2,3,4,5],[12,116,40,6,8,44,42,39,25,84,73,69,335],[0]),([9,0,1,2,3,4,5],[65,113,44,69,42,40,72,70],[0,3,2,4,5,6]),([15,0,1,2,3,4,44,5],[35,8,6,69,39,44,65,19,22,51,23,40],[0]),([74,0,1,2,3,4,5],[67,113,118,44,69,42,40,72,70],[0,3,2,4,5,6]),([15,0,1,2,3,8,4,5],[35,206,39,29,37,65,293,296],[5,6,0]),([23,14,2,3,4,5],[40,69],[0,1]),([13,0,1,2,40,3,4,5],[39,185,65,116,8,17,51,23,118,117,312,149,330],[0,5,6,2]),([75,18,0,1,2,3,4,5],[39,342,52,8,6,124,25,84,335,42,343],[0,2]),([23,0,1,2,17,3,4,5],[315,12,83,273,1,25,65,67,124,52,148,286],[0,1]),([9,23,0,1,2,3,4,5],[276,12,215,307,165,116,1,25,67,65,309,308],[0]),([23,0,1,2,3,4,69,5],[12,84,72,116,40,39,70],[0]),([0,1,14,62,2,3,4,5],[51,22,70,13,39,23,69,73,52,72,250,264],[0,1]),([76,0,1,2,3,4,5],[1,35,44,40,70,72,67,71,118,64],[0,1]),([0,1,2,3,77,4,5],[39,69,52,40,42,70,72],[5,6]),([47,15,0,1,2,3,4,5],[35,8,69,65,23,51,84,73,44],[0]),([60,23,0,1,2,3,4,5],[1,83,344,215,25,70,15,78],[0,1])]
def P_34_9_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [1,5,6,8,12,13,15,17,19,22,23,25,29,30,35,37,39,40,41,42,44,51,52,56,64,65,67,69,70,71,72,73,75,78,83,84,87,91,113,116,117,118,122,124,132,136,146,148,149,152,158,164,165,166,167,170,171,175,176,184,185,187,189,196,206,215,225,226,229,250,264,270,273,275,276,286,293,294,296,297,307,308,309,310,311,312,315,321,322,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_9_0 : checkNodesBT W_34 G_34 fmask_34 P_34_9_0 autos_34 bk_34_8 9 nd_34_9_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_9_0 : ∀ ns ∈ nd_34_9_0, Impossible G_34 9 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_8_ok chk_34_9_0
def nd_34_9_1 : List NodeSpec := [([78,0,1,2,17,3,4,5],[39,273,13,52,6,25,78,315,189,148,286,69],[0,2,5,6,8,9]),([12,0,79,1,2,3,4,5],[266,331,65,5,154,52,25,42,69,345,332],[0,8,4]),([6,19,0,1,2,3,4,5],[12,229,56,39,44,25,22,146,13,69,225],[0,1]),([0,1,2,17,3,80,4,5],[39,187,261,52,17,8,23,51,315,189,286,148,44],[0,2,5,6,8,9]),([23,0,1,2,3,61,4,5],[25,84,83,215,40,1,39,44,15,78,69,42,321,341],[0,1]),([0,1,2,81,3,4,5],[39,118,44,69,42,40,72,70],[0,3,2,4,5,6,1]),([64,0,1,14,2,3,4,5],[23,176,75,22,84,39,25,69,40],[0,1]),([0,1,82,2,3,4,5],[39,69,42,176,70,72,118],[0]),([18,1,2,3,22,4,5],[39,52,44],[0,5,6,2]),([83,0,1,2,3,4,5],[39,44,12,40,42,72,70,64,118],[5,6,0,2]),([0,1,2,3,84,4,5],[39,40,44,52,70,72],[])]
def P_34_9_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [1,5,6,8,12,13,15,17,22,23,25,39,40,42,44,51,52,56,64,65,69,70,72,75,78,83,84,118,146,148,154,176,187,189,215,225,229,261,266,273,286,315,321,331,332,341,345]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_9_1 : checkNodesBT W_34 G_34 fmask_34 P_34_9_1 autos_34 bk_34_8 9 nd_34_9_1 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma mem_34_9_1 : ∀ ns ∈ nd_34_9_1, Impossible G_34 9 (nodeValsBT W_34 ns).toFinset :=
  checkNodesBT_mem (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_8_ok chk_34_9_1
def nodes_34_9 : List NodeSpec := nd_34_9_0 ++ nd_34_9_1
def bk_34_9 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_9
set_option maxRecDepth 500000 in
lemma bk_34_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 9 xs.toFinset) bk_34_9 :=
  buildBucketsBT_of_mem (forall_append (mem_34_9_0) mem_34_9_1)
def nodes_34_10 : List NodeSpec := [([6,0,1,2,3,4,5],[65,39,44,69,42,40,72,70],[0,3,2,4,5,6,1]),([0,1,2,3,4,5,7],[71,64,44,69,40,42,70,72],[0,3,2,4,5,6,1]),([0,1,2,3,8,4,5],[65,39,44,69,40,42,70,72],[0,3,2,4,5,6,1]),([9,0,1,2,3,4,5],[52,65,67,44,69,40,42,70,72],[0,3,4,2,5,6]),([10,0,1,2,3,4,5],[65,39,44,69,42,40,72,70],[0,3,2,4,5,6]),([11,0,1,2,3,4,5],[65,44,42,40,72,70],[0,5,6,3,4]),([12,0,1,2,3,4,5],[44,65,39,69,42,40,72,70],[0,5,6,3,4,2]),([13,0,1,2,3,4,5],[69,65,39,44,42,40,72,70],[0,5,6,3,8,4,9]),([0,1,14,2,3,4,5],[69,42,70,72,71,64],[0,1]),([15,0,1,2,3,4,5],[69,44,42,40,72,70,71,64],[0,1,5,6,3,4,2,7]),([16,0,1,2,3,4,5],[44,39,52,69,42,40,72,70,71,64],[0,1,5,6,3,4,2,7]),([0,1,2,17,3,4,5],[39,65,44,69,40,42,70,72],[0,3,2,4,1,5,6,8,9]),([18,0,1,2,3,4,5],[44,69,42,40,72,70,71,64],[0,1,5,6,2,7]),([19,0,1,2,3,4,5],[44,42,72,70,71,64],[0,1]),([0,1,2,3,4,20,5],[65,113,44,69,40,42,70,72],[0,3,2,4,5,6]),([0,1,2,3,4,21,5],[65,69,40,42,70,72],[5,6,3,4,0]),([0,1,2,3,22,4,5],[69,39,52,44,40,42,70,72,71,64],[0,5,6,3,1,4,2,7]),([23,0,1,2,3,4,5],[40,44,72,70,71,64],[0,1])]
def P_34_10 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 [39,40,42,44,52,64,65,67,69,70,71,72,113]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_10 : checkNodesBT W_34 G_34 fmask_34 P_34_10 autos_34 bk_34_9 10 nodes_34_10 = true := by decide +kernel
def bk_34_10 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_10
set_option maxRecDepth 500000 in
lemma bk_34_10_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 10 xs.toFinset) bk_34_10 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_9_ok chk_34_10
def nodes_34_11 : List NodeSpec := [([0,1,2,3,4,5],[],[0,3,2,4,1,5,6,8,9])]
def P_34_11 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 R_34 slices_34 ps_34 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_11 : checkNodesBT W_34 G_34 fmask_34 P_34_11 autos_34 bk_34_10 11 nodes_34_11 = true := by decide +kernel
def bk_34_11 : BT (List (List Nat)) := buildBucketsBT W_34 nodes_34_11
set_option maxRecDepth 500000 in
lemma bk_34_11_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_34 11 xs.toFinset) bk_34_11 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound slices_34_ok) autos_34_ok bk_34_10_ok chk_34_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_34_ok : forestRootCheck R_34 G_34 [(VAR 0,15,14),(VAR 1,15,13),(VAR 2,15,11),(VAR 3,15,7),(VAR 4,25,9),(VAR 5,41,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_34_in : bucketContainsBT bk_34_11 R_34 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_34 : Lower R_34 G_34 12 := lower_of_forestBT root_34_ok bk_34_11_ok root_34_in
def wit : List PEqualNP.CircuitLowerBounds.Gate := [
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 7]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 14]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 12]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 17]⟩
]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by intro g hg; simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276682240 * 2 ^ 32 + 4261445632) ||| ((4276682240 * 2 ^ 32 + 4261445632) <<< 64)).testBit r.val := by decide +kernel
lemma root_eq : G_34 = ((4276682240 * 2 ^ 32 + 4261445632) ||| ((4276682240 * 2 ^ 32 + 4261445632) <<< 64)) := by decide
lemma low_root : Lower (varsOf 63) ((4276682240 * 2 ^ 32 + 4261445632) ||| ((4276682240 * 2 ^ 32 + 4261445632) <<< 64)) 12 := root_eq ▸ low_34
end PEqualNP.Outside.L_meta_12138
theorem PEqualNP.Outside.L_meta_12138 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682240 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_12138.table2_of_lower (4276682240 * 2 ^ 32 + 4261445632) (by decide) (by decide) (by decide) (by decide) 12 PEqualNP.Outside.L_meta_12138.low_root PEqualNP.Outside.L_meta_12138.wit PEqualNP.Outside.L_meta_12138.wo (by decide) PEqualNP.Outside.L_meta_12138.wit_mono PEqualNP.Outside.L_meta_12138.wit_eval s hcs
