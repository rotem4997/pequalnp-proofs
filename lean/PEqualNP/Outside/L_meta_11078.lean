import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_11078

private def targetEdges : List ℕ :=
  [0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6]

private def targetList (xs : List Bool) : Bool :=
  decide (∃ i < targetEdges.length / 2,
    xs.getD (targetEdges.getD (2 * i) 0) false = true ∧
    xs.getD (targetEdges.getD (2 * i + 1) 0) false = true)

private def target (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

private lemma ofFn_fin7 (x : Fin 7 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  simp [List.ofFn_succ]

private lemma target_eq_list (x : Fin 7 → Bool) :
    target x = targetList (List.ofFn x) := rfl

private def gs0 : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [9, 7]⟩,
   ⟨.or, [10, 6]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [13, 12]⟩,
   ⟨.or, [5, 11]⟩, ⟨.and, [15, 8]⟩, ⟨.or, [16, 14]⟩]

private lemma gs0_valid : ∀ g ∈ gs0,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [gs0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private lemma gs0_eval_list : ∀ (b0 b1 b2 b3 b4 b5 b6 : Bool),
    Circuit.eval ⟨gs0, 17⟩ [b0, b1, b2, b3, b4, b5, b6] =
    targetList [b0, b1, b2, b3, b4, b5, b6] := by
  decide

private lemma gs0_eval : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨gs0, 17⟩ (List.ofFn x) = target x := by
  intro x
  rw [target_eq_list, ofFn_fin7 x]
  exact gs0_eval_list (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

private abbrev Q := BitVec 16

private def norm (w : Q) := if w.getLsbD 0 then ~~~w else w

private def ops (a b : Q) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]

private def Trail (t : Q) (s : Finset Q) (n : ℕ) : Prop :=
  ∀ P : Finset Q → ℕ → Prop,
    (∀ k, P {t} k) →
    (∀ {r : Finset Q} {a b c : Q} {k : ℕ}, a ≠ b → c ∉ insert a (insert b r) →
      c ≠ 0 → c ∈ ops a b → P (insert c r) k → P (insert a (insert b r)) (k+1)) →
    P s n

private theorem Trail.done {t : Q} (k : ℕ) : Trail t {t} k :=
  fun _ done _ => done k

private theorem Trail.step {t a b c : Q} {r : Finset Q} {k : ℕ} (hab : a ≠ b)
    (hf : c ∉ insert a (insert b r)) (nz : c ≠ 0) (hc : c ∈ ops a b)
    (h : Trail t (insert c r) k) : Trail t (insert a (insert b r)) (k+1) :=
  fun P done step => step hab hf nz hc (h P done step)

private theorem trail_ind {t : Q} {P : Finset Q → ℕ → Prop} {s n} (h : Trail t s n)
    (done : ∀ k, P {t} k)
    (step : ∀ {r a b c k}, a ≠ b → c ∉ insert a (insert b r) → c ≠ 0 → c ∈ ops a b →
      Trail t (insert c r) k → P (insert c r) k → P (insert a (insert b r)) (k+1)) : P s n :=
  (h (fun r k => Trail t r k ∧ P r k) (fun k => ⟨Trail.done k, done k⟩)
    (fun hab hf nz hc h' => ⟨Trail.step hab hf nz hc h'.1, step hab hf nz hc h'.1 h'.2⟩)).2

private theorem trail_lift {t s n} (h : Trail t s n) : Trail t s (n+1) := by
  apply trail_ind (P := fun s n => Trail t s (n+1)) h
  · intro k; exact Trail.done _
  · intro r a b c k hab hf nz hc _ ih; exact .step hab hf nz hc ih

private theorem trail_mono {t s n m} (h : Trail t s n) (le : n ≤ m) : Trail t s m := by
  induction le with
  | refl => exact h
  | step _ ih => exact trail_lift ih

private theorem trail_card {t s n} (h : Trail t s n) : s.card ≤ n+1 := by
  apply trail_ind (P := fun s n => s.card ≤ n+1) h
  · simp
  · intro r a b c k hab fresh nz hc h ih
    have hn : c ∉ r := fun hh => fresh (by simp [hh])
    rw [Finset.card_insert_of_notMem hn] at ih
    have := Finset.card_insert_le a (insert b r)
    have := Finset.card_insert_le b r
    omega

private theorem trail_sep {t s n} (h : Trail t s n) (i j : ℕ) (hi : i < 16) (hj : j < 16)
    (same : ∀ x ∈ s, x.getLsbD i = x.getLsbD j) : t.getLsbD i = t.getLsbD j := by
  revert same
  apply trail_ind (P := fun s _ => (∀ x ∈ s, x.getLsbD i = x.getLsbD j) → t.getLsbD i = t.getLsbD j) h
  · intro k same; exact same _ (by simp)
  · intro r a b c k hab fresh nz hc h ih same
    apply ih
    have ha := same a (by simp)
    have hb := same b (by simp)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxr
    · simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;>
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hi, decide_eq_true hj, ha, hb]
    · exact same _ (by simp [hxr])

private def jumps : List ℕ := [1, 2, 4, 8]
private def dif (w : Q) (d : ℕ) := (w ^^^ (w >>> d)) &&& (BitVec.allOnes 16 >>> d)
private def unionDif (ws : List Q) (d : ℕ) : Q :=
  ws.foldr (fun w s => dif w d ||| s) 0
private def cover (t : Q) (ws : List Q) : Bool :=
  jumps.all fun d => (dif t d &&& unionDif ws d) == dif t d

private theorem bit_dif {w : Q} {d i : ℕ} (hi : i < 16) :
    (dif w d).getLsbD i = true ↔ i+d < 16 ∧ w.getLsbD i ≠ w.getLsbD (i+d) := by
  simp only [dif, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes, Bool.and_eq_true, decide_eq_true_eq, Nat.add_comm d i]
  cases w.getLsbD i <;> cases w.getLsbD (i + d) <;> simp

private theorem bit_union (ws : List Q) (d i : ℕ) :
    (unionDif ws d).getLsbD i = true ↔ ∃ w ∈ ws, (dif w d).getLsbD i = true := by
  induction ws with
  | nil => simp [unionDif]
  | cons w ws ih =>
    change (dif w d ||| unionDif ws d).getLsbD i = true ↔ _
    simp [ih]

private theorem trail_cover {t : Q} {ws : List Q} {n} (h : Trail t ws.toFinset n) :
    cover t ws = true := by
  apply List.all_eq_true.mpr
  intro d _
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  cases hd : (dif t d).getLsbD i with
  | false => rfl
  | true =>
    obtain ⟨hj, hne⟩ := (bit_dif hi).mp hd
    have ex : ∃ w ∈ ws, w.getLsbD i ≠ w.getLsbD (i+d) := by
      by_contra hn
      exact hne (trail_sep h i _ hi hj (fun x hx => by
        by_contra hneq
        exact hn ⟨x, List.mem_toFinset.mp hx, hneq⟩))
    obtain ⟨w, hw, hh⟩ := ex
    rw [(bit_union ws d i).mpr ⟨w, hw, (bit_dif hi).mpr ⟨hj,hh⟩⟩]
    rfl

private def pools (ws : List Q) (a b : Q) : List (List Q) :=
  [ws.filter (fun x => x != a && x != b), ws.filter (· != a), ws.filter (· != b), ws]

private def walk (t : Q) : ℕ → List Q → Bool
  | 0, ws => ws.contains t
  | n+1, ws =>
    ws.length ≤ n+2 && cover t ws &&
    (ws.contains t || ws.any fun a => ws.any fun b => a < b &&
      (pools ws a b).any fun r => r.length ≤ n &&
        (ops a b).any fun c => !(ws.contains c) && c != 0 && walk t n (c :: r))

private theorem pools_find {ws : List Q} {r : Finset Q} {a b : Q}
    (hw : ws.toFinset = insert a (insert b r)) (hn : ws.Nodup) :
    ∃ l ∈ pools ws a b, l.Nodup ∧ l.toFinset = r := by
  have mem (x : Q) : x ∈ ws ↔ x = a ∨ x = b ∨ x ∈ r := by
    rw [← List.mem_toFinset, hw]; simp
  by_cases ha : a ∈ r <;> by_cases hb : b ∈ r
  · exact ⟨ws, by simp [pools], hn, by simpa [ha,hb] using hw⟩
  · refine ⟨ws.filter (· != b), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind
  · refine ⟨ws.filter (· != a), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind
  · refine ⟨ws.filter (fun x => x != a && x != b), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind

private theorem ops_swap {a b c : Q} (h : c ∈ ops a b) : c ∈ ops b a := by
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at *
  rw [BitVec.and_comm a b, BitVec.or_comm a b] at h
  tauto


private theorem walk_pair {a b c : Q} {r : Finset Q} {t : Q} {k : ℕ}
    {ws : List Q} (hab : a < b) (hw : ws.toFinset = insert a (insert b r))
    (hn : ws.Nodup) (fresh : c ∉ insert a (insert b r)) (nz : c ≠ 0) (hc : c ∈ ops a b)
    (hdr : Trail t (insert c r) k)
    (ih : ∀ vs : List Q, vs.toFinset = insert c r → vs.Nodup → walk t k vs = true) :
    (ws.any fun a => ws.any fun b => a < b &&
      (pools ws a b).any fun r => r.length ≤ k &&
        (ops a b).any fun c => !(ws.contains c) && c != 0 && walk t k (c :: r)) = true := by
  obtain ⟨l, hl, hnl, hfl⟩ := pools_find hw hn
  have ha : a ∈ ws := by rw [← List.mem_toFinset, hw]; simp
  have hb : b ∈ ws := by rw [← List.mem_toFinset, hw]; simp
  have hnws : c ∉ ws := by simpa [← hw] using fresh
  have hnr : c ∉ r := fun h => fresh (by simp [h])
  have hnlc : c ∉ l := by simpa [← hfl] using hnr
  have hsize := trail_card hdr
  rw [Finset.card_insert_of_notMem hnr, ← hfl, List.toFinset_card_of_nodup hnl] at hsize
  apply List.any_eq_true.mpr
  refine ⟨a, ha, List.any_eq_true.mpr ⟨b, hb, ?_⟩⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hab, List.any_eq_true.mpr ⟨l, hl, ?_⟩⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, List.any_eq_true.mpr ⟨c, hc, ?_⟩⟩
  simp [hnws, nz, ih (c :: l) (by simp [hfl]) (List.nodup_cons.mpr ⟨hnlc, hnl⟩)] <;> exact nz

private theorem trail_walk {t s n} (h : Trail t s n) :
    ∀ ws : List Q, ws.toFinset = s → ws.Nodup → walk t n ws = true := by
  apply trail_ind (P := fun s n => ∀ ws : List Q, ws.toFinset = s → ws.Nodup → walk t n ws = true) h
  · intro k
    intro ws hw hn
    have ht : t ∈ ws := by rw [← List.mem_toFinset, hw]; simp
    cases k with
    | zero => simpa [walk] using ht
    | succ k =>
      have hcv := trail_cover (t := t) (n := k+1) (ws := ws) (hw ▸ Trail.done (t := t) (k+1))
      have hc := List.toFinset_card_of_nodup hn
      rw [hw, Finset.card_singleton] at hc
      simp [walk, ht, hcv, show ws.length ≤ k+2 by omega]
  · intro r a b c k hab fresh nz hc h ih
    intro ws hw hn
    have hall := Trail.step hab fresh nz hc h
    have hcv := trail_cover (ws := ws) (hw ▸ hall)
    have hsize := trail_card hall
    rw [← hw, List.toFinset_card_of_nodup hn] at hsize
    simp only [walk, show ws.length ≤ k+2 by omega, decide_true, hcv, Bool.true_and]
    rw [Bool.or_eq_true]
    right
    have hne : a.toNat ≠ b.toNat := fun he => hab (BitVec.eq_of_toNat_eq he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact walk_pair hlt hw hn fresh nz hc h ih
    · rw [Finset.insert_comm] at hw fresh
      exact walk_pair hgt hw hn fresh nz (ops_swap hc) h ih


private def readQ (x : Fin 16) (w : Q) := w.getLsbD x.val
private def Basis (gs : List Gate) :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem read_not (x : Fin 16) (w : Q) : readQ x (~~~w) = !(readQ x w) := by
  simp [readQ, x.isLt]
private theorem read_zero (x : Fin 16) : readQ x 0 = false := by simp [readQ]

private theorem getD_table (x : Fin 16) (ws : List Q) (i : ℕ) :
    (ws.map (readQ x)).getD i false = readQ x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [readQ]

private def gateQ (ws : List Q) (g : Gate) : Q :=
  match g.op, g.inputs with
  | .and, [] => ~~~0
  | .and, [i] => ws.getD i 0
  | .and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | .or, [] => 0
  | .or, [i] => ws.getD i 0
  | .or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | .not, [] => ~~~0
  | .not, i :: _ => ~~~(ws.getD i 0)
  | _, _ => 0

private theorem read_gateQ (x : Fin 16) (ws : List Q) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => (ws.map (readQ x)).getD i false) =
      readQ x (gateQ ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_table]
  cases op with
  | and =>
    match ins, hlen with
    | [], _ =>
      change true = readQ x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | [i], _ => simp [gateQ, GateOp.eval]
    | [i, j], _ => simp [gateQ, GateOp.eval, readQ, BitVec.getLsbD_and]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gateQ, GateOp.eval, readQ]
    | [i], _ => simp [gateQ, GateOp.eval]
    | [i, j], _ => simp [gateQ, GateOp.eval, readQ, BitVec.getLsbD_or]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil =>
      change true = readQ x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | cons i is =>
      exact (read_not x (ws.getD i 0)).symm
  | mod m => simp at hop
  | maj => simp at hop

private def wireQs (gs : List Gate) (ws : List Q) : List Q :=
  gs.foldl (fun vs g => vs ++ [gateQ vs g]) ws

private theorem read_wireQs (x : Fin 16) (gs : List Gate) (ws : List Q)
    (h : Basis gs) :
    (Circuit.wires ⟨gs, 0⟩ (ws.map (readQ x))) = (wireQs gs ws).map (readQ x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := read_gateQ x ws g (h g List.mem_cons_self)
    change Circuit.wires ⟨gs, 0⟩
        (ws.map (readQ x) ++ [g.op.eval (g.inputs.map fun i =>
          (ws.map (readQ x)).getD i false)]) =
      (wireQs gs (ws ++ [gateQ ws g])).map (readQ x)
    rw [hg, ← List.map_singleton, ← List.map_append]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

private def isBin (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .and, [_, _] => true
  | .or, [_, _] => true
  | _, _ => false

private def cost (gs : List Gate) : ℕ := gs.countP isBin

private def avail (ws : List Q) : Finset Q := insert 0 (ws.map norm).toFinset

private theorem norm_compl (u : Q) : norm (~~~u) = norm u := by
  unfold norm
  cases h : u.getLsbD 0 <;> simp only [BitVec.getLsbD_not, h] <;> simp

private theorem norm_pair (u v : Q) :
    norm (u &&& v) ∈ ops (norm u) (norm v) ∧ norm (u ||| v) ∈ ops (norm u) (norm v) := by
  unfold norm ops
  cases hu : u.getLsbD 0 <;> cases hv : v.getLsbD 0 <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, hu, hv] <;> simp [BitVec.not_and, BitVec.not_or, BitVec.and_comm, BitVec.or_comm]

private theorem norm_get (ws : List Q) (i : ℕ) : norm (ws.getD i 0) ∈ avail ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    simp [avail, List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [avail, norm]

private theorem fresh_pair {s : Finset Q} {c u v : Q} (hc : c ∈ ops u v) (hu : u ∈ s) (hv : v ∈ s)
    (hz : (0 : Q) ∈ s) (hf : c ∉ s) : u ≠ v := by
  rintro rfl
  simp only [ops, BitVec.and_self, BitVec.or_self, BitVec.and_not_self, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  grind

private theorem fresh_gate (ws : List Q) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hf : norm (gateQ ws g) ∉ avail ws) :
    isBin g = true ∧ ∃ a ∈ avail ws, ∃ b ∈ avail ws, a ≠ b ∧ norm (gateQ ws g) ∈ ops a b := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, len⟩ := hg
  have hz : norm 0 ∈ avail ws := by simp [avail, norm]
  have pair (i j : ℕ) {c : Q} (h : c ∈ ops (norm (ws.getD i 0)) (norm (ws.getD j 0)))
      (hn : c ∉ avail ws) :
      ∃ a ∈ avail ws, ∃ b ∈ avail ws, a ≠ b ∧ c ∈ ops a b :=
    ⟨_, norm_get ws i, _, norm_get ws j, fresh_pair h (norm_get ws i) (norm_get ws j)
      (by simp [avail]) hn, h⟩
  cases op with
  | and =>
    match ins, len with
    | [], _ => exact False.elim (hf (by change norm (~~~(0 : Q)) ∈ avail ws; rwa [norm_compl]))
    | [i], _ => exact False.elim (hf (norm_get ws i))
    | [i,j], _ => exact ⟨rfl, pair i j (norm_pair _ _).1 hf⟩
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, len with
    | [], _ => exact False.elim (hf hz)
    | [i], _ => exact False.elim (hf (norm_get ws i))
    | [i,j], _ => exact ⟨rfl, pair i j (norm_pair _ _).2 hf⟩
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    exfalso
    apply hf
    cases ins with
    | nil => change norm (~~~(0 : Q)) ∈ avail ws; rwa [norm_compl]
    | cons i is => simpa [gateQ, norm_compl] using norm_get ws i
  | mod m => simp at hop
  | maj => simp at hop

private theorem trail_extract {gs : List Gate} (ws : List Q) (hb : Basis gs) (o : ℕ) :
    ∃ s ⊆ avail ws, Trail (norm ((wireQs gs ws).getD o 0)) s (cost gs) := by
  induction gs generalizing ws with
  | nil => exact ⟨{_}, Finset.singleton_subset_iff.mpr (norm_get ws o), .done _⟩
  | cons g gs ih =>
    let c := norm (gateQ ws g)
    obtain ⟨s, hs, ht⟩ := ih (ws ++ [gateQ ws g]) (fun x hx => hb x (by simp [hx]))
    change ∃ s ⊆ avail ws, Trail (norm ((wireQs gs (ws ++ [gateQ ws g])).getD o 0)) s _
    have he : avail (ws ++ [gateQ ws g]) = insert c (avail ws) := by
      ext x; simp [avail, c]; tauto
    rw [he] at hs
    have hcost : cost gs ≤ cost (g :: gs) := by simp [cost, List.countP_cons]
    by_cases sub : s ⊆ avail ws
    · exact ⟨s, sub, trail_mono ht hcost⟩
    · have hn : c ∉ avail ws := by
        intro hh; rw [Finset.insert_eq_of_mem hh] at hs; exact sub hs
      have hcs : c ∈ s := by
        by_contra h
        apply sub; intro x hx
        exact (Finset.mem_insert.mp (hs hx)).resolve_left (by rintro rfl; exact h hx)
      have hr : s.erase c ⊆ avail ws := by
        intro x hx
        exact (Finset.mem_insert.mp (hs (Finset.mem_of_mem_erase hx))).resolve_left
          (Finset.ne_of_mem_erase hx)
      obtain ⟨hbin, a, ha, b, hbb, hab, hc⟩ := fresh_gate ws g (hb g (by simp)) hn
      have heq : insert c (s.erase c) = s := Finset.insert_erase hcs
      have hsub : insert a (insert b (s.erase c)) ⊆ avail ws := Finset.insert_subset_iff.mpr ⟨ha, Finset.insert_subset_iff.mpr ⟨hbb,hr⟩⟩
      refine ⟨_, hsub, ?_⟩
      rw [show cost (g :: gs) = cost gs + 1 by simp [cost, List.countP_cons, hbin]]
      exact .step hab (fun h => hn (hsub h)) (fun h => hn (h ▸ (by simp [avail])))
        hc (by rwa [heq])


private lemma wires_append (g1 g2 : List Gate) (x : List Bool) :
    Circuit.wires ⟨g1 ++ g2, 0⟩ x = Circuit.wires ⟨g2, 0⟩ (Circuit.wires ⟨g1, 0⟩ x) := by
  simp [Circuit.wires, List.foldl_append]

private lemma wires_append_singleton (pref : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨pref ++ [g], 0⟩ x =
    Circuit.wires ⟨pref, 0⟩ x ++ [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false)] := by
  rw [wires_append]
  rfl

private lemma wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    simp only [Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

private lemma wires_cons_getD_lt (pref : List Gate) (g : Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + pref.length) :
    (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD w false = (Circuit.wires ⟨pref, 0⟩ x).getD w false := by
  rw [wires_append_singleton]
  have hlen : (Circuit.wires ⟨pref, 0⟩ x).length = x.length + pref.length := wires_length pref x
  have hlt : w < (Circuit.wires ⟨pref, 0⟩ x).length := by omega
  simp [List.getD, List.getElem?_append_left hlt]

private lemma wires_cons_getD_eq (pref : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD (x.length + pref.length) false =
    g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) := by
  rw [wires_append_singleton]
  have hlen : (Circuit.wires ⟨pref, 0⟩ x).length = x.length + pref.length := wires_length pref x
  rw [← hlen]
  simp [List.getD]

private def Simple (D : List Bool → Prop) (p : ℕ) (f : List Bool → Bool) : Prop :=
  (∀ x, D x → f x = f (x.set p false)) ∨
  (∀ x, D x → f x = x.getD p false) ∨
  (∀ x, D x → f x = !(x.getD p false))

private lemma simple_const (D : List Bool → Prop) (p : ℕ) (b : Bool) :
    Simple D p (fun _ => b) := Or.inl (fun _ _ => rfl)

private lemma simple_not {D : List Bool → Prop} {p : ℕ} {f : List Bool → Bool}
    (hf : Simple D p f) : Simple D p (fun x => !(f x)) := by
  rcases hf with h1 | h2 | h3
  · exact Or.inl (fun x hx => by dsimp only; rw [h1 x hx])
  · exact Or.inr (Or.inr (fun x hx => by dsimp only; rw [h2 x hx]))
  · exact Or.inr (Or.inl (fun x hx => by dsimp only; rw [h3 x hx, Bool.not_not]))

private lemma wire_simple_all {D : List Bool → Prop} {p : ℕ} {pref : List Gate}
    (hlenD : ∀ x, D x → x.length = 7)
    (hpref : ∀ w < 7 + pref.length, Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false))
    (w : ℕ) : Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false) := by
  by_cases hw : w < 7 + pref.length
  · exact hpref w hw
  · left
    intro x hx
    dsimp only
    have h1 : (Circuit.wires ⟨pref, 0⟩ x).length = 7 + pref.length := by
      rw [wires_length, hlenD x hx]
    have h2 : (Circuit.wires ⟨pref, 0⟩ (x.set p false)).length = 7 + pref.length := by
      rw [wires_length, List.length_set, hlenD x hx]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private lemma gate_non_simple {D : List Bool → Prop} {p : ℕ} {pref : List Gate} {g : Gate}
    (hlenD : ∀ x, D x → x.length = 7)
    (hD : ∀ x, D x → D (x.set p false))
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hpref : ∀ w < 7 + pref.length, Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false))
    (hnot : ¬ Simple D p (fun x => g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false))) :
    isBin g = true ∧ ∃ g' : Gate,
      (g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
      isBin g' = false ∧
      ∀ x, D x → x.getD p false = false →
        g'.op.eval (g'.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) =
        g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  cases op with
  | not =>
    exfalso; apply hnot
    cases ins with
    | nil => exact simple_const D p true
    | cons a _ => exact simple_not (wire_simple_all hlenD hpref a)
  | mod m => simp at hop
  | maj => simp at hop
  | and =>
    match ins, hlen with
    | [], _ => exact False.elim (hnot (simple_const D p true))
    | [a], _ =>
      exfalso; apply hnot
      simpa [GateOp.eval] using wire_simple_all hlenD hpref a
    | [a, b], _ =>
      refine ⟨rfl, ?_⟩
      have ha := wire_simple_all hlenD hpref a
      have hb := wire_simple_all hlenD hpref b
      dsimp only [Simple] at ha hb
      rcases ha with ha1 | ha2 | ha3
      · rcases hb with hb1 | hb2 | hb3
        · exfalso; apply hnot; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha1 x hx, hb1 x hx]
        · refine ⟨⟨.or, []⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_nil, id_eq, Bool.and_true]
          rw [hb2 x hx, hxp, Bool.and_false]
        · refine ⟨⟨.or, [a]⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          rw [hb3 x hx, hxp, Bool.not_false, Bool.and_true]
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.or, []⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_nil, id_eq, Bool.and_true]
          rw [ha2 x hx, hxp, Bool.false_and]
        · exfalso; apply hnot; right; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha2 x hx, hb2 x hx, Bool.and_self]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha2 x hx, hb3 x hx, ha2 _ hx', hb3 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.or, [b]⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          rw [ha3 x hx, hxp, Bool.not_false, Bool.true_and]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha3 x hx, hb2 x hx, ha3 _ hx', hb2 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
        · exfalso; apply hnot; right; right; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha3 x hx, hb3 x hx, Bool.and_self]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => exact False.elim (hnot (simple_const D p false))
    | [a], _ =>
      exfalso; apply hnot
      simpa [GateOp.eval] using wire_simple_all hlenD hpref a
    | [a, b], _ =>
      refine ⟨rfl, ?_⟩
      have ha := wire_simple_all hlenD hpref a
      have hb := wire_simple_all hlenD hpref b
      dsimp only [Simple] at ha hb
      rcases ha with ha1 | ha2 | ha3
      · rcases hb with hb1 | hb2 | hb3
        · exfalso; apply hnot; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha1 x hx, hb1 x hx]
        · refine ⟨⟨.or, [a]⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [hb2 x hx, hxp, Bool.or_false]
        · refine ⟨⟨.and, []⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [hb3 x hx, hxp, Bool.not_false, Bool.or_true]
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.or, [b]⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha2 x hx, hxp, Bool.false_or]
        · exfalso; apply hnot; right; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha2 x hx, hb2 x hx, Bool.or_self]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha2 x hx, hb3 x hx, ha2 _ hx', hb3 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.and, []⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha3 x hx, hxp, Bool.not_false, Bool.true_or]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha3 x hx, hb2 x hx, ha3 _ hx', hb2 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
        · exfalso; apply hnot; right; right; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha3 x hx, hb3 x hx, Bool.or_self]
    | _ :: _ :: _ :: _, h => simp at h

private lemma elim_aux (D : List Bool → Prop) (p : ℕ)
    (hlenD : ∀ x, D x → x.length = 7)
    (hD : ∀ x, D x → D (x.set p false))
    (suff : List Gate) (pref : List Gate) (o : ℕ)
    (hb : Basis suff)
    (hpref : ∀ w < 7 + pref.length, Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false))
    (hnot : ¬ Simple D p (fun x => (Circuit.wires ⟨pref ++ suff, 0⟩ x).getD o false)) :
    ∃ suff' : List Gate, Basis suff' ∧ cost suff' < cost suff ∧
      ∀ x, D x → x.getD p false = false →
        Circuit.wires ⟨pref ++ suff', 0⟩ x = Circuit.wires ⟨pref ++ suff, 0⟩ x := by
  induction suff generalizing pref with
  | nil =>
    exfalso
    apply hnot
    simpa using wire_simple_all hlenD hpref o
  | cons g rest ih =>
    have hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hb g List.mem_cons_self
    have hrest : Basis rest := fun g' hg' => hb g' (List.mem_cons_of_mem _ hg')
    by_cases hgs : Simple D p (fun x => g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false))
    · have hpref' : ∀ w < 7 + (pref ++ [g]).length,
          Simple D p (fun x => (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD w false) := by
        intro w hw
        have hlen1 : (pref ++ [g]).length = pref.length + 1 := by simp
        by_cases hlt : w < 7 + pref.length
        · have heq : ∀ x, D x → (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD w false =
              (Circuit.wires ⟨pref, 0⟩ x).getD w false := fun x hx =>
            wires_cons_getD_lt pref g x w (by rw [hlenD x hx]; omega)
          have hwS := hpref w hlt
          dsimp only [Simple] at hwS
          rcases hwS with h1 | h2 | h3
          · exact Or.inl (fun x hx => by dsimp only; rw [heq x hx, heq _ (hD x hx), h1 x hx])
          · exact Or.inr (Or.inl (fun x hx => by dsimp only; rw [heq x hx, h2 x hx]))
          · exact Or.inr (Or.inr (fun x hx => by dsimp only; rw [heq x hx, h3 x hx]))
        · have hweq : w = 7 + pref.length := by omega
          subst hweq
          have heq : ∀ x, D x → (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD (7 + pref.length) false =
              g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) := fun x hx => by
            have := wires_cons_getD_eq pref g x
            rwa [hlenD x hx] at this
          dsimp only [Simple] at hgs
          rcases hgs with h1 | h2 | h3
          · exact Or.inl (fun x hx => by dsimp only; rw [heq x hx, heq _ (hD x hx), h1 x hx])
          · exact Or.inr (Or.inl (fun x hx => by dsimp only; rw [heq x hx, h2 x hx]))
          · exact Or.inr (Or.inr (fun x hx => by dsimp only; rw [heq x hx, h3 x hx]))
      have hnot' : ¬ Simple D p (fun x => (Circuit.wires ⟨(pref ++ [g]) ++ rest, 0⟩ x).getD o false) := by
        simpa [List.append_assoc] using hnot
      obtain ⟨rest', hbr', hcr', hwr'⟩ := ih (pref ++ [g]) hrest hpref' hnot'
      refine ⟨g :: rest', ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hg
        · exact hbr' x hx'
      · unfold cost at hcr' ⊢
        simp only [List.countP_cons]
        cases isBin g <;> simp <;> omega
      · intro x hx hxp
        simpa [List.append_assoc] using hwr' x hx hxp
    · obtain ⟨hbin, g', hg', hbin', hgeval⟩ := gate_non_simple hlenD hD hg hpref hgs
      refine ⟨g' :: rest, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hg'
        · exact hrest x hx'
      · unfold cost
        simp only [List.countP_cons, hbin, hbin']
        simp
      · intro x hx hxp
        have hstep : Circuit.wires ⟨pref ++ [g'], 0⟩ x = Circuit.wires ⟨pref ++ [g], 0⟩ x := by
          rw [wires_append_singleton, wires_append_singleton, hgeval x hx hxp]
        have h1 : pref ++ (g' :: rest) = (pref ++ [g']) ++ rest := by simp
        have h2 : pref ++ (g :: rest) = (pref ++ [g]) ++ rest := by simp
        calc Circuit.wires ⟨pref ++ (g' :: rest), 0⟩ x
            = Circuit.wires ⟨rest, 0⟩ (Circuit.wires ⟨pref ++ [g'], 0⟩ x) := by
                rw [h1]; exact wires_append (pref ++ [g']) rest x
          _ = Circuit.wires ⟨rest, 0⟩ (Circuit.wires ⟨pref ++ [g], 0⟩ x) := by rw [hstep]
          _ = Circuit.wires ⟨pref ++ (g :: rest), 0⟩ x := by
                rw [h2]; exact (wires_append (pref ++ [g]) rest x).symm

private lemma elim_step (D : List Bool → Prop) (p : ℕ)
    (hlenD : ∀ x, D x → x.length = 7)
    (hD : ∀ x, D x → D (x.set p false))
    (gs : List Gate) (o : ℕ) (hb : Basis gs)
    (hnot : ¬ Simple D p (fun x => Circuit.eval ⟨gs, o⟩ x)) :
    ∃ gs' : List Gate, Basis gs' ∧ cost gs' < cost gs ∧
      ∀ x, D x → x.getD p false = false →
        Circuit.eval ⟨gs', o⟩ x = Circuit.eval ⟨gs, o⟩ x := by
  have hpref : ∀ w < 7 + ([] : List Gate).length,
      Simple D p (fun x => (Circuit.wires ⟨[], 0⟩ x).getD w false) := by
    intro w _
    by_cases hwp : w = p
    · subst hwp
      exact Or.inr (Or.inl (fun _ _ => rfl))
    · left
      intro x _
      simp [Circuit.wires, List.getD, List.getElem?_set_ne (Ne.symm hwp)]
  have hnot' : ¬ Simple D p (fun x => (Circuit.wires ⟨[] ++ gs, 0⟩ x).getD o false) := hnot
  obtain ⟨gs', hb', hc', hw'⟩ := elim_aux D p hlenD hD gs [] o hb hpref hnot'
  refine ⟨gs', hb', hc', fun x hx hxp => ?_⟩
  change (Circuit.wires ⟨[] ++ gs', 0⟩ x).getD o false = (Circuit.wires ⟨[] ++ gs, 0⟩ x).getD o false
  rw [hw' x hx hxp]

private def D0 (x : List Bool) : Prop := x.length = 7
private def D1 (x : List Bool) : Prop := x.length = 7 ∧ x.getD 1 false = false
private def D2 (x : List Bool) : Prop := x.length = 7 ∧ x.getD 1 false = false ∧ x.getD 2 false = false

private lemma not_simple_D0 (f : List Bool → Bool) (hf : ∀ x, D0 x → f x = targetList x) :
    ¬ Simple D0 1 f := by
  rintro (h1 | h2 | h3)
  · have h := h1 [false, true, false, false, true, false, false] rfl
    rw [hf [false, true, false, false, true, false, false] rfl,
        hf ([false, true, false, false, true, false, false].set 1 false) rfl] at h
    exact absurd h (by decide)
  · have h := h2 [true, false, false, true, false, false, false] rfl
    rw [hf [true, false, false, true, false, false, false] rfl] at h
    exact absurd h (by decide)
  · have h := h3 [false, false, false, false, false, false, false] rfl
    rw [hf [false, false, false, false, false, false, false] rfl] at h
    exact absurd h (by decide)

private lemma not_simple_D1 (f : List Bool → Bool) (hf : ∀ x, D1 x → f x = targetList x) :
    ¬ Simple D1 2 f := by
  rintro (h1 | h2 | h3)
  · have h := h1 [false, false, true, false, false, true, false] ⟨rfl, rfl⟩
    rw [hf [false, false, true, false, false, true, false] ⟨rfl, rfl⟩,
        hf ([false, false, true, false, false, true, false].set 2 false) ⟨rfl, rfl⟩] at h
    exact absurd h (by decide)
  · have h := h2 [true, false, false, true, false, false, false] ⟨rfl, rfl⟩
    rw [hf [true, false, false, true, false, false, false] ⟨rfl, rfl⟩] at h
    exact absurd h (by decide)
  · have h := h3 [false, false, false, false, false, false, false] ⟨rfl, rfl⟩
    rw [hf [false, false, false, false, false, false, false] ⟨rfl, rfl⟩] at h
    exact absurd h (by decide)

private lemma not_simple_D2 (f : List Bool → Bool) (hf : ∀ x, D2 x → f x = targetList x) :
    ¬ Simple D2 4 f := by
  rintro (h1 | h2 | h3)
  · have h := h1 [true, false, false, false, true, false, false] ⟨rfl, rfl, rfl⟩
    rw [hf [true, false, false, false, true, false, false] ⟨rfl, rfl, rfl⟩,
        hf ([true, false, false, false, true, false, false].set 4 false) ⟨rfl, rfl, rfl⟩] at h
    exact absurd h (by decide)
  · have h := h2 [true, false, false, true, false, false, false] ⟨rfl, rfl, rfl⟩
    rw [hf [true, false, false, true, false, false, false] ⟨rfl, rfl, rfl⟩] at h
    exact absurd h (by decide)
  · have h := h3 [false, false, false, false, false, false, false] ⟨rfl, rfl, rfl⟩
    rw [hf [false, false, false, false, false, false, false] ⟨rfl, rfl, rfl⟩] at h
    exact absurd h (by decide)

private def inputs16 : List Q := [0xaaaa, 0, 0, 0xcccc, 0, 0xf0f0, 0xff00]
private def initial : List Q := [0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00]
private theorem init_avail : avail inputs16 = initial.toFinset := by decide +kernel
private def run (t : Q) (k : ℕ) := initial.sublists.any (walk t k)
private def tt4 : ℕ := 0xfee8

private def mkIn16 (i : Fin 16) : List Bool :=
  [i.val.testBit 0, false, false, i.val.testBit 1, false, i.val.testBit 2, i.val.testBit 3]

private theorem input_eval16 (i : Fin 16) :
    mkIn16 i = inputs16.map (readQ i) := by decide +revert +kernel

private theorem index_eval16 (i : Fin 16) :
    targetList (mkIn16 i) = tt4.testBit i.val := by decide +revert +kernel

private theorem eval_on_D0 {gs : List Gate} {o : ℕ}
    (hv : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target x)
    (x : List Bool) (hx : D0 x) :
    Circuit.eval ⟨gs, o⟩ x = targetList x := by
  have hlen : x.length = 7 := hx
  let f : Fin 7 → Bool := fun j => x.getD j.val false
  have hof : List.ofFn f = x := by
    apply List.ext_getElem (by simp [hlen])
    intro i hi1 hi2
    simp only [List.getElem_ofFn, f, List.getD, List.getElem?_eq_getElem hi2, Option.getD_some]
  have := hv f
  rw [hof, target_eq_list, hof] at this
  exact this

private theorem lower_run16 {gs : List Gate} (hb : Basis gs) {o : ℕ}
    (hv : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target x)
    (hc : cost gs ≤ 9) : run (norm (BitVec.ofNat 16 tt4)) 6 = true := by
  have h0 : ∀ x, D0 x → Circuit.eval ⟨gs, o⟩ x = targetList x := eval_on_D0 hv
  have hD0 : ∀ x, D0 x → D0 (x.set 1 false) := fun x hx => by
    show (x.set 1 false).length = 7
    simpa [D0] using hx
  obtain ⟨gs1, hb1, hc1, he1⟩ := elim_step D0 1 (fun _ h => h) hD0
    gs o hb (not_simple_D0 _ h0)
  have h1 : ∀ x, D1 x → Circuit.eval ⟨gs1, o⟩ x = targetList x := fun x hx =>
    (he1 x hx.1 hx.2).trans (h0 x hx.1)
  have hD1 : ∀ x, D1 x → D1 (x.set 2 false) := fun x hx =>
    ⟨by simp [hx.1], by simpa [List.getD, List.getElem?_set_ne] using hx.2⟩
  obtain ⟨gs2, hb2, hc2, he2⟩ := elim_step D1 2 (fun _ h => h.1) hD1
    gs1 o hb1 (not_simple_D1 _ h1)
  have h2 : ∀ x, D2 x → Circuit.eval ⟨gs2, o⟩ x = targetList x := fun x hx =>
    (he2 x ⟨hx.1, hx.2.1⟩ hx.2.2).trans (h1 x ⟨hx.1, hx.2.1⟩)
  have hD2 : ∀ x, D2 x → D2 (x.set 4 false) := fun x hx =>
    ⟨by simp [hx.1],
     by simpa [List.getD, List.getElem?_set_ne] using hx.2.1,
     by simpa [List.getD, List.getElem?_set_ne] using hx.2.2⟩
  obtain ⟨gs3, hb3, hc3, he3⟩ := elim_step D2 4 (fun _ h => h.1) hD2
    gs2 o hb2 (not_simple_D2 _ h2)
  have h3 : ∀ i : Fin 16, Circuit.eval ⟨gs3, o⟩ (mkIn16 i) = tt4.testBit i.val := fun i => by
    have hmD : D2 (mkIn16 i) := ⟨rfl, rfl, rfl⟩
    have hm4 : (mkIn16 i).getD 4 false = false := rfl
    rw [he3 (mkIn16 i) hmD hm4, h2 (mkIn16 i) hmD, index_eval16 i]
  have he : (wireQs gs3 inputs16).getD o 0 = BitVec.ofNat 16 tt4 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h := h3 ⟨i, hi⟩
    change (Circuit.wires ⟨gs3, 0⟩ (mkIn16 ⟨i, hi⟩)).getD o false = _ at h
    rw [input_eval16 ⟨i, hi⟩, read_wireQs _ _ _ hb3, getD_table] at h
    simpa only [readQ, BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and] using h
  obtain ⟨s, hs, ht⟩ := trail_extract inputs16 hb3 o
  rw [he] at ht
  rw [init_avail] at hs
  let ws := initial.filter (· ∈ s)
  have hw : ws.toFinset = s := by ext x; simp [ws]; exact fun a => List.mem_toFinset.mp (hs a)
  have hnd : initial.Nodup := by decide +kernel
  exact List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr List.filter_sublist,
    trail_walk (trail_mono ht (by omega)) ws hw (hnd.filter _)⟩

private theorem cost_lt {gs : List Gate} (hh : ∃ g ∈ gs, g.op = .not) : cost gs < gs.length := by
  have h : ∃ g ∈ gs, isBin g = false := by
    obtain ⟨g, hg, hop⟩ := hh
    exact ⟨g, hg, by simp [isBin, hop]⟩
  simpa [cost] using (List.countP_lt_length_iff.mpr h)

private def splitRun (t : Q) (n m j : ℕ) :=
  initial.sublists.any fun ws =>
    ws.length ≤ n+2 && cover t ws &&
    (ws.contains t || ws.any fun a => ws.any fun b => a < b &&
      (pools ws a b).any fun r => r.length ≤ n &&
        (ops a b).any fun c => (c.toNat % m == j) &&
          !(ws.contains c) && c != 0 && walk t n (c :: r))

private theorem partition_run {t : Q} {n m : ℕ} (hm : 0 < m)
    (hh : ∀ j : Fin m, splitRun t n m j.val = false) : run t (n+1) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨ws,hw,hg⟩ := List.any_eq_true.mp h
  simp only [walk, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hl, hv⟩, ht | ⟨a,ha,b,hb,hab,r,hr,hlen,c,hc,⟨hhc,hz⟩,hwalk⟩⟩ := hg
  · have hsplit : splitRun t n m 0 = true := by
      apply List.any_eq_true.mpr
      exact ⟨ws,hw, by simp [hl, hv, List.contains_iff_mem.mp ht]⟩
    have he := hh ⟨0,hm⟩
    change splitRun t n m 0 = false at he
    rw [he] at hsplit
    contradiction
  · let j : Fin m := ⟨c.toNat % m, Nat.mod_lt _ hm⟩
    have hsplit : splitRun t n m j.val = true := by
      apply List.any_eq_true.mpr
      refine ⟨ws,hw,?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact ⟨⟨hl,hv⟩, Or.inr ⟨a,ha,b,hb,hab,r,hr,hlen,c,hc,⟨⟨by simp [j],hhc⟩,hz⟩,hwalk⟩⟩
    rw [hh j] at hsplit
    contradiction


set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 0 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case1 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 1 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case2 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 2 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 3 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case4 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 4 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case5 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 5 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case6 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 6 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case7 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 7 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 8 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 9 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case10 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 10 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case11 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 11 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case12 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 12 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case13 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 13 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case14 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 14 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case15 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 15 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case16 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 16 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case17 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 17 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case18 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 18 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case19 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 19 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case20 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 20 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case21 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 21 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case22 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 22 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case23 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 23 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case24 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 24 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case25 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 25 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case26 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 26 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case27 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 27 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case28 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 28 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case29 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 29 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case30 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 30 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case31 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 31 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case32 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 32 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case33 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 33 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case34 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 34 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case35 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 35 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case36 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 36 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case37 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 37 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case38 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 38 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case39 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 39 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case40 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 40 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case41 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 41 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case42 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 42 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case43 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 43 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case44 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 44 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case45 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 45 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case46 : splitRun (norm (BitVec.ofNat 16 tt4)) 5 47 46 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem excluded0 : run (norm (BitVec.ofNat 16 tt4)) 6 = false := by
  apply partition_run (n := 5) (m := 47) (by decide)
  intro j
  fin_cases j
  · exact case0
  · exact case1
  · exact case2
  · exact case3
  · exact case4
  · exact case5
  · exact case6
  · exact case7
  · exact case8
  · exact case9
  · exact case10
  · exact case11
  · exact case12
  · exact case13
  · exact case14
  · exact case15
  · exact case16
  · exact case17
  · exact case18
  · exact case19
  · exact case20
  · exact case21
  · exact case22
  · exact case23
  · exact case24
  · exact case25
  · exact case26
  · exact case27
  · exact case28
  · exact case29
  · exact case30
  · exact case31
  · exact case32
  · exact case33
  · exact case34
  · exact case35
  · exact case36
  · exact case37
  · exact case38
  · exact case39
  · exact case40
  · exact case41
  · exact case42
  · exact case43
  · exact case44
  · exact case45
  · exact case46

end PEqualNP.Outside.L_meta_11078

open PEqualNP.Outside.L_meta_11078

theorem PEqualNP.Outside.L_meta_11078 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o hb _ hv
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · have basis : Basis gs := by
      intro g hg
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hb g hg
    refine ⟨gs0, 17, gs0_valid, ?_, gs0_eval⟩
    change 11 ≤ gs.length
    by_contra hlt
    have hcost := cost_lt hn
    have hrun := lower_run16 basis hv (by omega)
    rw [excluded0] at hrun
    contradiction
  · refine ⟨gs, o, ?_, le_rfl, hv⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hb g hg
    exact ⟨hop.imp_right (fun h => h.resolve_right (fun hnot => hn ⟨g, hg, hnot⟩)), hlen⟩
