import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- The live-wire extraction follows thctamm’s checked Petersen circuit search.
-- Each private test pair must retain a signal that separates its two inputs after a gate is applied.
namespace PEqualNP.Outside.L_meta_2427
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Mask := BitVec 96
abbrev Sig := Mask × Mask
def zz : Sig := (0,0)
def oo : Sig := (-1,-1)
def goal : Sig := (-1,0)
def bin (o : Bool) (a b : Sig) : Sig := if o then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
lemma bin_id (o : Bool) (x : Sig) : bin o x x = x := by cases x; cases o <;> simp [bin]
lemma bin_comm (o : Bool) (x y : Sig) : bin o x y = bin o y x := by cases o <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
def bit (s : Bool) (i : Fin 96) (x : Sig) : Bool := (if s then x.1 else x.2).getLsbD i
lemma bit_zz (s i) : bit s i zz = false := by cases s <;> simp [bit,zz]
lemma bit_oo (s i) : bit s i oo = true := by revert i; cases s <;> decide +kernel
lemma bit_goal (s i) : bit s i goal = s := by revert i; cases s <;> decide +kernel
lemma bit_bin (s i o) (x y : Sig) : bit s i (bin o x y) = if o then (bit s i x || bit s i y) else (bit s i x && bit s i y) := by cases s <;> cases o <;> simp [bit,bin]
def mark (x : Sig) : Mask := x.1 &&& ~~~x.2
lemma bit_mark (x : Sig) (i : Fin 96) : (mark x).getLsbD i = (bit true i x && !bit false i x) := by simp [mark,bit]
def isOr : GateOp → Bool | .or => true | _ => false
def isAnd : GateOp → Bool | .and => true | _ => false
def gv (w : List Sig) (g : Gate) : Sig := match g.inputs with
  | [] => if isAnd g.op then oo else zz
  | [i] => w.getD i zz
  | i::j::_ => bin (isOr g.op) (w.getD i zz) (w.getD j zz)
def execute : List Gate → List Sig → List Sig
  | [],w => w
  | g::gs,w => execute gs (w ++ [gv w g])
lemma get_bit (s i) (w : List Sig) (n : ℕ) : (w.map (bit s i)).getD n false = bit s i (w.getD n zz) := by simpa [bit_zz] using (List.getD_map w zz (bit s i) (n:=n))
lemma gate_bit (s i) (w : List Sig) (g : Gate) (legal : (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  simp only [get_bit]
  rcases legal with ⟨op,sz⟩
  rcases l:g.inputs with _|⟨u,us⟩
  · rcases op with op|op <;> simp [gv,l,op,isOr,isAnd,GateOp.eval,bit_oo,bit_zz]
  · rcases us with _|⟨v,vs⟩
    · rcases op with op|op <;> simp [gv,l,op,isOr,isAnd,GateOp.eval,get_bit]
    · have h : vs=[] := by rw [l] at sz; simpa using sz
      subst vs; rcases op with op|op <;> simp [gv,l,op,isOr,isAnd,GateOp.eval,get_bit,bit_bin]
lemma exec_bits (s i) (gs : List Gate) (w : List Sig) (legal : ∀ g∈gs, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) :
    (execute gs w).map (bit s i) = gs.foldl (fun v g => v++[g.op.eval (g.inputs.map fun j => v.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [execute,ih _ (fun a h => legal a (by simp [h]))]; simp [gate_bit s i w g (legal _ (by simp))]
def Live : ℕ → Finset Sig → Prop
  | 0,S => S = {goal}
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (o : Bool), a≠b ∧ bin o a b ∉ insert a (insert b U) ∧ S=insert a (insert b U) ∧ Live k (insert (bin o a b) U)
lemma Live.stop : Live 0 {goal} := rfl
lemma Live.step {k U a b o} (ab : a ≠ b) (fresh : bin o a b ∉ insert a (insert b U)) (next : Live k (insert (bin o a b) U)) : Live (k+1) (insert a (insert b U)) := ⟨U,a,b,o,ab,fresh,rfl,next⟩
lemma live_size {k S} (h : Live k S) : S.card ≤ k+1 := by
  induction k generalizing S with
  | zero => change S={goal} at h; simp [h]
  | succ k rec =>
    obtain ⟨U,a,b,o,_,fresh,rfl,tail⟩ := h
    have ih := rec tail
    have nf : bin o a b ∉ U := fun e => fresh (by simp [e])
    rw [Finset.card_insert_of_notMem nf] at ih
    have := Finset.card_insert_le a (insert b U); have := Finset.card_insert_le b U; omega
lemma live_witness {k S} (h : Live k S) (i : Fin 96) : ∃ x∈S, (mark x).getLsbD i = true := by
  induction k generalizing S with
  | zero => change S={goal} at h; subst S; exact ⟨goal,by simp,by simp [bit_mark,bit_goal]⟩
  | succ k rec =>
    obtain ⟨U,a,b,o,_,_,rfl,tail⟩ := h
    have ih := rec tail
    obtain ⟨x,hx,ok⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl|hx
    · rw [bit_mark,bit_bin,bit_bin] at ok
      have sep : (mark a).getLsbD i = true ∨ (mark b).getLsbD i = true := by
        simp only [bit_mark]; revert ok; cases o <;> cases bit true i a <;> cases bit true i b <;> cases bit false i a <;> cases bit false i b <;> decide
      rcases sep with e|e; exact ⟨a,by simp,e⟩; exact ⟨b,by simp,e⟩
    · exact ⟨x,by simp [hx],ok⟩
def pool (w : List Sig) := insert zz (insert oo w.toFinset)
lemma mem_read (w : List Sig) (i : ℕ) : w.getD i zz ∈ pool w := by
  simp only [List.getD_eq_getElem?_getD]; cases h:w[i]? with
  | none => simp [pool]
  | some x => have hx := List.mem_of_getElem? h; simp [pool,hx]
lemma extract (gs : List Gate) (w : List Sig) (ht : goal ∈ pool (execute gs w)) : ∃ k S, k≤gs.length ∧ Live k S ∧ S⊆pool w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{goal},by simp,Live.stop,Finset.singleton_subset_iff.mpr ht⟩
  | cons g gs ih =>
    let z := gv w g
    obtain ⟨k,S,hk,live,sub⟩ := ih (w++[z]) ht
    have parts {x} (hx : x∈S) : x∈pool w ∨ x=z := by have := sub hx; simpa [pool,or_assoc,or_left_comm,or_comm] using this
    by_cases seen : z∈pool w
    · exact ⟨k,S,by simp;omega,live,fun x hx => (parts hx).elim id (fun e => e ▸ seen)⟩
    by_cases needed : z∈S
    · let U := S.erase z
      have usub {x} (hx : x∈U) : x∈pool w := (parts (Finset.mem_erase.mp hx).2).resolve_right (Finset.mem_erase.mp hx).1
      have tail : Live k (insert z U) := by simpa [U,Finset.insert_erase needed] using live
      rcases l:g.inputs with _|⟨i,is⟩
      · have impossible : z∈pool w := by dsimp [z,gv]; rw [l]; change (if isAnd g.op then oo else zz) ∈ pool w; split <;> simp [pool]
        exact False.elim (seen impossible)
      · cases is with
        | nil => exact False.elim (seen (by simpa [z,gv,l] using mem_read w i))
        | cons j js =>
          let a := w.getD i zz; let b := w.getD j zz; let o := isOr g.op
          have ez : z=bin o a b := by simp [z,gv,l,a,b,o]
          have ha : a∈pool w := mem_read _ _; have hb : b∈pool w := mem_read _ _
          have ab : a≠b := by intro e; rw [ez,e,bin_id] at seen; contradiction
          have fresh : bin o a b ∉ insert a (insert b U) := by rw [←ez]; intro h; rcases Finset.mem_insert.mp h with e|h; exact seen (e ▸ ha); rcases Finset.mem_insert.mp h with e|h; exact seen (e ▸ hb); exact seen (usub h)
          exact ⟨k+1,_,by simp; omega,Live.step ab fresh (ez ▸ tail),by intro x hx; rcases Finset.mem_insert.mp hx with rfl|hx;exact ha;rcases Finset.mem_insert.mp hx with rfl|hx;exact hb;exact usub hx⟩
    · exact ⟨k,S,by simp; omega,live,fun x hx => (parts hx).resolve_right (fun e => needed (e ▸ hx))⟩
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def features : List (List ℕ) := [[0], [1], [2], [13], [14], [15], [17], [18], [19], [23], [24], [25], [13, 15], [14, 17], [15, 17], [15, 17, 18], [19, 23], [18, 19, 23], [17, 24], [17, 19, 24], [18, 25], [13, 19], [14, 23], [15, 23], [15, 23, 24], [24, 25]]
def raw : List Sig := [(0xffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaa),
(0xffffffff00000000,0xcccccccccccccccccccccccc),
(0xffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0),
(0xff000000ff,0x111111111111111111111111),
(0xff0000ff0000000000,0x30303030303030303030303),
(0xff000000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f),
(0xff00,0x555555555555555555555555),
(0xff000000000000,0x333333333333333333333333),
(0xff00000000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f),
(0xff0000,0x555555555555555555555555),
(0xff00000000000000,0x333333333333333333333333),
(0xff00000000000000ff000000,0x50505050505050505050505),
(0xff00000000ff000000ff,0x1f1f1f1f1f1f1f1f1f1f1f1f),
(0xff0000ff000000ff00,0x575757575757575757575757),
(0xff00000000000000ff00,0x5f5f5f5f5f5f5f5f5f5f5f5f),
(0xff0000ff00000000ff00,0x7f7f7f7f7f7f7f7f7f7f7f7f),
(0xff00000000000000ff0000,0x5f5f5f5f5f5f5f5f5f5f5f5f),
(0xff000000ff000000ff0000,0x7f7f7f7f7f7f7f7f7f7f7f7f),
(0xff0000000000ff00,0x777777777777777777777777),
(0xff0000ff0000000000ff00,0x7f7f7f7f7f7f7f7f7f7f7f7f),
(0xff00000000ff0000ff000000,0x373737373737373737373737),
(0xff0000000000ff000000ff,0x1f1f1f1f1f1f1f1f1f1f1f1f),
(0xff0000ff0000ff0000,0x575757575757575757575757),
(0xff000000000000ff0000,0x5f5f5f5f5f5f5f5f5f5f5f5f),
(0xff00ff00000000ff0000,0x7f7f7f7f7f7f7f7f7f7f7f7f),
(0xff000000ff000000ff000000,0x373737373737373737373737)]
def posRows : Array ℕ := #[8193, 131073, 8388609, 33554433, 8194, 16386, 262146, 16777218, 16388, 32772, 524292, 33554436]
def negRows : Array ℕ := #[59695104, 17612801, 42631170, 557059, 25567236, 17039365, 8519686, 7]
def sample (s : Bool) (i : Fin 96) (v : Fin 26) : Bool := (if s then posRows[i.val/8]?.getD 0 else negRows[i.val % 8]?.getD 0).testBit v.val
def input (x : Fin 26 → Bool) (j : Fin 26) := (features.getD j.val []).any fun n => x (Fin.ofNat 26 n)
def edge (x : Fin 26 → Bool) : Bool := decide (∃ p l : Fin 13, p.val < 3 ∧ (∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p=l+d) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)

def seeds : List Sig := raw.take 12
def others : List Sig := zz::oo::raw.drop 12
set_option maxRecDepth 4000 in
lemma raw_true_0 : ∀ j : Fin 8, let i : Fin 96 := ⟨0+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_true_1 : ∀ j : Fin 8, let i : Fin 96 := ⟨8+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_true_2 : ∀ j : Fin 8, let i : Fin 96 := ⟨16+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_true_3 : ∀ j : Fin 8, let i : Fin 96 := ⟨24+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_true_4 : ∀ j : Fin 8, let i : Fin 96 := ⟨32+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_true_5 : ∀ j : Fin 8, let i : Fin 96 := ⟨40+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_true_6 : ∀ j : Fin 8, let i : Fin 96 := ⟨48+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_true_7 : ∀ j : Fin 8, let i : Fin 96 := ⟨56+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_true_8 : ∀ j : Fin 8, let i : Fin 96 := ⟨64+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_true_9 : ∀ j : Fin 8, let i : Fin 96 := ⟨72+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_true_10 : ∀ j : Fin 8, let i : Fin 96 := ⟨80+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_true_11 : ∀ j : Fin 8, let i : Fin 96 := ⟨88+j.val,by omega⟩; raw.map (bit true i) = List.ofFn (input (sample true i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_0 : ∀ j : Fin 8, let i : Fin 96 := ⟨0+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_1 : ∀ j : Fin 8, let i : Fin 96 := ⟨8+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_2 : ∀ j : Fin 8, let i : Fin 96 := ⟨16+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_3 : ∀ j : Fin 8, let i : Fin 96 := ⟨24+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_4 : ∀ j : Fin 8, let i : Fin 96 := ⟨32+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_5 : ∀ j : Fin 8, let i : Fin 96 := ⟨40+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_6 : ∀ j : Fin 8, let i : Fin 96 := ⟨48+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_7 : ∀ j : Fin 8, let i : Fin 96 := ⟨56+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_8 : ∀ j : Fin 8, let i : Fin 96 := ⟨64+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_9 : ∀ j : Fin 8, let i : Fin 96 := ⟨72+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_10 : ∀ j : Fin 8, let i : Fin 96 := ⟨80+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
set_option maxRecDepth 4000 in
lemma raw_false_11 : ∀ j : Fin 8, let i : Fin 96 := ⟨88+j.val,by omega⟩; raw.map (bit false i) = List.ofFn (input (sample false i)) := by decide +kernel
lemma input_exact : ∀ s i, raw.map (bit s i) = List.ofFn (input (sample s i)) := by
  intro s i; cases s
  · let j : Fin 8 := ⟨i.val % 8,by omega⟩
    have v : i.val < 96 := i.isLt
    by_cases h0 : i.val < 8
    · have e : i = ⟨0+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_false_0 j
    by_cases h1 : i.val < 16
    · have e : i = ⟨8+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_false_1 j
    by_cases h2 : i.val < 24
    · have e : i = ⟨16+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_false_2 j
    by_cases h3 : i.val < 32
    · have e : i = ⟨24+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_false_3 j
    by_cases h4 : i.val < 40
    · have e : i = ⟨32+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_false_4 j
    by_cases h5 : i.val < 48
    · have e : i = ⟨40+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_false_5 j
    by_cases h6 : i.val < 56
    · have e : i = ⟨48+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_false_6 j
    by_cases h7 : i.val < 64
    · have e : i = ⟨56+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_false_7 j
    by_cases h8 : i.val < 72
    · have e : i = ⟨64+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_false_8 j
    by_cases h9 : i.val < 80
    · have e : i = ⟨72+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_false_9 j
    by_cases h10 : i.val < 88
    · have e : i = ⟨80+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_false_10 j
    have h11 : i.val < 96 := v
    have e : i = ⟨88+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
    exact e.symm ▸ raw_false_11 j
  · let j : Fin 8 := ⟨i.val % 8,by omega⟩
    have v : i.val < 96 := i.isLt
    by_cases h0 : i.val < 8
    · have e : i = ⟨0+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_true_0 j
    by_cases h1 : i.val < 16
    · have e : i = ⟨8+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_true_1 j
    by_cases h2 : i.val < 24
    · have e : i = ⟨16+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_true_2 j
    by_cases h3 : i.val < 32
    · have e : i = ⟨24+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_true_3 j
    by_cases h4 : i.val < 40
    · have e : i = ⟨32+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_true_4 j
    by_cases h5 : i.val < 48
    · have e : i = ⟨40+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_true_5 j
    by_cases h6 : i.val < 56
    · have e : i = ⟨48+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_true_6 j
    by_cases h7 : i.val < 64
    · have e : i = ⟨56+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_true_7 j
    by_cases h8 : i.val < 72
    · have e : i = ⟨64+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_true_8 j
    by_cases h9 : i.val < 80
    · have e : i = ⟨72+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_true_9 j
    by_cases h10 : i.val < 88
    · have e : i = ⟨80+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
      exact e.symm ▸ raw_true_10 j
    have h11 : i.val < 96 := v
    have e : i = ⟨88+j.val,by have := j.isLt;omega⟩ := by apply Fin.ext;dsimp [j];omega
    exact e.symm ▸ raw_true_11 j
def bits (m : ℕ) (k : Fin 26) := m.testBit k.val
lemma edge_true_0 : edge (bits 8193) = true := by decide +kernel
lemma edge_true_1 : edge (bits 131073) = true := by decide +kernel
lemma edge_true_2 : edge (bits 8388609) = true := by decide +kernel
lemma edge_true_3 : edge (bits 33554433) = true := by decide +kernel
lemma edge_true_4 : edge (bits 8194) = true := by decide +kernel
lemma edge_true_5 : edge (bits 16386) = true := by decide +kernel
lemma edge_true_6 : edge (bits 262146) = true := by decide +kernel
lemma edge_true_7 : edge (bits 16777218) = true := by decide +kernel
lemma edge_true_8 : edge (bits 16388) = true := by decide +kernel
lemma edge_true_9 : edge (bits 32772) = true := by decide +kernel
lemma edge_true_10 : edge (bits 524292) = true := by decide +kernel
lemma edge_true_11 : edge (bits 33554436) = true := by decide +kernel
lemma edge_true (j : Fin 12) : edge (bits (posRows[j.val]?.getD 0)) = true := by
  fin_cases j
  · exact edge_true_0
  · exact edge_true_1
  · exact edge_true_2
  · exact edge_true_3
  · exact edge_true_4
  · exact edge_true_5
  · exact edge_true_6
  · exact edge_true_7
  · exact edge_true_8
  · exact edge_true_9
  · exact edge_true_10
  · exact edge_true_11
lemma edge_false_0 : edge (bits 59695104) = false := by decide +kernel
lemma edge_false_1 : edge (bits 17612801) = false := by decide +kernel
lemma edge_false_2 : edge (bits 42631170) = false := by decide +kernel
lemma edge_false_3 : edge (bits 557059) = false := by decide +kernel
lemma edge_false_4 : edge (bits 25567236) = false := by decide +kernel
lemma edge_false_5 : edge (bits 17039365) = false := by decide +kernel
lemma edge_false_6 : edge (bits 8519686) = false := by decide +kernel
lemma edge_false_7 : edge (bits 7) = false := by decide +kernel
lemma edge_false (j : Fin 8) : edge (bits (negRows[j.val]?.getD 0)) = false := by
  fin_cases j
  · exact edge_false_0
  · exact edge_false_1
  · exact edge_false_2
  · exact edge_false_3
  · exact edge_false_4
  · exact edge_false_5
  · exact edge_false_6
  · exact edge_false_7
lemma edge_exact : ∀ s i, edge (sample s i) = s := by
  intro s i; cases s
  · exact edge_false ⟨i.val % 8,by omega⟩
  · exact edge_true ⟨i.val/8,by have := i.isLt; omega⟩
def must : List Sig := raw.take 12
def extras : List Sig := zz :: oo :: raw.drop 12
set_option maxRecDepth 4000 in
lemma uniqueBits : must.all (fun x => (List.finRange 96).any fun i => ((zz::oo::raw).filter fun a => (mark a).getLsbD i) == [x]) = true := by decide +kernel
lemma privateRows (x : Sig) (h : x∈must) : ∃ i : Fin 96, (zz::oo::raw).filter (fun a => (mark a).getLsbD i) = [x] := by
  obtain ⟨i,_,equal⟩ := List.any_eq_true.mp (List.all_eq_true.mp uniqueBits x h)
  exact ⟨i,eq_of_beq equal⟩
lemma rootInfo {k S} (live : Live k S) (sub : S⊆pool raw) : must.toFinset ⊆ S := by
  intro x hx
  obtain ⟨i,only⟩ := privateRows x (List.mem_toFinset.mp hx)
  obtain ⟨a,ha,yes⟩ := live_witness live i
  have mem : a ∈ zz::oo::raw := by have := sub ha; simpa [pool] using this
  have h : a ∈ (zz::oo::raw).filter (fun t => (mark t).getLsbD i) := List.mem_filter.mpr ⟨mem,yes⟩
  rw [only] at h; exact (List.mem_singleton.mp h) ▸ ha
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma get_goal (C : Circuit) (legal : Monotone2 C) (computes : ∀ x, circuitFun 26 C (input x) = edge x) : goal ∈ pool (execute C.gates raw) := by
  let z := (execute C.gates raw).getD C.output zz
  have good (s i) : bit s i z = s := by
    unfold z; rw [←get_bit,exec_bits s i C.gates raw (fun g hg => legal g hg),input_exact]
    exact (computes (sample s i)).trans (edge_exact s i)
  have id : z=goal := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq; intro i hi; exact (good true ⟨i,hi⟩).trans (bit_goal true ⟨i,hi⟩).symm
    · apply BitVec.eq_of_getLsbD_eq; intro i hi; exact (good false ⟨i,hi⟩).trans (bit_goal false ⟨i,hi⟩).symm
  exact id ▸ mem_read (execute C.gates raw) C.output
abbrev Row := List Sig
def both : List Bool := [false,true]
lemma mem_both (b : Bool) : b ∈ both := by cases b <;> decide
def cover : Row → Mask | [] => 0 | x::xs => mark x ||| cover xs
lemma cover_bit {v : Row} (i : Fin 96) (x : Sig) (hx : x∈v) (on : (mark x).getLsbD i = true) : (cover v).getLsbD i = true := by
  induction v with
  | nil => simp at hx
  | cons a as ih => rcases List.mem_cons.mp hx with rfl|h; simp [cover,on]; simp [cover,ih h]
lemma live_cover {v : Row} {k} (h : Live k v.toFinset) : cover v = -1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨x,mem,on⟩ := live_witness h ⟨i,hi⟩
  exact (cover_bit ⟨i,hi⟩ x (List.mem_toFinset.mp mem) on).trans (bit_goal true ⟨i,hi⟩).symm

def pick (b : Bool) (a : Sig) : Row := if b then [a] else []
def rest (v : Row) (a b : Sig) := v.filter fun x => !(x==a || x==b)
def sigLE (x y : Sig) := if x.1=y.1 then decide (x.2.toNat≤y.2.toNat) else decide (x.1.toNat<y.1.toNat)
def put (x : Sig) : Row → Row
  | [] => [x]
  | y::ys => if sigLE x y then x::y::ys else y::put x ys
def ordered : Row → Row | [] => [] | x::xs => put x (ordered xs)
lemma put_mem (x y : Sig) (xs : Row) : y∈put x xs ↔ y=x ∨ y∈xs := by
  induction xs with
  | nil => simp [put]
  | cons z zs ih => cases e : sigLE x z <;> simp [put,e,ih,or_left_comm]
lemma ordered_mem (x : Sig) (v : Row) : x∈ordered v ↔ x∈v := by induction v <;> simp_all [ordered,put_mem]
def canon (v : Row) : Row := (ordered v).dedup
lemma canon_set (v : Row) : (canon v).toFinset = v.toFinset := by ext x; simp [canon,ordered_mem]
def pairs : Row → List (Sig × Sig)
  | [] => []
  | a::t => (t.map fun b => (a,b)) ++ pairs t
lemma coverPair {v : Row} {a b : Sig} (ab : a ≠ b) (ha : a ∈ v) (hb : b ∈ v) :
    (a,b) ∈ pairs v ∨ (b,a) ∈ pairs v := by
  induction v with
  | nil => simp at ha
  | cons c v ih =>
    rcases List.mem_cons.mp ha with rfl|haTail
    · left; have h := (List.mem_cons.mp hb).resolve_left (Ne.symm ab); simp [pairs,h]
    rcases List.mem_cons.mp hb with rfl|hb
    · right; simp [pairs,haTail]
    rcases ih haTail hb with h|h; left; simp [pairs,h]; right; simp [pairs,h]


def roots : List Row := ([must] ++ (extras.map fun x => x::must) ++ ((pairs extras).map fun (a,b) => a::b::must)).map canon
lemma root_mem {k S} (small : k≤13) (live : Live k S) (sub : S⊆pool raw) : ∃ w∈roots, w.Nodup ∧ w.toFinset=S := by
  have all := rootInfo live sub
  let E := S \ must.toFinset
  have bound : E.card ≤ 2 := by
    have n : must.toFinset.card=12 := by decide +kernel
    have sz := live_size live
    dsimp [E]; rw [Finset.card_sdiff_of_subset all];omega
  have extra {x} (hx : x∈E) : x∈extras := by
    have inpool := sub (Finset.mem_sdiff.mp hx).1
    have part : pool raw = must.toFinset ∪ extras.toFinset := by decide +kernel
    rw [part] at inpool
    exact List.mem_toFinset.mp ((Finset.mem_union.mp inpool).resolve_left (Finset.mem_sdiff.mp hx).2)
  have rep : E ∪ must.toFinset = S := Finset.sdiff_union_of_subset all
  have one (v : Row) (hv : v∈[must] ++ (extras.map fun x => x::must) ++ ((pairs extras).map fun (a,b) => a::b::must)) (eqv : v.toFinset=S) : ∃ w∈roots, w.Nodup ∧ w.toFinset=S :=
    ⟨canon v,List.mem_map.mpr ⟨v,hv,rfl⟩,List.nodup_dedup _,(canon_set _).trans eqv⟩
  by_cases zero : E.card=0
  · have e := Finset.card_eq_zero.mp zero; apply one must (by simp);simpa [e] using rep
  by_cases single : E.card=1
  · obtain ⟨a,e⟩ := Finset.card_eq_one.mp single; have ha : a∈extras := extra (by simp [e])
    exact one (a::must) (by simp [ha]) (by simpa [e] using rep)
  obtain ⟨a,b,ab,e⟩ := Finset.card_eq_two.mp (show E.card=2 by omega)
  have ha : a∈extras := extra (by simp [e]); have hb : b∈extras := extra (by simp [e])
  rcases coverPair ab ha hb with pair|pair
  · apply one (a::b::must)
    · apply List.mem_append_right; exact List.mem_map.mpr ⟨(a,b),pair,rfl⟩
    · simpa [e] using rep
  · apply one (b::a::must)
    · apply List.mem_append_right; exact List.mem_map.mpr ⟨(b,a),pair,rfl⟩
    · simpa [e,Finset.insert_comm] using rep
def s0 : Sig := (0x0, 0x0)
def s1 : Sig := (0xff, 0x0)
def s2 : Sig := (0xff00, 0x0)
def s3 : Sig := (0xffff, 0x0)
def s4 : Sig := (0xff0000, 0x0)
def s5 : Sig := (0xffff00, 0x0)
def s6 : Sig := (0xffffff, 0x0)
def s7 : Sig := (0xffffffff, 0x0)
def s8 : Sig := (0xff000000ff, 0x0)
def s9 : Sig := (0xff000000000000, 0x0)
def s10 : Sig := (0xff00000000ff00, 0x0)
def s11 : Sig := (0xff000000ffff00, 0x0)
def s12 : Sig := (0xffff000000000000, 0x0)
def s13 : Sig := (0xffff000000ffff00, 0x0)
def s14 : Sig := (0x0, 0x10101010101010101010101)
def s15 : Sig := (0xff00, 0x10101010101010101010101)
def s16 : Sig := (0xffff00, 0x10101010101010101010101)
def s17 : Sig := (0x0, 0x20202020202020202020202)
def s18 : Sig := (0xff00, 0x20202020202020202020202)
def s19 : Sig := (0x0, 0x30303030303030303030303)
def s20 : Sig := (0xff000000000000, 0x30303030303030303030303)
def s21 : Sig := (0xffff000000000000, 0x30303030303030303030303)
def s22 : Sig := (0xff0000ff0000000000, 0x30303030303030303030303)
def s23 : Sig := (0xff0000ff000000ff00, 0x30303030303030303030303)
def s24 : Sig := (0xff0000ff0000ffff00, 0x30303030303030303030303)
def s25 : Sig := (0xff00ffff0000000000, 0x30303030303030303030303)
def s26 : Sig := (0xffffffff0000000000, 0x30303030303030303030303)
def s27 : Sig := (0xff00000000000000ff000000, 0x50505050505050505050505)
def s28 : Sig := (0xff00000000000000ff0000ff, 0x50505050505050505050505)
def s29 : Sig := (0xff00000000000000ff00ff00, 0x50505050505050505050505)
def s30 : Sig := (0xff00000000000000ff00ffff, 0x50505050505050505050505)
def s31 : Sig := (0xff00000000000000ffffff00, 0x50505050505050505050505)
def s32 : Sig := (0xff00000000000000ffffffff, 0x50505050505050505050505)
def s33 : Sig := (0xff00000000ff0000ff000000, 0x50505050505050505050505)
def s34 : Sig := (0xff000000ffff0000ff000000, 0x50505050505050505050505)
def s35 : Sig := (0xff00ff0000000000ff000000, 0x50505050505050505050505)
def s36 : Sig := (0xffffff0000000000ff000000, 0x50505050505050505050505)
def s37 : Sig := (0x0, 0x70707070707070707070707)
def s38 : Sig := (0xff000000000000000000, 0x70707070707070707070707)
def s39 : Sig := (0xffff000000000000000000, 0x70707070707070707070707)
def s40 : Sig := (0xff0000ff0000ff00ff000000, 0x70707070707070707070707)
def s41 : Sig := (0x0, 0xa0a0a0a0a0a0a0a0a0a0a0a)
def s42 : Sig := (0xff, 0xa0a0a0a0a0a0a0a0a0a0a0a)
def s43 : Sig := (0xff00, 0xa0a0a0a0a0a0a0a0a0a0a0a)
def s44 : Sig := (0xff000000000000000000, 0xa0a0a0a0a0a0a0a0a0a0a0a)
def s45 : Sig := (0xffff000000000000000000, 0xa0a0a0a0a0a0a0a0a0a0a0a)
def s46 : Sig := (0x0, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s47 : Sig := (0xff000000000000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s48 : Sig := (0xffff0000ff0000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s49 : Sig := (0xff00000000000000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s50 : Sig := (0xff000000000000000000ff, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s51 : Sig := (0xff0000000000000000ff00, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s52 : Sig := (0xff00000000000000ffff00, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s53 : Sig := (0xff000000000000ff000000, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s54 : Sig := (0xff00ff0000000000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s55 : Sig := (0xff00ff0000ff0000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s56 : Sig := (0xffff000000000000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s57 : Sig := (0xffff00000000000000ff00, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s58 : Sig := (0xffff000000000000ffff00, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s59 : Sig := (0xffffff0000ff0000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s60 : Sig := (0xffff000000000000ff000000, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s61 : Sig := (0xffff00ff0000ff00ff000000, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s62 : Sig := (0xffffff0000000000ff000000, 0xf0f0f0f0f0f0f0f0f0f0f0f)
def s63 : Sig := (0xff000000ff, 0x111111111111111111111111)
def s64 : Sig := (0xff0000ffff, 0x111111111111111111111111)
def s65 : Sig := (0xff00ff00ff, 0x111111111111111111111111)
def s66 : Sig := (0xff00ffffff, 0x111111111111111111111111)
def s67 : Sig := (0xffff0000ff, 0x111111111111111111111111)
def s68 : Sig := (0xffff00ffff, 0x111111111111111111111111)
def s69 : Sig := (0xffffffffff, 0x111111111111111111111111)
def s70 : Sig := (0xff00ff000000ff, 0x111111111111111111111111)
def s71 : Sig := (0xff00ff0000ffff, 0x111111111111111111111111)
def s72 : Sig := (0xff00ff00ffffff, 0x111111111111111111111111)
def s73 : Sig := (0xffff00ff000000ff, 0x111111111111111111111111)
def s74 : Sig := (0xffff00ff00ffffff, 0x111111111111111111111111)
def s75 : Sig := (0xff000000ff000000ff, 0x111111111111111111111111)
def s76 : Sig := (0xff00000000ff000000ff, 0x111111111111111111111111)
def s77 : Sig := (0xff0000000000ff000000ff, 0x111111111111111111111111)
def s78 : Sig := (0xffff00000000ff000000ff, 0x111111111111111111111111)
def s79 : Sig := (0xff0000ffff000000ff, 0x131313131313131313131313)
def s80 : Sig := (0xff000000000000ffff0000ff, 0x151515151515151515151515)
def s81 : Sig := (0x0, 0x171717171717171717171717)
def s82 : Sig := (0x0, 0x1f1f1f1f1f1f1f1f1f1f1f1f)
def s83 : Sig := (0xff000000ff, 0x1f1f1f1f1f1f1f1f1f1f1f1f)
def s84 : Sig := (0xff000000000000000000, 0x1f1f1f1f1f1f1f1f1f1f1f1f)
def s85 : Sig := (0xff00000000ff000000ff, 0x1f1f1f1f1f1f1f1f1f1f1f1f)
def s86 : Sig := (0xffff0000ffff000000ff, 0x1f1f1f1f1f1f1f1f1f1f1f1f)
def s87 : Sig := (0xff0000000000ff000000ff, 0x1f1f1f1f1f1f1f1f1f1f1f1f)
def s88 : Sig := (0xffff00000000ff000000ff, 0x1f1f1f1f1f1f1f1f1f1f1f1f)
def s89 : Sig := (0x0, 0x2a2a2a2a2a2a2a2a2a2a2a2a)
def s90 : Sig := (0xff00, 0x2a2a2a2a2a2a2a2a2a2a2a2a)
def s91 : Sig := (0xff000000000000, 0x333333333333333333333333)
def s92 : Sig := (0xff00ff000000ff, 0x333333333333333333333333)
def s93 : Sig := (0xff00000000000000, 0x333333333333333333333333)
def s94 : Sig := (0xff000000000000ff, 0x333333333333333333333333)
def s95 : Sig := (0xff0000000000ff00, 0x333333333333333333333333)
def s96 : Sig := (0xff00000000ffff00, 0x333333333333333333333333)
def s97 : Sig := (0xff000000ff000000, 0x333333333333333333333333)
def s98 : Sig := (0xff0000ff00000000, 0x333333333333333333333333)
def s99 : Sig := (0xff0000ff000000ff, 0x333333333333333333333333)
def s100 : Sig := (0xff0000ff0000ffff, 0x333333333333333333333333)
def s101 : Sig := (0xff0000ff00ffffff, 0x333333333333333333333333)
def s102 : Sig := (0xff00ff0000000000, 0x333333333333333333333333)
def s103 : Sig := (0xffff000000000000, 0x333333333333333333333333)
def s104 : Sig := (0xffff00000000ff00, 0x333333333333333333333333)
def s105 : Sig := (0xffff000000ffff00, 0x333333333333333333333333)
def s106 : Sig := (0xffff00ff00000000, 0x333333333333333333333333)
def s107 : Sig := (0xffff00ff000000ff, 0x333333333333333333333333)
def s108 : Sig := (0xffff00ff0000ffff, 0x333333333333333333333333)
def s109 : Sig := (0xffff00ff00ffffff, 0x333333333333333333333333)
def s110 : Sig := (0xff00ffff0000000000, 0x333333333333333333333333)
def s111 : Sig := (0xffff00000000000000, 0x333333333333333333333333)
def s112 : Sig := (0xffff00ff0000000000, 0x333333333333333333333333)
def s113 : Sig := (0xffff00ffff000000ff, 0x333333333333333333333333)
def s114 : Sig := (0xffffffff0000000000, 0x333333333333333333333333)
def s115 : Sig := (0xff00ff00000000000000, 0x333333333333333333333333)
def s116 : Sig := (0xff000000ff00000000000000, 0x333333333333333333333333)
def s117 : Sig := (0x0, 0x373737373737373737373737)
def s118 : Sig := (0xff000000000000, 0x373737373737373737373737)
def s119 : Sig := (0xff00000000000000ff000000, 0x373737373737373737373737)
def s120 : Sig := (0xff00000000ff0000ff000000, 0x373737373737373737373737)
def s121 : Sig := (0xff00000000ff00ffff0000ff, 0x373737373737373737373737)
def s122 : Sig := (0xff000000ff000000ff000000, 0x373737373737373737373737)
def s123 : Sig := (0xff000000ffff0000ff000000, 0x373737373737373737373737)
def s124 : Sig := (0xff0000ff00ffff00ff000000, 0x373737373737373737373737)
def s125 : Sig := (0x0, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s126 : Sig := (0xff000000000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s127 : Sig := (0xff000000000000000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s128 : Sig := (0xff0000ff000000000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s129 : Sig := (0xff0000ff00ff000000ff, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s130 : Sig := (0xff00ff00000000000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s131 : Sig := (0xff00ffff000000000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s132 : Sig := (0xff00ffff00ff000000ff, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s133 : Sig := (0xffff00ffff0000000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s134 : Sig := (0xff000000ff000000000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s135 : Sig := (0xff0000ff00000000000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s136 : Sig := (0xffff0000ff000000000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s137 : Sig := (0xffff0000ff00ff000000ff, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s138 : Sig := (0xffff00ffff000000000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s139 : Sig := (0xff00ff0000ff0000ff000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s140 : Sig := (0xff00ff0000ff00ffff0000ff, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s141 : Sig := (0xff00ff00ffff0000ff000000, 0x3f3f3f3f3f3f3f3f3f3f3f3f)
def s142 : Sig := (0xff00, 0x555555555555555555555555)
def s143 : Sig := (0xff0000, 0x555555555555555555555555)
def s144 : Sig := (0xff00ff, 0x555555555555555555555555)
def s145 : Sig := (0xffff00, 0x555555555555555555555555)
def s146 : Sig := (0xffffff, 0x555555555555555555555555)
def s147 : Sig := (0xffffff00, 0x555555555555555555555555)
def s148 : Sig := (0xff0000ffff, 0x555555555555555555555555)
def s149 : Sig := (0xff00ff0000, 0x555555555555555555555555)
def s150 : Sig := (0xff00ff00ff, 0x555555555555555555555555)
def s151 : Sig := (0xff00ffff00, 0x555555555555555555555555)
def s152 : Sig := (0xff00ffffff, 0x555555555555555555555555)
def s153 : Sig := (0xff0000ff0000, 0x555555555555555555555555)
def s154 : Sig := (0xff0000ffff00, 0x555555555555555555555555)
def s155 : Sig := (0xff000000ff0000, 0x555555555555555555555555)
def s156 : Sig := (0xff000000ffff00, 0x555555555555555555555555)
def s157 : Sig := (0xff00ff00ffffff, 0x555555555555555555555555)
def s158 : Sig := (0xff00000000ffff00, 0x555555555555555555555555)
def s159 : Sig := (0xffff000000ffff00, 0x555555555555555555555555)
def s160 : Sig := (0xff0000000000ffff00, 0x555555555555555555555555)
def s161 : Sig := (0xff000000000000ffff00, 0x555555555555555555555555)
def s162 : Sig := (0xff00000000000000ffff00, 0x555555555555555555555555)
def s163 : Sig := (0xff0000000000000000ffff00, 0x555555555555555555555555)
def s164 : Sig := (0xff00000000000000ff00ff00, 0x555555555555555555555555)
def s165 : Sig := (0xff00000000000000ffff0000, 0x555555555555555555555555)
def s166 : Sig := (0xff00000000000000ffffff00, 0x555555555555555555555555)
def s167 : Sig := (0xff000000000000ffffff00ff, 0x555555555555555555555555)
def s168 : Sig := (0xff000000000000ffffffffff, 0x555555555555555555555555)
def s169 : Sig := (0x0, 0x575757575757575757575757)
def s170 : Sig := (0xff00, 0x575757575757575757575757)
def s171 : Sig := (0xff0000ff0000000000, 0x575757575757575757575757)
def s172 : Sig := (0xff0000ff000000ff00, 0x575757575757575757575757)
def s173 : Sig := (0xff0000ff0000ff0000, 0x575757575757575757575757)
def s174 : Sig := (0xff0000ff0000ffff00, 0x575757575757575757575757)
def s175 : Sig := (0xff0000ffff0000ffff, 0x575757575757575757575757)
def s176 : Sig := (0x0, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s177 : Sig := (0xff00, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s178 : Sig := (0xff000000000000000000, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s179 : Sig := (0xff00000000000000ff00, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s180 : Sig := (0xff000000000000ff0000, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s181 : Sig := (0xff000000000000ffff00, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s182 : Sig := (0xff00000000ff0000ffff, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s183 : Sig := (0xff00000000ff00ffffff, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s184 : Sig := (0xffff0000ff000000ff00, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s185 : Sig := (0xffff0000ff0000ffff00, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s186 : Sig := (0xffff0000ffff0000ffff, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s187 : Sig := (0xff0000000000000000ff00, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s188 : Sig := (0xff00000000000000ff0000, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s189 : Sig := (0xffff00000000000000ff00, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s190 : Sig := (0xffff000000000000ffff00, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s191 : Sig := (0xffff00000000ff0000ffff, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s192 : Sig := (0xff00ff0000000000ff00ff00, 0x5f5f5f5f5f5f5f5f5f5f5f5f)
def s193 : Sig := (0x0, 0x707070707070707070707070)
def s194 : Sig := (0xff000000000000000000, 0x707070707070707070707070)
def s195 : Sig := (0x0, 0x777777777777777777777777)
def s196 : Sig := (0xff00, 0x777777777777777777777777)
def s197 : Sig := (0xff00000000ff00, 0x777777777777777777777777)
def s198 : Sig := (0xff000000ff0000, 0x777777777777777777777777)
def s199 : Sig := (0xff000000ffff00, 0x777777777777777777777777)
def s200 : Sig := (0xff00ff0000ffff, 0x777777777777777777777777)
def s201 : Sig := (0xff0000000000ff00, 0x777777777777777777777777)
def s202 : Sig := (0xff00000000ff0000, 0x777777777777777777777777)
def s203 : Sig := (0xffff000000ffff00, 0x777777777777777777777777)
def s204 : Sig := (0xff00ffff000000ff00, 0x777777777777777777777777)
def s205 : Sig := (0xff00ffff0000ffff00, 0x777777777777777777777777)
def s206 : Sig := (0xffffffff000000ff00, 0x777777777777777777777777)
def s207 : Sig := (0xff0000ff00ffff00ff00ff00, 0x777777777777777777777777)
def s208 : Sig := (0xff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s209 : Sig := (0xff000000000000, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s210 : Sig := (0xff000000000000000000, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s211 : Sig := (0xff0000ff00000000ff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s212 : Sig := (0xff0000ff000000ff0000, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s213 : Sig := (0xff0000ff000000ffff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s214 : Sig := (0xff0000ff00ff0000ffff, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s215 : Sig := (0xff00ff0000000000ff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s216 : Sig := (0xff00ff00000000ff0000, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s217 : Sig := (0xff00ffff00000000ff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s218 : Sig := (0xff00ffff000000ffff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s219 : Sig := (0xffff00ffff000000ff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s220 : Sig := (0xffff00ffff0000ffff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s221 : Sig := (0xff000000ff00000000ff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s222 : Sig := (0xff000000ff000000ff0000, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s223 : Sig := (0xff0000ff0000000000ff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s224 : Sig := (0xffff0000ff00000000ff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s225 : Sig := (0xffff0000ff000000ffff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s226 : Sig := (0xffff0000ff00ff0000ffff, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s227 : Sig := (0xffff00ffff00000000ff00, 0x7f7f7f7f7f7f7f7f7f7f7f7f)
def s228 : Sig := (0x0, 0x888888888888888888888888)
def s229 : Sig := (0x0, 0xa0a0a0a0a0a0a0a0a0a0a0a0)
def s230 : Sig := (0xffffffff, 0xaaaaaaaaaaaaaaaaaaaaaaaa)
def s231 : Sig := (0xffffffffff, 0xaaaaaaaaaaaaaaaaaaaaaaaa)
def s232 : Sig := (0xff00ffffffff, 0xaaaaaaaaaaaaaaaaaaaaaaaa)
def s233 : Sig := (0xff0000ffffffff, 0xaaaaaaaaaaaaaaaaaaaaaaaa)
def s234 : Sig := (0xff000000ffffffff, 0xaaaaaaaaaaaaaaaaaaaaaaaa)
def s235 : Sig := (0xff000000000000ffffffff, 0xaaaaaaaaaaaaaaaaaaaaaaaa)
def s236 : Sig := (0xffff0000000000ffffffff, 0xaaaaaaaaaaaaaaaaaaaaaaaa)
def s237 : Sig := (0xff0000ff00ffffffff, 0xabababababababababababab)
def s238 : Sig := (0xff0000000000ffffffff, 0xafafafafafafafafafafafaf)
def s239 : Sig := (0xff000000000000ffffffff, 0xafafafafafafafafafafafaf)
def s240 : Sig := (0xffff0000000000ffffffff, 0xafafafafafafafafafafafaf)
def s241 : Sig := (0xff00000000000000ffffffff, 0xafafafafafafafafafafafaf)
def s242 : Sig := (0xffffffffff, 0xbbbbbbbbbbbbbbbbbbbbbbbb)
def s243 : Sig := (0xff0000ffffffff, 0xbbbbbbbbbbbbbbbbbbbbbbbb)
def s244 : Sig := (0xff000000ffffffff, 0xbbbbbbbbbbbbbbbbbbbbbbbb)
def s245 : Sig := (0xffff0000ffffffff, 0xbbbbbbbbbbbbbbbbbbbbbbbb)
def s246 : Sig := (0xff00000000ffffffffff, 0xbfbfbfbfbfbfbfbfbfbfbfbf)
def s247 : Sig := (0xff0000ff0000ffffffff, 0xbfbfbfbfbfbfbfbfbfbfbfbf)
def s248 : Sig := (0xff00000000ff0000ffffffff, 0xbfbfbfbfbfbfbfbfbfbfbfbf)
def s249 : Sig := (0x0, 0xc0c0c0c0c0c0c0c0c0c0c0c0)
def s250 : Sig := (0xffffffff00000000, 0xcccccccccccccccccccccccc)
def s251 : Sig := (0xffffffff000000ff, 0xcccccccccccccccccccccccc)
def s252 : Sig := (0xffffffff0000ff00, 0xcccccccccccccccccccccccc)
def s253 : Sig := (0xffffffff00ffff00, 0xcccccccccccccccccccccccc)
def s254 : Sig := (0xffffffffff000000, 0xcccccccccccccccccccccccc)
def s255 : Sig := (0xffffffffff00000000, 0xcccccccccccccccccccccccc)
def s256 : Sig := (0xff00ffffffff00000000, 0xcccccccccccccccccccccccc)
def s257 : Sig := (0xff0000ffffffff00000000, 0xcccccccccccccccccccccccc)
def s258 : Sig := (0xffff00ffffffff00000000, 0xcccccccccccccccccccccccc)
def s259 : Sig := (0xff000000ffffffff00000000, 0xcccccccccccccccccccccccc)
def s260 : Sig := (0xff000000ffffffffff000000, 0xcdcdcdcdcdcdcdcdcdcdcdcd)
def s261 : Sig := (0xffffffffff00000000, 0xcfcfcfcfcfcfcfcfcfcfcfcf)
def s262 : Sig := (0xff00ffffffff00000000, 0xcfcfcfcfcfcfcfcfcfcfcfcf)
def s263 : Sig := (0xff0000ffffffff00000000, 0xcfcfcfcfcfcfcfcfcfcfcfcf)
def s264 : Sig := (0xffffffff000000ff, 0xdddddddddddddddddddddddd)
def s265 : Sig := (0xffffffff0000ff00, 0xdddddddddddddddddddddddd)
def s266 : Sig := (0xffffffff00ff0000, 0xdddddddddddddddddddddddd)
def s267 : Sig := (0xffffffff00ffff00, 0xdddddddddddddddddddddddd)
def s268 : Sig := (0xffffffffff0000ff00, 0xdfdfdfdfdfdfdfdfdfdfdfdf)
def s269 : Sig := (0xff00ffffffff000000ff, 0xdfdfdfdfdfdfdfdfdfdfdfdf)
def s270 : Sig := (0xff00ffffffff0000ff00, 0xdfdfdfdfdfdfdfdfdfdfdfdf)
def s271 : Sig := (0xffffffffffffffff, 0xeeeeeeeeeeeeeeeeeeeeeeee)
def s272 : Sig := (0xffffffff0000000000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0)
def s273 : Sig := (0xffffffff00000000000000ff, 0xf0f0f0f0f0f0f0f0f0f0f0f0)
def s274 : Sig := (0xffffffff000000000000ff00, 0xf0f0f0f0f0f0f0f0f0f0f0f0)
def s275 : Sig := (0xffffffff0000000000ff0000, 0xf0f0f0f0f0f0f0f0f0f0f0f0)
def s276 : Sig := (0xffffffff0000000000ffff00, 0xf0f0f0f0f0f0f0f0f0f0f0f0)
def s277 : Sig := (0xffffffff00000000ff000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0)
def s278 : Sig := (0xffffffff000000ff00000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0)
def s279 : Sig := (0xffffffff0000ff0000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0)
def s280 : Sig := (0xffffffff00ff000000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0)
def s281 : Sig := (0xffffffffff00000000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0)
def s282 : Sig := (0xffffffff000000ff000000ff, 0xf1f1f1f1f1f1f1f1f1f1f1f1)
def s283 : Sig := (0xffffffff0000ff0000000000, 0xf3f3f3f3f3f3f3f3f3f3f3f3)
def s284 : Sig := (0xffffffff00ff000000000000, 0xf3f3f3f3f3f3f3f3f3f3f3f3)
def s285 : Sig := (0xffffffffff00000000000000, 0xf3f3f3f3f3f3f3f3f3f3f3f3)
def s286 : Sig := (0xffffffffffff000000000000, 0xf3f3f3f3f3f3f3f3f3f3f3f3)
def s287 : Sig := (0xffffffff0000000000ff0000, 0xf5f5f5f5f5f5f5f5f5f5f5f5)
def s288 : Sig := (0xffffffff0000ff000000ff00, 0xf7f7f7f7f7f7f7f7f7f7f7f7)
def s289 : Sig := (0xffffffff00ff00000000ff00, 0xf7f7f7f7f7f7f7f7f7f7f7f7)
def s290 : Sig := (0xffffffff00000000ffffffff, 0xfafafafafafafafafafafafa)
def s291 : Sig := (0xffffffffffffffff00000000, 0xfcfcfcfcfcfcfcfcfcfcfcfc)
def s292 : Sig := (0xffffffff, 0xffffffffffffffffffffffff)
def s293 : Sig := (0xff0000ffffffff, 0xffffffffffffffffffffffff)
def s294 : Sig := (0xffffffff00000000, 0xffffffffffffffffffffffff)
def s295 : Sig := (0xffffffff0000ff00, 0xffffffffffffffffffffffff)
def s296 : Sig := (0xff0000ff00ffffffff, 0xffffffffffffffffffffffff)
def s297 : Sig := (0xff0000000000ffffffff, 0xffffffffffffffffffffffff)
def s298 : Sig := (0xff0000ff0000ffffffff, 0xffffffffffffffffffffffff)
def s299 : Sig := (0xff00ffffffff00000000, 0xffffffffffffffffffffffff)
def s300 : Sig := (0xff00ffffffff0000ff00, 0xffffffffffffffffffffffff)
def s301 : Sig := (0xff000000ffffffffff000000, 0xffffffffffffffffffffffff)
def s302 : Sig := (0xffffffff0000000000000000, 0xffffffffffffffffffffffff)
def s303 : Sig := (0xffffffff000000000000ff00, 0xffffffffffffffffffffffff)
def s304 : Sig := (0xffffffff000000ff000000ff, 0xffffffffffffffffffffffff)
def s305 : Sig := (0xffffffff00ff00000000ff00, 0xffffffffffffffffffffffff)
def s306 : Sig := (0xffffffffffffffffffffffff, 0xffffffffffffffffffffffff)
def stored13 (i : ℕ) := if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then (([s0,s142,s143,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row)) else (if i < 2 then (([s0,s142,s143,s230,s63,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row)) else (([s0,s142,s143,s230,s63,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row)))) else (if i < 5 then (if i < 4 then (([s0,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s0,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row))) else (if i < 6 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s85,s49,s87,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s120,s272] : Row))))) else (if i < 10 then (if i < 8 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s85,s128,s49,s27,s272] : Row)) else (if i < 9 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s85,s49,s134,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s197,s93,s250,s22,s47,s85,s49,s27,s272] : Row)))) else (if i < 12 then (if i < 11 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s85,s211,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s85,s49,s221,s27,s272] : Row))) else (if i < 13 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s272,s306] : Row)))))) else (if i < 21 then (if i < 17 then (if i < 15 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s128,s130,s49,s27,s272] : Row)) else (if i < 16 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s128,s49,s135,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s179,s128,s49,s27,s272] : Row)))) else (if i < 19 then (if i < 18 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s128,s49,s187,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s128,s211,s49,s27,s272] : Row))) else (if i < 20 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s128,s215,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s128,s49,s223,s27,s272] : Row))))) else (if i < 24 then (if i < 22 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row)) else (if i < 23 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s128,s49,s27,s272,s306] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s211,s216,s49,s27,s272] : Row)))) else (if i < 26 then (if i < 25 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s211,s49,s27,s272,s306] : Row))) else (if i < 27 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row))))))
def route13 (i : ℕ) := if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then ((0x15800500040 : ℕ)) else (if i < 2 then ((0x19801900080 : ℕ)) else ((0x1d801d001c0 : ℕ)))) else (if i < 5 then (if i < 4 then ((0x1901180018011900d800d9021801280129012000120122001000d000d2021001100112010801000004010c0104000000c000c40200 : ℕ)) else ((0x25802500240 : ℕ))) else (if i < 6 then ((0xdc009001d1809900980 : ℕ)) else ((0x138008800b980b9009c0 : ℕ))))) else (if i < 10 then (if i < 8 then ((0x124009401d580bd00a00 : ℕ)) else (if i < 9 then ((0x130008c01d980c100a40 : ℕ)) else ((0x1058148008800c500c40 : ℕ)))) else (if i < 12 then (if i < 11 then ((0x148009401dd80c900c80 : ℕ)) else ((0x151808c01e180cd00cc0 : ℕ))) else (if i < 13 then ((0x3d91a18179806180d9006500dc007c003981a59181818591e581a280d8006401a69165007501ca9124206880b5002d2124006880b5202d00ad00ad20d1023000b100b12164007401c990b40125406a00b0002c40b44125006a00b0402c00ac00ac40d00 : ℕ)) else ((0x1e980d500d40 : ℕ)))))) else (if i < 21 then (if i < 17 then (if i < 15 then ((0x12800ec81f181ed00f00 : ℕ)) else (if i < 16 then ((0x13400e801f581f500f40 : ℕ)) else ((0x140009401f9810901080 : ℕ)))) else (if i < 19 then (if i < 18 then ((0x145808c01fd810d110c0 : ℕ)) else ((0x201820101100 : ℕ))) else (if i < 20 then ((0x14500ec8209820501140 : ℕ)) else ((0x14e00e8020d820d01180 : ℕ))))) else (if i < 24 then (if i < 22 then ((0x4591a981768079812480650128807c004181ad9189818d921181b2812c006401b69176007901cd9128007c81b2004521cd21b620410189018d22110124006581a901ad216800e001008140406a010000304100c140006a0100403000fc00fc411c0 : ℕ)) else (if i < 23 then ((0x215821501200 : ℕ)) else ((0x14c013d821d821902180 : ℕ)))) else (if i < 26 then (if i < 25 then ((0x4d91b9817d80e5814880650145807c004981bd91918195922181ba814a006401be917d00e50145007c81ba004d21be20490191019522210148006581b901bd217c00e401b88144007e01b8004c41bcc1bc40480190019442200 : ℕ)) else ((0x225822502240 : ℕ))) else (if i < 27 then ((0x1628029817180359051908111c18065017180358051808101c190650084019981999229807c0161802a806c0058008011c28064008001c29064016e01560159005d015d1071015d00710161002a015da07180a8a05800f8306400f820640080a1c20064017100352051215d807180a8805800f8106400f80064008081c220640171003500510084819901992229007c8159805d806e005800a8105800a80058006c8058016200290081a1c10065808181c12065816c815481600028815c1070015c00700158005c016c0154015ca070815c807081608028015ec072808241c0806500f9506500f9406500aa4058015e407200f9e06580f9c0658082c1c00065817000344050415e8072808201c0c06500f9106500f9006500aa0058015e007200f9a06580f98065808281c040658170003400500086019801984228007e0 : ℕ)) else ((0x5591c5805581c5919d819d922d81c681c691c6005521c62055019d019d222d01c501c521c481c4005441c4c1c44054019c019c422c0 : ℕ))))))
def stored12 (i : ℕ) := if i < 70 then (if i < 35 then (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then (([s0,s2,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s0,s145,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row))) else (if i < 3 then (([s0,s145,s230,s63,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row)) else (([s0,s142,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 6 then (if i < 5 then (([s0,s142,s230,s63,s150,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s0,s145,s230,s63,s91,s93,s250,s22,s172,s47,s49,s27,s272] : Row))) else (if i < 7 then (([s0,s145,s230,s63,s91,s93,s250,s22,s47,s179,s49,s27,s272] : Row)) else (([s0,s145,s230,s63,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row))))) else (if i < 12 then (if i < 10 then (if i < 9 then (([s0,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s0,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row))) else (if i < 11 then (([s1,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row)))) else (if i < 14 then (if i < 13 then (([s2,s143,s230,s63,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row)) else (([s2,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 15 then (([s2,s143,s230,s63,s91,s93,s250,s22,s172,s47,s49,s27,s272] : Row)) else (if i < 16 then (([s2,s143,s230,s63,s91,s93,s250,s22,s173,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s91,s93,s250,s22,s47,s179,s49,s27,s272] : Row))))))) else (if i < 26 then (if i < 21 then (if i < 19 then (if i < 18 then (([s2,s143,s230,s63,s91,s93,s250,s22,s47,s180,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row))) else (if i < 20 then (([s2,s143,s230,s63,s91,s93,s250,s22,s47,s212,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 23 then (if i < 22 then (([s2,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s14,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 24 then (([s17,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 25 then (([s18,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s19,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 30 then (if i < 28 then (if i < 27 then (([s37,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s40,s272] : Row))) else (if i < 29 then (([s41,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s42,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 32 then (if i < 31 then (([s43,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s46,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 33 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s48,s49,s27,s272] : Row)) else (if i < 34 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s56,s27,s272] : Row)) else (([s81,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))))))) else (if i < 52 then (if i < 43 then (if i < 39 then (if i < 37 then (if i < 36 then (([s82,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s83,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 38 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s84,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s85,s49,s87,s27,s272] : Row)))) else (if i < 41 then (if i < 40 then (([s145,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s120,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s85,s128,s49,s27,s272] : Row))) else (if i < 42 then (([s145,s230,s63,s91,s93,s250,s22,s47,s85,s49,s134,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row))))) else (if i < 47 then (if i < 45 then (if i < 44 then (([s142,s145,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row)) else (([s142,s230,s63,s150,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row))) else (if i < 46 then (([s142,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s165,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s172,s47,s85,s49,s27,s272] : Row)))) else (if i < 49 then (if i < 48 then (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s85,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s85,s49,s187,s27,s272] : Row))) else (if i < 50 then (([s145,s230,s63,s91,s197,s93,s250,s22,s47,s85,s49,s27,s272] : Row)) else (if i < 51 then (([s145,s230,s63,s91,s93,s250,s22,s47,s85,s211,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s85,s49,s221,s27,s272] : Row))))))) else (if i < 61 then (if i < 56 then (if i < 54 then (if i < 53 then (([s145,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s272,s306] : Row))) else (if i < 55 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s86,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s88,s27,s272] : Row)))) else (if i < 58 then (if i < 57 then (([s89,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s90,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 59 then (([s125,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 60 then (([s142,s143,s230,s63,s91,s126,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s128,s130,s49,s27,s272] : Row)))))) else (if i < 65 then (if i < 63 then (if i < 62 then (([s145,s230,s63,s91,s93,s250,s22,s47,s128,s49,s135,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row))) else (if i < 64 then (([s142,s145,s230,s63,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row)) else (([s142,s230,s63,s150,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row)))) else (if i < 67 then (if i < 66 then (([s145,s230,s63,s91,s93,s250,s22,s172,s47,s128,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s128,s49,s27,s272] : Row))) else (if i < 68 then (([s145,s230,s63,s91,s93,s250,s22,s47,s128,s49,s187,s27,s272] : Row)) else (if i < 69 then (([s145,s230,s63,s91,s93,s250,s22,s47,s128,s211,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s128,s215,s49,s27,s272] : Row))))))))) else (if i < 105 then (if i < 87 then (if i < 78 then (if i < 74 then (if i < 72 then (if i < 71 then (([s145,s230,s63,s91,s93,s250,s22,s47,s128,s49,s223,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row))) else (if i < 73 then (([s145,s230,s63,s91,s93,s250,s22,s47,s128,s49,s27,s272,s306] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s129,s49,s27,s272] : Row)))) else (if i < 76 then (if i < 75 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s131,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s133,s49,s27,s272] : Row))) else (if i < 77 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s137,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s138,s27,s272] : Row))))) else (if i < 82 then (if i < 80 then (if i < 79 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s140,s272] : Row)) else (([s142,s208,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 81 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s213,s49,s27,s272] : Row)))) else (if i < 84 then (if i < 83 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s214,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s218,s49,s27,s272] : Row))) else (if i < 85 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s220,s49,s27,s272] : Row)) else (if i < 86 then (([s228,s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s237,s47,s49,s27,s272] : Row))))))) else (if i < 96 then (if i < 91 then (if i < 89 then (if i < 88 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s238,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s241,s272] : Row))) else (if i < 90 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s246,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s247,s49,s27,s272] : Row)))) else (if i < 93 then (if i < 92 then (([s142,s143,s230,s63,s91,s93,s250,s271,s22,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s292,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 94 then (([s142,s143,s230,s63,s91,s293,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 95 then (([s142,s143,s230,s63,s91,s93,s250,s22,s296,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s298,s49,s27,s272] : Row)))))) else (if i < 100 then (if i < 98 then (if i < 97 then (([s142,s145,s230,s63,s91,s93,s250,s22,s172,s47,s49,s27,s272] : Row)) else (([s142,s145,s230,s63,s91,s93,s250,s22,s173,s47,s49,s27,s272] : Row))) else (if i < 99 then (([s142,s145,s230,s63,s91,s93,s250,s22,s47,s179,s49,s27,s272] : Row)) else (([s142,s145,s230,s63,s91,s93,s250,s22,s47,s180,s49,s27,s272] : Row)))) else (if i < 102 then (if i < 101 then (([s142,s145,s230,s63,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s142,s145,s230,s63,s91,s93,s250,s22,s47,s212,s49,s27,s272] : Row))) else (if i < 103 then (([s142,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 104 then (([s142,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s142,s230,s63,s150,s91,s93,s250,s22,s172,s47,s49,s27,s272] : Row)))))))) else (if i < 123 then (if i < 114 then (if i < 109 then (if i < 107 then (if i < 106 then (([s142,s230,s63,s150,s91,s93,s250,s22,s173,s47,s49,s27,s272] : Row)) else (([s142,s230,s63,s150,s91,s93,s250,s22,s47,s179,s49,s27,s272] : Row))) else (if i < 108 then (([s142,s230,s63,s150,s91,s93,s250,s22,s47,s180,s49,s27,s272] : Row)) else (([s142,s230,s63,s150,s91,s197,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 111 then (if i < 110 then (([s142,s230,s63,s150,s91,s198,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s230,s63,s150,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row))) else (if i < 112 then (([s142,s230,s63,s150,s91,s93,s250,s22,s47,s212,s49,s27,s272] : Row)) else (if i < 113 then (([s142,s230,s63,s150,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s230,s63,s150,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row)))))) else (if i < 118 then (if i < 116 then (if i < 115 then (([s142,s230,s63,s91,s93,s250,s266,s22,s173,s47,s49,s27,s272] : Row)) else (([s142,s230,s63,s91,s93,s250,s22,s47,s180,s49,s27,s272,s287] : Row))) else (if i < 117 then (([s145,s230,s63,s91,s93,s250,s22,s172,s173,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s172,s47,s179,s49,s27,s272] : Row)))) else (if i < 120 then (if i < 119 then (([s145,s230,s63,s91,s93,s250,s22,s172,s47,s180,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s172,s47,s211,s49,s27,s272] : Row))) else (if i < 121 then (([s145,s230,s63,s91,s93,s250,s22,s172,s47,s212,s49,s27,s272] : Row)) else (if i < 122 then (([s145,s230,s63,s91,s93,s250,s22,s172,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s172,s47,s49,s27,s272,s306] : Row))))))) else (if i < 132 then (if i < 127 then (if i < 125 then (if i < 124 then (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s180,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s49,s187,s27,s272] : Row))) else (if i < 126 then (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s49,s188,s27,s272] : Row)) else (([s145,s230,s63,s91,s197,s93,s250,s22,s47,s179,s49,s27,s272] : Row)))) else (if i < 129 then (if i < 128 then (([s145,s230,s63,s91,s198,s93,s250,s22,s47,s179,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s211,s49,s27,s272] : Row))) else (if i < 130 then (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s212,s49,s27,s272] : Row)) else (if i < 131 then (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s49,s221,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s49,s222,s27,s272] : Row)))))) else (if i < 136 then (if i < 134 then (if i < 133 then (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s49,s27,s272,s306] : Row))) else (if i < 135 then (([s145,s230,s63,s91,s93,s250,s22,s47,s211,s216,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s211,s49,s223,s27,s272] : Row)))) else (if i < 138 then (if i < 137 then (([s145,s230,s63,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s211,s49,s27,s272,s306] : Row))) else (if i < 139 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 140 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s142,s143,s230,s91,s93,s250,s22,s47,s85,s49,s27,s272,s282] : Row)))))))))
def route12 (i : ℕ) := if i < 70 then (if i < 35 then (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then ((0x800000388038000c0 : ℕ)) else ((0x2080080 : ℕ))) else (if i < 3 then ((0x2480240 : ℕ)) else ((0x1980190 : ℕ)))) else (if i < 6 then (if i < 5 then ((0x1d8015003c003c20100 : ℕ)) else ((0x2180210 : ℕ))) else (if i < 7 then ((0x2880250 : ℕ)) else ((0x2c802c0 : ℕ))))) else (if i < 12 then (if i < 10 then (if i < 9 then ((0x1901480018014901880189030801c801c901c0001201c2001001800182030001400142010801000040 : ℕ)) else ((0x3480340 : ℕ))) else (if i < 11 then ((0x4c004400480048204001f004c0820d820d94c681f88205020521fc01fc4 : ℕ)) else ((0x7c8058048c848801700 : ℕ)))) else (if i < 14 then (if i < 13 then ((0x8080800490849001cc0 : ℕ)) else ((0x848084006401f404948211821194ca01f482110211249402000 : ℕ))) else (if i < 15 then ((0x888088021844988218c49802340 : ℕ)) else (if i < 16 then ((0x8c808c049c849c02344 : ℕ)) else ((0x988090021c44a884a0024c0 : ℕ))))))) else (if i < 26 then (if i < 21 then (if i < 19 then (if i < 18 then ((0x9c809404ac84a4024c4 : ℕ)) else ((0xa080a004b084b002800 : ℕ))) else (if i < 20 then ((0xa480a404b484b402804 : ℕ)) else ((0x549070805480709074807490a88078807890780054207820540074007420a800700070206880680050006000b0810904b8806c806c90b40060806c006c20b0010984b80064020042e80 : ℕ)))) else (if i < 23 then (if i < 22 then ((0xac80ac04bc84bc03140 : ℕ)) else ((0xe580e500e40 : ℕ))) else (if i < 24 then ((0xf080f000ec0 : ℕ)) else (if i < 25 then ((0xf880f800f40211821194ca02110211205c0 : ℕ)) else ((0x100810000fc0 : ℕ)))))) else (if i < 30 then (if i < 28 then (if i < 27 then ((0x110010d010c0 : ℕ)) else ((0x2158215911c04ce04ce211904cc84ccc1180 : ℕ))) else (if i < 29 then ((0x128012401200 : ℕ)) else ((0x1340130012c020d820d9 : ℕ)))) else (if i < 32 then (if i < 31 then ((0x140013c013802118211905c0 : ℕ)) else ((0x14c014901480 : ℕ))) else (if i < 33 then ((0x20a822284da04da215401500 : ℕ)) else (if i < 34 then ((0x14c015901580 : ℕ)) else ((0x15d815d015c0 : ℕ)))))))) else (if i < 52 then (if i < 43 then (if i < 39 then (if i < 37 then (if i < 36 then ((0x229816101600 : ℕ)) else ((0x231816501640 : ℕ))) else (if i < 38 then ((0x22d816901680 : ℕ)) else ((0x1b0016403f4816c0 : ℕ)))) else (if i < 41 then (if i < 40 then ((0x1e8015c018881880 : ℕ)) else ((0x1d4016803f8818c0 : ℕ))) else (if i < 42 then ((0x1e0016003fc81900 : ℕ)) else ((0x235817101700 : ℕ))))) else (if i < 47 then (if i < 45 then (if i < 44 then ((0x3918181025401120 : ℕ)) else ((0x3c5817d04d404d421740 : ℕ))) else (if i < 46 then ((0x4e084e49359818501780 : ℕ)) else ((0x4008264015c01890 : ℕ)))) else (if i < 49 then (if i < 48 then ((0x25401680408818d0 : ℕ)) else ((0x2700160040c81910 : ℕ))) else (if i < 50 then ((0x4048288015c01940 : ℕ)) else (if i < 51 then ((0x2880168041081980 : ℕ)) else ((0x29c01600414819c0 : ℕ))))))) else (if i < 61 then (if i < 56 then (if i < 54 then (if i < 53 then ((0x8d933c831080f981ad010101b00148008983409378837c941883b081a800fc03b492dc013103e891d4210c8184005921d4010c818420590180018021a004d0017c017c22b4012c03e4917802580112017400bc0 : ℕ)) else ((0x41c81a40 : ℕ))) else (if i < 55 then ((0x23e81ac01a80 : ℕ)) else ((0x23981b101b00 : ℕ)))) else (if i < 58 then (if i < 57 then ((0x1b881b801b40 : ℕ)) else ((0x1c081c001bc005c0 : ℕ))) else (if i < 59 then ((0x241824101c40 : ℕ)) else (if i < 60 then ((0x249824501c80 : ℕ)) else ((0x1d801c8842484200 : ℕ)))))) else (if i < 65 then (if i < 63 then (if i < 62 then ((0x1e401c4042884280 : ℕ)) else ((0x24d824d01cc0 : ℕ))) else (if i < 64 then ((0x3958395028001120 : ℕ)) else ((0x3c9835d04e804ec21d00 : ℕ)))) else (if i < 67 then (if i < 66 then ((0x4058294015c04050 : ℕ)) else ((0x28001680434842c0 : ℕ))) else (if i < 68 then ((0x28c8160043884300 : ℕ)) else (if i < 69 then ((0x43c843c0 : ℕ)) else ((0x28c01c8844484400 : ℕ))))))))) else (if i < 105 then (if i < 87 then (if i < 78 then (if i < 74 then (if i < 72 then (if i < 71 then ((0x2a001c4044884480 : ℕ)) else ((0x9593448308813d81d4810101d881480091834893808384944c83b881dc00fc03bc9308013d03ec91d8014883b8009523ec23bc209103800384244c01d401018344034822b801b401d08284011201d000c00 : ℕ))) else (if i < 73 then ((0x45084500 : ℕ)) else ((0x25d825501d40 : ℕ)))) else (if i < 76 then (if i < 75 then ((0x269825101d80 : ℕ)) else ((0x275827501dc0 : ℕ))) else (if i < 77 then ((0x261827101e00 : ℕ)) else ((0x26d826d01e40 : ℕ))))) else (if i < 82 then (if i < 80 then (if i < 79 then ((0x265826501e80 : ℕ)) else ((0x27d827d02780 : ℕ))) else (if i < 81 then ((0x281828102800 : ℕ)) else ((0x28d828d02840 : ℕ)))) else (if i < 84 then (if i < 83 then ((0x295828902880 : ℕ)) else ((0x2a1829102900 : ℕ))) else (if i < 85 then ((0x29e829e02980 : ℕ)) else (if i < 86 then ((0x2bd82a502a40 : ℕ)) else ((0x2c182c100e840e802a80 : ℕ))))))) else (if i < 96 then (if i < 91 then (if i < 89 then (if i < 88 then ((0x2d182c90105410502ac0 : ℕ)) else ((0x2cd82c5010544dc810504dcc2b00 : ℕ))) else (if i < 90 then ((0x2d982dd0116411602b40 : ℕ)) else ((0x2e182e10116411602b80 : ℕ)))) else (if i < 93 then (if i < 92 then ((0x2ed8144a14482e500e00146414602e40 : ℕ)) else ((0x2f982f902f00 : ℕ))) else (if i < 94 then ((0x30982fd02f40 : ℕ)) else (if i < 95 then ((0x311831103000 : ℕ)) else ((0x30d830d03040 : ℕ)))))) else (if i < 100 then (if i < 98 then (if i < 97 then ((0x37983790 : ℕ)) else ((0x37d837d01ec0238014e0 : ℕ))) else (if i < 99 then ((0x39983810 : ℕ)) else ((0x39d838501ec0250014e0 : ℕ)))) else (if i < 102 then (if i < 101 then ((0x3a183a10 : ℕ)) else ((0x3a583a501ec0284014e0 : ℕ))) else (if i < 103 then ((0x75934c8075834c9388838893a9838d838d938d0075238d20750388038823a9034c034c2208820800c402d0812a82208101024c1101024c0101023400e402d0012a024ca101824c81018220010182f000640 : ℕ)) else (if i < 104 then ((0x3ad83ad0 : ℕ)) else ((0x3b1833d04e104e123240 : ℕ)))))))) else (if i < 123 then (if i < 114 then (if i < 109 then (if i < 107 then (if i < 106 then ((0x3b5834101ec04e504e523244 : ℕ)) else ((0x3cd834504e904e923280 : ℕ))) else (if i < 108 then ((0x3d1834901ec04ed04ed23284 : ℕ)) else ((0x3b9836104f004f5232c0 : ℕ)))) else (if i < 111 then (if i < 110 then ((0x3bd836501ec04f404f8232c4 : ℕ)) else ((0x3d5836904fc050123300 : ℕ))) else (if i < 112 then ((0x3d9836d01ec0500050423304 : ℕ)) else (if i < 113 then ((0x79935480798354938c838c93dd83c083c09355007123552071034d034d2371021404cc0049035004d82508035024d8050820b844dc03204208031c4334031800680 : ℕ)) else ((0x3e18375050c050c23380 : ℕ)))))) else (if i < 118 then (if i < 116 then (if i < 115 then ((0x3e9820c03e50 : ℕ)) else ((0x21083f183ed0 : ℕ))) else (if i < 117 then ((0x3f58238023003f50 : ℕ)) else ((0x409825c022c03f90 : ℕ)))) else (if i < 120 then (if i < 119 then ((0x40d8260022803fd0 : ℕ)) else ((0x4118294022c04110 : ℕ))) else (if i < 121 then ((0x4158298022804150 : ℕ)) else (if i < 122 then ((0x7d9358807d835893908390941982d88136823c8101025c110c025c010c03c483c492d80136025ca10c83c4007d225c810c83c4207d039003902419023c010183580358230000f40512032482380200032400cc0 : ℕ)) else ((0x41d841d0 : ℕ))))))) else (if i < 132 then (if i < 127 then (if i < 125 then (if i < 124 then ((0x2500248045484210 : ℕ)) else ((0x2680244045584250 : ℕ))) else (if i < 126 then ((0x26c0240045884290 : ℕ)) else ((0x4358280022c04350 : ℕ)))) else (if i < 129 then (if i < 128 then ((0x439c284022804390 : ℕ)) else ((0x45c843d0 : ℕ))) else (if i < 130 then ((0x2840248046084410 : ℕ)) else (if i < 131 then ((0x28c8244046184450 : ℕ)) else ((0x2908240046484490 : ℕ)))))) else (if i < 136 then (if i < 134 then (if i < 133 then ((0x9d936082fc81428274010102680148009983649398839c946883cc825c00fc03d092e001b90280210c83c800812280010c83c8208103940394244d02540101835c035c22f4813803f0932c82500200032800d00 : ℕ)) else ((0x46c84510 : ℕ))) else (if i < 135 then ((0x290027c847484700 : ℕ)) else ((0x2a00278047584750 : ℕ)))) else (if i < 138 then (if i < 137 then ((0xa59368830c81c182888101028c814800a1836c93a083a4947883d4829400fc03d8930c01c1028c014883d400a523d820a103a003a42478028801018368036c230401bc033082840200033000d40 : ℕ)) else ((0x47c847c0 : ℕ))) else (if i < 139 then ((0x2cc804582f8808590a991551370810102f8808580a9815503709101015803a883a89480814802c4804e811800e4015013dc80fc015003dc90fc02ec02bc02c000f102c8112502c8012502c4004e02c8a1258170a0e401cc30fc01cc20fc0150a3dc00fc02f8008520a922c88125817080e401cc10fc01cc00fc015083dc20fc02f8008500a9015883a803a82480014882c080f1811e00e4017010e4017000e4011880e402cc00450155a370010181558370210182e482a482b0004082ac112002ac012002a800ec02e402a402aca12082ac812082b0804002d4812a8224833481010250110102500101023800e402d4012a0250a1018250810182240334010182f000c800d80 : ℕ)) else (if i < 140 then ((0xad937480ad837493ac83ac948483e083e093e000ad23e020ad03ac03ac2484037403742338833800dc0 : ℕ)) else ((0x4c8051004d104d00 : ℕ)))))))))
def stored11 (i : ℕ) := if i < 162 then (if i < 81 then (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then (([s0,s2,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s0,s5,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 3 then (([s0,s145,s230,s63,s103,s250,s22,s47,s85,s49,s27,s272] : Row)) else (if i < 4 then (([s0,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s0,s230,s63,s152,s91,s93,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 7 then (if i < 6 then (([s0,s145,s230,s63,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s0,s145,s230,s63,s91,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 8 then (([s0,s145,s230,s63,s91,s250,s22,s112,s47,s49,s27,s272] : Row)) else (if i < 9 then (([s0,s145,s230,s63,s103,s250,s22,s47,s49,s27,s120,s272] : Row)) else (([s0,s145,s230,s63,s103,s250,s22,s47,s128,s49,s27,s272] : Row)))))) else (if i < 15 then (if i < 12 then (if i < 11 then (([s0,s145,s230,s63,s197,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s0,s145,s230,s63,s103,s250,s22,s47,s211,s49,s27,s272] : Row))) else (if i < 13 then (([s0,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 14 then (([s0,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s0,s143,s230,s64,s91,s93,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 17 then (if i < 16 then (([s0,s142,s230,s150,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s1,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 18 then (([s1,s142,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 19 then (([s1,s142,s143,s230,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s1,s142,s143,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row))))))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then (([s2,s4,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s9,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 23 then (([s2,s143,s230,s63,s103,s250,s22,s47,s85,s49,s27,s272] : Row)) else (if i < 24 then (([s2,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s274] : Row))))) else (if i < 27 then (if i < 26 then (([s2,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s230,s63,s150,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 28 then (([s2,s143,s230,s63,s91,s95,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 29 then (([s2,s143,s230,s63,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s91,s103,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 35 then (if i < 32 then (if i < 31 then (([s2,s143,s230,s63,s91,s250,s22,s112,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s103,s250,s22,s47,s49,s27,s120,s272] : Row))) else (if i < 33 then (([s2,s143,s230,s63,s103,s250,s22,s47,s128,s49,s27,s272] : Row)) else (if i < 34 then (([s2,s142,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s103,s250,s22,s172,s47,s49,s27,s272] : Row))))) else (if i < 37 then (if i < 36 then (([s2,s143,s230,s63,s103,s250,s22,s173,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s103,s250,s22,s47,s179,s49,s27,s272] : Row))) else (if i < 38 then (([s2,s143,s230,s63,s103,s250,s22,s47,s180,s49,s27,s272] : Row)) else (if i < 39 then (([s2,s143,s230,s63,s197,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s198,s103,s250,s22,s47,s49,s27,s272] : Row)))))))) else (if i < 60 then (if i < 50 then (if i < 45 then (if i < 42 then (if i < 41 then (([s2,s143,s230,s63,s103,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s103,s250,s22,s47,s212,s49,s27,s272] : Row))) else (if i < 43 then (([s2,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 44 then (([s2,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s2,s143,s230,s64,s91,s93,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 47 then (if i < 46 then (([s2,s143,s230,s63,s91,s93,s250,s23,s47,s49,s27,s272] : Row)) else (([s3,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 48 then (([s5,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row)) else (if i < 49 then (([s5,s230,s63,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row)) else (([s142,s5,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 55 then (if i < 52 then (if i < 51 then (([s5,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s5,s230,s63,s91,s93,s250,s22,s172,s47,s49,s27,s272] : Row))) else (if i < 53 then (([s5,s230,s63,s91,s93,s250,s22,s47,s179,s49,s27,s272] : Row)) else (if i < 54 then (([s5,s230,s63,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s5,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 57 then (if i < 56 then (([s5,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s142,s143,s230,s8,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 58 then (([s14,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 59 then (([s15,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s17,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then (([s17,s142,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s18,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 63 then (([s18,s142,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 64 then (([s19,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s19,s142,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 67 then (if i < 66 then (([s142,s143,s230,s63,s20,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s93,s250,s22,s25,s47,s49,s27,s272] : Row))) else (if i < 68 then (([s37,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 69 then (([s37,s142,s143,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s38,s49,s27,s272] : Row)))))) else (if i < 75 then (if i < 72 then (if i < 71 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s40,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s56,s27,s40,s272] : Row))) else (if i < 73 then (([s41,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 74 then (([s41,s142,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s41,s142,s143,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row))))) else (if i < 78 then (if i < 76 then (([s42,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 77 then (([s42,s142,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s42,s142,s143,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row)))) else (if i < 79 then (([s43,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 80 then (([s43,s142,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s43,s142,s143,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row))))))))) else (if i < 121 then (if i < 101 then (if i < 91 then (if i < 86 then (if i < 83 then (if i < 82 then (([s142,s143,s230,s63,s91,s93,s250,s22,s44,s49,s27,s272] : Row)) else (([s46,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 84 then (([s46,s142,s143,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row)) else (if i < 85 then (([s145,s230,s63,s91,s93,s250,s22,s47,s48,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s103,s250,s22,s47,s48,s49,s27,s272] : Row))))) else (if i < 88 then (if i < 87 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s56,s27,s272] : Row)) else (([s81,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 89 then (([s82,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 90 then (([s145,s230,s63,s83,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s84,s49,s27,s272] : Row)))))) else (if i < 96 then (if i < 93 then (if i < 92 then (([s145,s230,s63,s103,s250,s22,s47,s85,s49,s87,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row))) else (if i < 94 then (([s230,s63,s152,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row)) else (if i < 95 then (([s230,s63,s91,s93,s250,s22,s47,s85,s49,s27,s166,s272] : Row)) else (([s145,s230,s63,s91,s99,s250,s22,s47,s85,s49,s27,s272] : Row))))) else (if i < 98 then (if i < 97 then (([s145,s230,s63,s91,s103,s250,s22,s47,s85,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s250,s22,s112,s47,s85,s49,s27,s272] : Row))) else (if i < 99 then (([s145,s230,s63,s103,s250,s22,s47,s85,s49,s27,s120,s272] : Row)) else (if i < 100 then (([s145,s230,s63,s103,s250,s22,s47,s85,s128,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s85,s49,s134,s27,s272] : Row))))))) else (if i < 111 then (if i < 106 then (if i < 103 then (if i < 102 then (([s145,s230,s63,s197,s103,s250,s22,s47,s85,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s85,s211,s49,s27,s272] : Row))) else (if i < 104 then (([s145,s230,s63,s103,s250,s22,s47,s85,s49,s221,s27,s272] : Row)) else (if i < 105 then (([s145,s230,s63,s103,s250,s22,s47,s85,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s85,s49,s27,s272,s306] : Row))))) else (if i < 108 then (if i < 107 then (([s145,s230,s63,s91,s93,s250,s22,s47,s86,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s103,s250,s22,s47,s86,s49,s27,s272] : Row))) else (if i < 109 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s88,s27,s272] : Row)) else (if i < 110 then (([s89,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s89,s142,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 116 then (if i < 113 then (if i < 112 then (([s90,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s90,s142,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 114 then (([s125,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 115 then (([s145,s230,s63,s91,s126,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row))))) else (if i < 118 then (if i < 117 then (([s230,s63,s152,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s129,s49,s27,s272] : Row))) else (if i < 119 then (([s145,s230,s63,s91,s93,s250,s22,s47,s131,s49,s27,s272] : Row)) else (if i < 120 then (([s145,s230,s63,s91,s93,s250,s22,s47,s133,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s137,s27,s272] : Row)))))))) else (if i < 141 then (if i < 131 then (if i < 126 then (if i < 123 then (if i < 122 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s138,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s140,s272] : Row))) else (if i < 124 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 125 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s273] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s274] : Row))))) else (if i < 128 then (if i < 127 then (([s142,s143,s230,s63,s91,s93,s250,s22,s47,s49,s27,s277] : Row)) else (([s142,s144,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 129 then (([s142,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 130 then (([s142,s230,s63,s149,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s230,s63,s152,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 136 then (if i < 133 then (if i < 132 then (([s142,s230,s63,s153,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s230,s63,s91,s155,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 134 then (([s142,s230,s63,s91,s93,s250,s22,s47,s49,s27,s167,s272] : Row)) else (if i < 135 then (([s142,s230,s63,s91,s93,s250,s22,s173,s47,s49,s27,s275] : Row)) else (([s142,s230,s63,s91,s93,s250,s22,s47,s180,s49,s27,s275] : Row))))) else (if i < 138 then (if i < 137 then (([s145,s230,s63,s148,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s152,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 139 then (([s169,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 140 then (([s170,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s171,s47,s49,s27,s272] : Row))))))) else (if i < 151 then (if i < 146 then (if i < 143 then (if i < 142 then (([s145,s230,s63,s91,s93,s250,s22,s172,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s174,s47,s49,s27,s272] : Row))) else (if i < 144 then (([s145,s230,s63,s91,s93,s250,s22,s175,s47,s49,s27,s272] : Row)) else (if i < 145 then (([s176,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s177,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 148 then (if i < 147 then (([s145,s230,s63,s91,s93,s250,s22,s47,s178,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s179,s49,s27,s272] : Row))) else (if i < 149 then (([s145,s230,s63,s91,s93,s250,s22,s47,s181,s49,s27,s272] : Row)) else (if i < 150 then (([s145,s230,s63,s91,s93,s250,s22,s47,s182,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s183,s49,s27,s272] : Row)))))) else (if i < 156 then (if i < 153 then (if i < 152 then (([s145,s230,s63,s91,s93,s250,s22,s47,s184,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s185,s49,s27,s272] : Row))) else (if i < 154 then (([s145,s230,s63,s91,s93,s250,s22,s47,s186,s49,s27,s272] : Row)) else (if i < 155 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s189,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s190,s27,s272] : Row))))) else (if i < 159 then (if i < 157 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s191,s27,s272] : Row)) else (if i < 158 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s192,s272] : Row)) else (([s208,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 160 then (([s145,s230,s63,s91,s209,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 161 then (([s145,s230,s63,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s213,s49,s27,s272] : Row)))))))))) else (if i < 243 then (if i < 202 then (if i < 182 then (if i < 172 then (if i < 167 then (if i < 164 then (if i < 163 then (([s145,s230,s63,s91,s93,s250,s22,s47,s214,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s217,s49,s27,s272] : Row))) else (if i < 165 then (([s145,s230,s63,s91,s93,s250,s22,s47,s218,s49,s27,s272] : Row)) else (if i < 166 then (([s145,s230,s63,s91,s93,s250,s22,s47,s219,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s220,s49,s27,s272] : Row))))) else (if i < 169 then (if i < 168 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s226,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s227,s27,s272] : Row))) else (if i < 170 then (([s228,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 171 then (([s145,s230,s63,s91,s93,s250,s22,s237,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s238,s49,s27,s272] : Row)))))) else (if i < 177 then (if i < 174 then (if i < 173 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s241,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s246,s49,s27,s272] : Row))) else (if i < 175 then (([s145,s230,s63,s91,s93,s250,s22,s47,s247,s49,s27,s272] : Row)) else (if i < 176 then (([s249,s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s260,s272] : Row))))) else (if i < 179 then (if i < 178 then (([s145,s230,s63,s91,s93,s250,s22,s261,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s262,s49,s27,s272] : Row))) else (if i < 180 then (([s145,s230,s63,s91,s93,s250,s264,s22,s47,s49,s27,s272] : Row)) else (if i < 181 then (([s145,s230,s63,s91,s93,s250,s265,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s267,s22,s47,s49,s27,s272] : Row))))))) else (if i < 192 then (if i < 187 then (if i < 184 then (if i < 183 then (([s145,s230,s63,s91,s93,s250,s22,s268,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s269,s49,s27,s272] : Row))) else (if i < 185 then (([s145,s230,s63,s91,s93,s250,s22,s47,s270,s49,s27,s272] : Row)) else (if i < 186 then (([s145,s230,s63,s91,s93,s250,s271,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 189 then (if i < 188 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272,s291] : Row)) else (([s145,s230,s292,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 190 then (([s145,s230,s63,s91,s293,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 191 then (([s145,s230,s63,s91,s93,s250,s294,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s295,s22,s47,s49,s27,s272] : Row)))))) else (if i < 197 then (if i < 194 then (if i < 193 then (([s145,s230,s63,s91,s93,s250,s22,s296,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s298,s49,s27,s272] : Row))) else (if i < 195 then (([s145,s230,s63,s91,s93,s250,s22,s47,s299,s49,s27,s272] : Row)) else (if i < 196 then (([s145,s230,s63,s91,s93,s250,s22,s47,s300,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s301,s272] : Row))))) else (if i < 199 then (if i < 198 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s230,s63,s148,s150,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 200 then (([s230,s63,s148,s152,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 201 then (([s230,s63,s148,s91,s93,s250,s22,s47,s49,s27,s165,s272] : Row)) else (([s230,s63,s152,s91,s93,s250,s22,s172,s47,s49,s27,s272] : Row)))))))) else (if i < 222 then (if i < 212 then (if i < 207 then (if i < 204 then (if i < 203 then (([s230,s63,s152,s91,s93,s250,s22,s47,s179,s49,s27,s272] : Row)) else (([s230,s63,s152,s91,s197,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 205 then (([s230,s63,s152,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row)) else (if i < 206 then (([s230,s63,s152,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s63,s152,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row))))) else (if i < 209 then (if i < 208 then (([s145,s230,s63,s91,s99,s250,s22,s47,s49,s27,s120,s272] : Row)) else (([s145,s230,s63,s91,s99,s250,s22,s47,s49,s27,s122,s272] : Row))) else (if i < 210 then (([s145,s230,s63,s91,s99,s250,s22,s47,s128,s49,s27,s272] : Row)) else (if i < 211 then (([s145,s230,s63,s91,s99,s250,s22,s47,s130,s49,s27,s272] : Row)) else (([s142,s145,s230,s63,s91,s99,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 217 then (if i < 214 then (if i < 213 then (([s142,s230,s63,s150,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s230,s63,s91,s99,s250,s22,s47,s49,s27,s165,s272] : Row))) else (if i < 215 then (([s145,s230,s63,s91,s99,s250,s22,s172,s47,s49,s27,s272] : Row)) else (if i < 216 then (([s145,s230,s63,s91,s99,s250,s22,s47,s179,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s197,s99,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 219 then (if i < 218 then (([s145,s230,s63,s91,s201,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s99,s250,s22,s47,s211,s49,s27,s272] : Row))) else (if i < 220 then (([s145,s230,s63,s91,s99,s250,s22,s47,s215,s49,s27,s272] : Row)) else (if i < 221 then (([s145,s230,s63,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s99,s250,s22,s47,s49,s27,s272,s306] : Row))))))) else (if i < 232 then (if i < 227 then (if i < 224 then (if i < 223 then (([s145,s230,s63,s91,s103,s250,s22,s47,s49,s27,s120,s272] : Row)) else (([s145,s230,s63,s91,s103,s250,s22,s47,s49,s27,s122,s272] : Row))) else (if i < 225 then (([s145,s230,s63,s91,s103,s250,s22,s47,s128,s49,s27,s272] : Row)) else (if i < 226 then (([s145,s230,s63,s91,s103,s250,s22,s47,s130,s49,s27,s272] : Row)) else (([s142,s145,s230,s63,s91,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 229 then (if i < 228 then (([s142,s230,s63,s91,s103,s250,s22,s47,s49,s27,s165,s272] : Row)) else (([s145,s230,s63,s91,s103,s250,s22,s172,s47,s49,s27,s272] : Row))) else (if i < 230 then (([s145,s230,s63,s91,s103,s250,s22,s47,s179,s49,s27,s272] : Row)) else (if i < 231 then (([s145,s230,s63,s91,s197,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s201,s103,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 237 then (if i < 234 then (if i < 233 then (([s145,s230,s63,s91,s103,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s103,s250,s22,s47,s215,s49,s27,s272] : Row))) else (if i < 235 then (([s145,s230,s63,s91,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 236 then (([s145,s230,s63,s91,s103,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s145,s230,s63,s91,s250,s22,s112,s47,s49,s27,s120,s272] : Row))))) else (if i < 240 then (if i < 238 then (([s145,s230,s63,s91,s250,s22,s112,s47,s49,s27,s122,s272] : Row)) else (if i < 239 then (([s145,s230,s63,s91,s250,s22,s112,s47,s128,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s250,s22,s112,s47,s130,s49,s27,s272] : Row)))) else (if i < 241 then (([s142,s230,s63,s91,s250,s22,s112,s47,s49,s27,s165,s272] : Row)) else (if i < 242 then (([s145,s230,s63,s91,s250,s22,s172,s112,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s250,s22,s112,s47,s179,s49,s27,s272] : Row))))))))) else (if i < 284 then (if i < 263 then (if i < 253 then (if i < 248 then (if i < 245 then (if i < 244 then (([s145,s230,s63,s91,s197,s250,s22,s112,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s201,s250,s22,s112,s47,s49,s27,s272] : Row))) else (if i < 246 then (([s145,s230,s63,s91,s250,s22,s112,s47,s211,s49,s27,s272] : Row)) else (if i < 247 then (([s145,s230,s63,s91,s250,s22,s112,s47,s215,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s250,s22,s112,s47,s49,s27,s272] : Row))))) else (if i < 250 then (if i < 249 then (([s145,s230,s63,s91,s250,s22,s112,s47,s49,s27,s272,s306] : Row)) else (([s145,s230,s63,s91,s244,s250,s22,s47,s49,s27,s122,s272] : Row))) else (if i < 251 then (([s145,s230,s63,s91,s250,s22,s47,s49,s27,s122,s272,s285] : Row)) else (if i < 252 then (([s145,s230,s63,s91,s250,s22,s47,s130,s49,s27,s272,s285] : Row)) else (([s145,s230,s63,s91,s201,s244,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 258 then (if i < 255 then (if i < 254 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s120,s122,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s128,s49,s27,s120,s272] : Row))) else (if i < 256 then (([s145,s230,s63,s103,s250,s22,s47,s130,s49,s27,s120,s272] : Row)) else (if i < 257 then (([s145,s230,s63,s103,s250,s22,s172,s47,s49,s27,s120,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s179,s49,s27,s120,s272] : Row))))) else (if i < 260 then (if i < 259 then (([s145,s230,s63,s197,s103,s250,s22,s47,s49,s27,s120,s272] : Row)) else (([s145,s230,s63,s201,s103,s250,s22,s47,s49,s27,s120,s272] : Row))) else (if i < 261 then (([s145,s230,s63,s103,s250,s22,s47,s211,s49,s27,s120,s272] : Row)) else (if i < 262 then (([s145,s230,s63,s103,s250,s22,s47,s215,s49,s27,s120,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s120,s272] : Row))))))) else (if i < 273 then (if i < 268 then (if i < 265 then (if i < 264 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s120,s272,s306] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s128,s130,s49,s27,s272] : Row))) else (if i < 266 then (([s145,s230,s63,s103,s250,s22,s47,s128,s49,s134,s27,s272] : Row)) else (if i < 267 then (([s145,s230,s63,s103,s250,s22,s47,s128,s49,s135,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s179,s128,s49,s27,s272] : Row))))) else (if i < 270 then (if i < 269 then (([s145,s230,s63,s103,s250,s22,s47,s128,s49,s187,s27,s272] : Row)) else (([s145,s230,s63,s197,s103,s250,s22,s47,s128,s49,s27,s272] : Row))) else (if i < 271 then (([s145,s230,s63,s201,s103,s250,s22,s47,s128,s49,s27,s272] : Row)) else (if i < 272 then (([s145,s230,s63,s103,s250,s22,s47,s128,s211,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s128,s215,s49,s27,s272] : Row)))))) else (if i < 278 then (if i < 275 then (if i < 274 then (([s145,s230,s63,s103,s250,s22,s47,s128,s49,s221,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s128,s49,s223,s27,s272] : Row))) else (if i < 276 then (([s145,s230,s63,s103,s250,s22,s47,s128,s49,s27,s272] : Row)) else (if i < 277 then (([s145,s230,s63,s103,s250,s22,s47,s128,s49,s27,s272,s306] : Row)) else (([s145,s230,s63,s197,s198,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 281 then (if i < 279 then (([s145,s230,s63,s197,s202,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 280 then (([s145,s230,s63,s197,s103,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s145,s230,s63,s197,s103,s250,s22,s47,s212,s49,s27,s272] : Row)))) else (if i < 282 then (([s145,s230,s63,s197,s103,s250,s22,s47,s216,s49,s27,s272] : Row)) else (if i < 283 then (([s145,s230,s63,s197,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s197,s103,s250,s22,s47,s49,s27,s272,s306] : Row)))))))) else (if i < 304 then (if i < 294 then (if i < 289 then (if i < 286 then (if i < 285 then (([s145,s230,s63,s103,s250,s22,s47,s211,s216,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s211,s49,s222,s27,s272] : Row))) else (if i < 287 then (([s145,s230,s63,s103,s250,s22,s47,s211,s49,s27,s272] : Row)) else (if i < 288 then (([s145,s230,s63,s103,s250,s22,s47,s211,s49,s27,s272,s306] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 291 then (if i < 290 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row))) else (if i < 292 then (([s143,s230,s64,s91,s93,s250,s22,s47,s49,s27,s120,s272] : Row)) else (if i < 293 then (([s143,s230,s64,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row)) else (([s142,s143,s230,s64,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 299 then (if i < 296 then (if i < 295 then (([s143,s230,s64,s91,s93,s250,s22,s172,s47,s49,s27,s272] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s173,s47,s49,s27,s272] : Row))) else (if i < 297 then (([s143,s230,s64,s91,s93,s250,s22,s47,s179,s49,s27,s272] : Row)) else (if i < 298 then (([s143,s230,s64,s91,s93,s250,s22,s47,s180,s49,s27,s272] : Row)) else (([s143,s230,s64,s91,s197,s93,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 301 then (if i < 300 then (([s143,s230,s64,s91,s198,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row))) else (if i < 302 then (([s143,s230,s64,s91,s93,s250,s22,s47,s212,s49,s27,s272] : Row)) else (if i < 303 then (([s143,s230,s64,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row))))))) else (if i < 314 then (if i < 309 then (if i < 306 then (if i < 305 then (([s142,s143,s230,s67,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s91,s93,s250,s75,s22,s47,s49,s27,s272] : Row))) else (if i < 307 then (([s142,s143,s230,s91,s93,s250,s22,s47,s76,s49,s27,s272] : Row)) else (if i < 308 then (([s142,s230,s150,s91,s93,s250,s22,s79,s47,s49,s27,s272] : Row)) else (([s145,s230,s91,s93,s250,s22,s47,s85,s49,s27,s272,s282] : Row))))) else (if i < 311 then (if i < 310 then (([s142,s230,s150,s91,s99,s250,s22,s47,s85,s49,s27,s272] : Row)) else (([s142,s230,s150,s91,s92,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 312 then (([s142,s230,s150,s242,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 313 then (([s142,s230,s150,s91,s99,s250,s22,s47,s49,s27,s120,s272] : Row)) else (([s142,s230,s150,s91,s99,s250,s22,s47,s49,s27,s122,s272] : Row)))))) else (if i < 319 then (if i < 316 then (if i < 315 then (([s142,s230,s150,s91,s99,s250,s22,s47,s128,s49,s27,s272] : Row)) else (([s142,s230,s150,s91,s99,s250,s22,s47,s130,s49,s27,s272] : Row))) else (if i < 317 then (([s142,s230,s150,s91,s197,s99,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 318 then (([s142,s230,s150,s91,s198,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s230,s150,s91,s202,s99,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 322 then (if i < 320 then (([s142,s230,s150,s91,s99,s250,s22,s47,s211,s49,s27,s272] : Row)) else (if i < 321 then (([s142,s230,s150,s91,s99,s250,s22,s47,s212,s49,s27,s272] : Row)) else (([s142,s230,s150,s91,s99,s250,s22,s47,s216,s49,s27,s272] : Row)))) else (if i < 323 then (([s142,s230,s150,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 324 then (([s142,s230,s150,s91,s99,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s142,s143,s230,s91,s93,s250,s22,s85,s56,s27,s272,s282] : Row))))))))))
def route11 (i : ℕ) := if i < 162 then (if i < 81 then (if i < 40 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then ((0x3c801400080 : ℕ)) else ((0x48004001880180 : ℕ))) else (if i < 3 then ((0x280 : ℕ)) else (if i < 4 then ((0x880080 : ℕ)) else ((0x10800c001c001c2 : ℕ))))) else (if i < 7 then (if i < 6 then ((0x21800d001c0 : ℕ)) else ((0x248 : ℕ))) else (if i < 8 then ((0x208042004210110 : ℕ)) else (if i < 9 then ((0x288 : ℕ)) else ((0x2c0 : ℕ)))))) else (if i < 15 then (if i < 12 then (if i < 11 then ((0x2d8 : ℕ)) else ((0x300 : ℕ))) else (if i < 13 then ((0x19021000180211024002410340020002010110005000d0010000c00040 : ℕ)) else (if i < 14 then ((0x380 : ℕ)) else ((0x3c00140 : ℕ))))) else (if i < 17 then (if i < 16 then ((0x40001d001c0 : ℕ)) else ((0x50004400480048221404dc826482649696822082540254223c0 : ℕ))) else (if i < 18 then ((0x54004c00440225069082aa02aa14ee82310241026902694 : ℕ)) else (if i < 19 then ((0x58004c004806e40509051105114 : ℕ)) else ((0x54005800582050023584e0824984ea8229828e828ea2798279c : ℕ))))))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then ((0x5c805c009080900090c09040f80 : ℕ)) else ((0x6000e00068009400e1014c009500690 : ℕ))) else (if i < 23 then ((0xac065c844801f40 : ℕ)) else (if i < 24 then ((0x688068044c844c02100 : ℕ)) else ((0x70806c04548258825895fa445002180 : ℕ))))) else (if i < 27 then (if i < 26 then ((0x74807402180458825c825c969a0218825c025c24580 : ℕ)) else ((0x7c80780098009824648244045c0 : ℕ))) else (if i < 28 then ((0x9c8080056482580468025c0 : ℕ)) else (if i < 29 then ((0xa88084009805b5846c026c0 : ℕ)) else ((0xa485e88474027c0 : ℕ)))))) else (if i < 35 then (if i < 32 then (if i < 31 then ((0xa080e400e4108805b0847802900 : ℕ)) else ((0xac8658847c02e40 : ℕ))) else (if i < 33 then ((0xb00660848003080 : ℕ)) else (if i < 34 then ((0xb40074022d066482a602a614f20239024d0484027d0 : ℕ)) else ((0xb802ad466882b1448802e50 : ℕ))))) else (if i < 37 then (if i < 36 then ((0xbc066c848c02e54 : ℕ)) else ((0xc002b54678849003090 : ℕ))) else (if i < 38 then ((0xc4067c849403094 : ℕ)) else (if i < 39 then ((0xc0867082b94498034c0 : ℕ)) else ((0xc48674849c034c4 : ℕ)))))))) else (if i < 60 then (if i < 50 then (if i < 45 then (if i < 42 then (if i < 41 then ((0xc8068084a003740 : ℕ)) else ((0xcc068484a403744 : ℕ))) else (if i < 43 then ((0x6090a8006080a810a400a410d000a000a0108800640084007c0078005c006c00d881810688809c009c10dc00700080008c018584a80074027d43c80 : ℕ)) else (if i < 44 then ((0xd4068c84ac040c0 : ℕ)) else ((0xd8008c045006e80564056416ed04540468046824580 : ℕ))))) else (if i < 47 then (if i < 46 then ((0xdc80dc05fa46ed85fac6ed069a0 : ℕ)) else ((0xf000e800ec00ec24e4844c023c0 : ℕ))) else (if i < 48 then ((0x11080f404b484b00 : ℕ)) else (if i < 49 then ((0x114811404b884b80 : ℕ)) else ((0x118811804bc84bc02100 : ℕ)))))) else (if i < 55 then (if i < 52 then (if i < 51 then ((0x11c811c021c04c082608260969e021c8260026024c00 : ℕ)) else ((0x120812004c484c40 : ℕ))) else (if i < 53 then ((0x128812404cc84c80 : ℕ)) else (if i < 54 then ((0x12c812c04d084d00 : ℕ)) else ((0x65910480658104910881089130810c810c910c0065210c20650108010821300104010420fc0138818904d481008100913c00fc810001002138018984d40 : ℕ))))) else (if i < 57 then (if i < 56 then ((0x134813404d884d80 : ℕ)) else ((0x148014501440 : ℕ))) else (if i < 58 then ((0x15081500 : ℕ)) else (if i < 59 then ((0x1548154044c844c02100 : ℕ)) else ((0x15c815c0 : ℕ))))))) else (if i < 70 then (if i < 65 then (if i < 62 then (if i < 61 then ((0x160015c0 : ℕ)) else ((0x1648164025c825c969a025c025c2 : ℕ))) else (if i < 63 then ((0x168016402a602a614f2024d00680 : ℕ)) else (if i < 64 then ((0x16c816c0 : ℕ)) else ((0x170016c0 : ℕ))))) else (if i < 67 then (if i < 66 then ((0x178044e021101740 : ℕ)) else ((0x184046e046e1246045e01800 : ℕ))) else (if i < 68 then ((0x190018c0 : ℕ)) else (if i < 69 then ((0x19101900 : ℕ)) else ((0x211819501940 : ℕ)))))) else (if i < 75 then (if i < 72 then (if i < 71 then ((0x29c829c91a006a206a2219c04f48 : ℕ)) else ((0x25184fa04fa21a104f884f8c1a00 : ℕ))) else (if i < 73 then ((0x1a801a40 : ℕ)) else (if i < 74 then ((0x1ac01a40 : ℕ)) else ((0x1ac01a80 : ℕ))))) else (if i < 78 then (if i < 76 then ((0x1b401b0026482649 : ℕ)) else (if i < 77 then ((0x1b801b002aa02aa1 : ℕ)) else ((0x1b801b402498 : ℕ)))) else (if i < 79 then ((0x1c001bc025c825c9 : ℕ)) else (if i < 80 then ((0x1c401bc02a602a610680 : ℕ)) else ((0x1c401c0024d80688 : ℕ))))))))) else (if i < 121 then (if i < 101 then (if i < 91 then (if i < 86 then (if i < 83 then (if i < 82 then ((0x21181cc01c80 : ℕ)) else ((0x1d801d40 : ℕ))) else (if i < 84 then ((0x1d901d80 : ℕ)) else (if i < 85 then ((0x2a082d086ae06ae21dc0 : ℕ)) else ((0x28a02c2050601dc0 : ℕ))))) else (if i < 88 then (if i < 87 then ((0x1d801e00 : ℕ)) else ((0x1e481e40 : ℕ))) else (if i < 89 then ((0x2d881e80 : ℕ)) else (if i < 90 then ((0x2e081ec0 : ℕ)) else ((0x2dc81f00 : ℕ)))))) else (if i < 96 then (if i < 93 then (if i < 92 then ((0x20401ec05fc0 : ℕ)) else ((0x2e481f40 : ℕ))) else (if i < 94 then ((0x2ec81f804fc04fc2 : ℕ)) else (if i < 95 then ((0x514851892e881fc0 : ℕ)) else ((0x59181f904fc0 : ℕ))))) else (if i < 98 then (if i < 97 then ((0x5c8831401908 : ℕ)) else ((0x57c86b606ba11fd0 : ℕ))) else (if i < 99 then ((0x33401e406000 : ℕ)) else (if i < 100 then ((0x31401f006040 : ℕ)) else ((0x32801e806080 : ℕ))))))) else (if i < 111 then (if i < 106 then (if i < 103 then (if i < 102 then ((0x60c037c01e40 : ℕ)) else ((0x37c01f006100 : ℕ))) else (if i < 104 then ((0x39401e806140 : ℕ)) else (if i < 105 then ((0xbd9569040401698201016d020401d400b9856d15bc05c0161805680200016c056c13b901b105f1131c019081fd00f5050001f903b801b005f011fc031d019201f800f40 : ℕ)) else ((0x61c0 : ℕ))))) else (if i < 108 then (if i < 107 then ((0x2f882000 : ℕ)) else ((0x2f202000 : ℕ))) else (if i < 109 then ((0x2f482040 : ℕ)) else (if i < 110 then ((0x20882080 : ℕ)) else ((0x33e02080 : ℕ)))))) else (if i < 116 then (if i < 113 then (if i < 112 then ((0x20c820c0 : ℕ)) else ((0x342020c00680 : ℕ))) else (if i < 114 then ((0x2fc82fc0 : ℕ)) else (if i < 115 then ((0x30483000 : ℕ)) else ((0x30883080 : ℕ))))) else (if i < 118 then (if i < 117 then ((0x310830c051c05202 : ℕ)) else ((0x33083140 : ℕ))) else (if i < 119 then ((0x32483180 : ℕ)) else (if i < 120 then ((0x32083200 : ℕ)) else ((0x33883280 : ℕ)))))))) else (if i < 141 then (if i < 131 then (if i < 126 then (if i < 123 then (if i < 122 then ((0x32c832c0 : ℕ)) else ((0x33483340 : ℕ))) else (if i < 124 then ((0x211821102100 : ℕ)) else (if i < 125 then ((0x235822502140 : ℕ)) else ((0x239822d02180 : ℕ))))) else (if i < 128 then (if i < 127 then ((0x50985099231822902200 : ℕ)) else ((0x279826905110511223c0 : ℕ))) else (if i < 129 then ((0x27d827d0 : ℕ)) else (if i < 130 then ((0x28d825502400 : ℕ)) else ((0x2a18289052405242 : ℕ)))))) else (if i < 136 then (if i < 133 then (if i < 132 then ((0x2a9826502480 : ℕ)) else ((0x2a5825d024c0 : ℕ))) else (if i < 134 then ((0x5288528929d829d0528052822500 : ℕ)) else (if i < 135 then ((0x2b182ad0 : ℕ)) else ((0x2b982b50 : ℕ))))) else (if i < 138 then (if i < 137 then ((0x2d182c1052c052c22440 : ℕ)) else ((0x2d582cd053005302 : ℕ))) else (if i < 139 then ((0x2d982d90 : ℕ)) else (if i < 140 then ((0x2dd82dd0 : ℕ)) else ((0x2e182e10 : ℕ))))))) else (if i < 151 then (if i < 146 then (if i < 143 then (if i < 142 then ((0x2e582e50 : ℕ)) else ((0x2f582f50 : ℕ))) else (if i < 144 then ((0x2f982f10 : ℕ)) else (if i < 145 then ((0x34482fd0 : ℕ)) else ((0x34883010 : ℕ))))) else (if i < 148 then (if i < 147 then ((0x34983050 : ℕ)) else ((0x34c83090 : ℕ))) else (if i < 149 then ((0x35083190 : ℕ)) else (if i < 150 then ((0x35d83150 : ℕ)) else ((0x365831d0 : ℕ)))))) else (if i < 156 then (if i < 153 then (if i < 152 then ((0x35c83310 : ℕ)) else ((0x36083390 : ℕ))) else (if i < 154 then ((0x36883350 : ℕ)) else (if i < 155 then ((0x35183250 : ℕ)) else ((0x358832d0 : ℕ))))) else (if i < 159 then (if i < 157 then ((0x36183290 : ℕ)) else (if i < 158 then ((0x35483210 : ℕ)) else ((0x36c836c0 : ℕ)))) else (if i < 160 then ((0x370836d0 : ℕ)) else (if i < 161 then ((0x37483740 : ℕ)) else ((0x37883780 : ℕ)))))))))) else (if i < 243 then (if i < 202 then (if i < 182 then (if i < 172 then (if i < 167 then (if i < 164 then (if i < 163 then ((0x385837c0 : ℕ)) else ((0x38c83790 : ℕ))) else (if i < 165 then ((0x39083800 : ℕ)) else (if i < 166 then ((0x38483840 : ℕ)) else ((0x38883880 : ℕ))))) else (if i < 169 then (if i < 168 then ((0x38983940 : ℕ)) else ((0x39183910 : ℕ))) else (if i < 170 then ((0x39c83980 : ℕ)) else (if i < 171 then ((0x3a083a001580 : ℕ)) else ((0x3b083a4017d0 : ℕ)))))) else (if i < 177 then (if i < 174 then (if i < 173 then ((0x3ac83a8017d050c8 : ℕ)) else ((0x3c083b8019a0 : ℕ))) else (if i < 175 then ((0x3bc83bc019a0 : ℕ)) else (if i < 176 then ((0x39d839d0 : ℕ)) else ((0x3cc8155215503a10 : ℕ))))) else (if i < 179 then (if i < 178 then ((0x3d0817426b2017406b223a90 : ℕ)) else ((0x3d48174217403a50 : ℕ))) else (if i < 180 then ((0x3d1817aa17a83ad053405342 : ℕ)) else (if i < 181 then ((0x3d5817aa17a83b10 : ℕ)) else ((0x3d9817aa17a83b50 : ℕ))))))) else (if i < 192 then (if i < 187 then (if i < 184 then (if i < 183 then ((0x3dc8194a19483c10 : ℕ)) else ((0x3dd8194a19483b90 : ℕ))) else (if i < 185 then ((0x3e08194a19483bd0 : ℕ)) else (if i < 186 then ((0x3e481c8a1c883c4014401d20 : ℕ)) else ((0x69926c8069826c927c827c93c8829082909290006922902069027c027c23c8026c026c2244824400f80 : ℕ))))) else (if i < 189 then (if i < 188 then ((0x1cd11cd03e5814a01cda1cd83e50 : ℕ)) else ((0x3e883e80 : ℕ))) else (if i < 190 then ((0x3f483ec0 : ℕ)) else (if i < 191 then ((0x3fc83e90 : ℕ)) else ((0x40083ed0 : ℕ)))))) else (if i < 197 then (if i < 194 then (if i < 193 then ((0x3f083f00 : ℕ)) else ((0x3f883f80 : ℕ))) else (if i < 195 then ((0x40183f50 : ℕ)) else (if i < 196 then ((0x40883f90 : ℕ)) else ((0x40483f10 : ℕ))))) else (if i < 199 then (if i < 198 then ((0x40c840c0 : ℕ)) else ((0x42882bd0244053805382 : ℕ))) else (if i < 200 then ((0x42c82c5053c053c2 : ℕ)) else (if i < 201 then ((0x540c540d2c9c2c90250054005402 : ℕ)) else ((0x4308410054405442 : ℕ)))))))) else (if i < 222 then (if i < 212 then (if i < 207 then (if i < 204 then (if i < 203 then ((0x4388414054805482 : ℕ)) else ((0x4348418054c05502 : ℕ))) else (if i < 205 then ((0x43c841c055405582 : ℕ)) else (if i < 206 then ((0x89927480898274928482849440829882989294008522942085028002802420025004f4004d02700504255c02702504055c2140050c0 : ℕ)) else ((0x4448424056005602 : ℕ))))) else (if i < 209 then (if i < 208 then ((0x569841105140 : ℕ)) else ((0x56d8210041125180 : ℕ))) else (if i < 210 then ((0x5958415051c0 : ℕ)) else (if i < 211 then ((0x5998210041525200 : ℕ)) else ((0x57582810524052c0 : ℕ)))))) else (if i < 217 then (if i < 214 then (if i < 213 then ((0x57982710539027005380 : ℕ)) else ((0x5b985b9957182950528027405400 : ℕ))) else (if i < 215 then ((0x57d82e905440 : ℕ)) else (if i < 216 then ((0x59d830d05480 : ℕ)) else ((0x5818419054c0 : ℕ))))) else (if i < 219 then (if i < 218 then ((0x5858210041925500 : ℕ)) else ((0x5a1841d05540 : ℕ))) else (if i < 220 then ((0x5a58210041d25580 : ℕ)) else (if i < 221 then ((0xa1958d00a1858d1589858995a985700570129c00e922c82079028802c4242104f9053402bc0048027405300270055c01040 : ℕ)) else ((0x5ad842505600 : ℕ))))))) else (if i < 232 then (if i < 227 then (if i < 224 then (if i < 223 then ((0x5bc8 : ℕ)) else ((0x5c0821002f401d88 : ℕ))) else (if i < 225 then ((0x5cc8 : ℕ)) else (if i < 226 then ((0x5d08210031801d88 : ℕ)) else ((0x5c5834c01718 : ℕ))))) else (if i < 229 then (if i < 228 then ((0x5ec85ec958a02840 : ℕ)) else ((0x5c9835c01908 : ℕ))) else (if i < 230 then ((0x5d4837401908 : ℕ)) else (if i < 231 then ((0x5cd8 : ℕ)) else ((0x5d18210035101d88 : ℕ)))))) else (if i < 237 then (if i < 234 then (if i < 233 then ((0x5d88 : ℕ)) else ((0x5dc8210037901d88 : ℕ))) else (if i < 235 then ((0xa5958900a5858915c405c415e08574057412a0011903d401ad82e401500308116c0308016c02d0016c03e90075028802c0017183b001a8828403500171828001080 : ℕ)) else (if i < 236 then ((0x5e48 : ℕ)) else ((0x56886b686b694310 : ℕ))))) else (if i < 240 then (if i < 238 then ((0x56c821006ba86ba94312 : ℕ)) else (if i < 239 then ((0x58086c606ca94350 : ℕ)) else ((0x584821006ca06ce14352 : ℕ)))) else (if i < 241 then ((0x5b885b8958c86f185ba05ba129902980 : ℕ)) else (if i < 242 then ((0x59086aa06aa12ed0 : ℕ)) else ((0x59c86be06c213110 : ℕ))))))))) else (if i < 284 then (if i < 263 then (if i < 253 then (if i < 248 then (if i < 245 then (if i < 244 then ((0x59486be86be94390 : ℕ)) else ((0x59886c286c2921004392 : ℕ))) else (if i < 246 then ((0x5a086d206d6943d0 : ℕ)) else (if i < 247 then ((0x5a4821006d606da143d2 : ℕ)) else ((0xa9957080a985709574857495a8805a86a2057806ae16de057816ae06de10f226b202a0042d24410429007d029c02c802980294010c0 : ℕ))))) else (if i < 250 then (if i < 249 then ((0x5ac86e206e214450 : ℕ)) else ((0x5f082640 : ℕ))) else (if i < 251 then ((0x2a805f18 : ℕ)) else (if i < 252 then ((0x2a405f48 : ℕ)) else ((0x5f5825c0 : ℕ)))))) else (if i < 258 then (if i < 255 then (if i < 254 then ((0x2f402e005fc8 : ℕ)) else ((0x33002dc06048 : ℕ))) else (if i < 256 then ((0x33802d806088 : ℕ)) else (if i < 257 then ((0x601836801e40 : ℕ)) else ((0x38501e4060c8 : ℕ))))) else (if i < 260 then (if i < 259 then ((0x605835d02dc0 : ℕ)) else ((0x609836102d80 : ℕ))) else (if i < 261 then ((0x38502dc06108 : ℕ)) else (if i < 262 then ((0x38902d806148 : ℕ)) else ((0x3dd01b980ad9330118c059100ad8330018c059115c805c8161882f8016c057c057c13f1016506a482f4027c0431012102f00171841103c001b48365019202ec02e801100 : ℕ))))))) else (if i < 273 then (if i < 268 then (if i < 265 then (if i < 264 then ((0x61c8 : ℕ)) else ((0x318030406200 : ℕ))) else (if i < 266 then ((0x324030006208 : ℕ)) else (if i < 267 then ((0x32c02fc06240 : ℕ)) else ((0x37401f006280 : ℕ))))) else (if i < 270 then (if i < 269 then ((0x38c01e8062c0 : ℕ)) else ((0x628837402dc0 : ℕ))) else (if i < 271 then ((0x62c837902d80 : ℕ)) else (if i < 272 then ((0x6300 : ℕ)) else ((0x379030406340 : ℕ)))))) else (if i < 278 then (if i < 275 then (if i < 274 then ((0x38c030006348 : ℕ)) else ((0x39102fc06380 : ℕ))) else (if i < 276 then ((0xc59595040101c58330016d032401d400c1859915cc05d0163c05800320016c058413f501bd05f41318027c0435012503140171841503bc0208031003780192030c01140 : ℕ)) else (if i < 277 then ((0x6400 : ℕ)) else ((0x621835003490 : ℕ))))) else (if i < 281 then (if i < 279 then ((0x625835803440 : ℕ)) else (if i < 280 then ((0x6318 : ℕ)) else ((0x635837803490 : ℕ)))) else (if i < 282 then ((0x639838003440 : ℕ)) else (if i < 283 then ((0xb1959d00b1859d15d405d4163d859c059c1439012903e0033c035d016d0374118c0374018c035c016c03ed01c20351027c04190354017183ec01c084380350027d041801280 : ℕ)) else ((0x6418 : ℕ)))))))) else (if i < 304 then (if i < 294 then (if i < 289 then (if i < 286 then (if i < 285 then ((0x380037006440 : ℕ)) else ((0x390036d06448 : ℕ))) else (if i < 287 then ((0xcd95a1040803400385016d038c01d400c985a515d805dc164805a00384016c05a413f9020d0379027c043d012d037c0171841d03f8020c043c0378027d041c012c0 : ℕ)) else (if i < 288 then ((0x64c0 : ℕ)) else ((0x3d1005583fc00b590d191dd15a9016d03fc00b580d181dd05a9116d01e005e005e0165001d403d00056819c015001dc15a8016c01dc05a8116c03e5039d03a1015d03a511a503a501a503a9005203d801ad82f401500318116c0318016c02d40441016c03e9011d013103cc016181a2015001f4115001f4015001a0815003ad004502cc0421017183e4039c03a8005083a411a403a401a403a0015c03c4039803b401a883ac004403d901ae82d50440016d0319116d0319016d02f5015003b501aa0358017182cd0420017183e8011c01300 : ℕ))))) else (if i < 291 then (if i < 290 then ((0xd595ad00d585ad15e405e4165405ac05ac1445013504250444042401340 : ℕ)) else ((0x65804480 : ℕ))) else (if i < 292 then ((0x65c047c0 : ℕ)) else (if i < 293 then ((0x66004800 : ℕ)) else ((0x664048404580 : ℕ)))))) else (if i < 299 then (if i < 296 then (if i < 295 then ((0x66804880 : ℕ)) else ((0x66c048c0 : ℕ))) else (if i < 297 then ((0x67004900 : ℕ)) else (if i < 298 then ((0x67404940 : ℕ)) else ((0x67804980 : ℕ))))) else (if i < 301 then (if i < 300 then ((0x67c049c0 : ℕ)) else ((0x68004a00 : ℕ))) else (if i < 302 then ((0x68404a40 : ℕ)) else (if i < 303 then ((0xe195b500e185b515e805e8168805b005b014780095247820950474047424a8047004702464046000904 : ℕ)) else ((0x68c04ac0 : ℕ))))))) else (if i < 314 then (if i < 309 then (if i < 306 then (if i < 305 then ((0x6e486e4969004e004dc0 : ℕ)) else ((0x69404ec04e80 : ℕ))) else (if i < 307 then ((0x69804f104f00 : ℕ)) else (if i < 308 then ((0x6a006f106f11529052924f804f40 : ℕ)) else ((0x4f006a405000 : ℕ))))) else (if i < 311 then (if i < 310 then ((0x6a804fd04fc0 : ℕ)) else ((0x6ac0525052d05040 : ℕ))) else (if i < 312 then ((0x6b00535044c450c0 : ℕ)) else (if i < 313 then ((0x6b4054505140 : ℕ)) else ((0x6b8054525180 : ℕ)))))) else (if i < 319 then (if i < 316 then (if i < 315 then ((0x6bc0549051c0 : ℕ)) else ((0x6c0054925200 : ℕ))) else (if i < 317 then ((0x6c4054d054c0 : ℕ)) else (if i < 318 then ((0x6c80551054c4 : ℕ)) else ((0x6cc055125504 : ℕ))))) else (if i < 322 then (if i < 320 then ((0x6d0055505540 : ℕ)) else (if i < 321 then ((0x6d4055905544 : ℕ)) else ((0x6d8055925584 : ℕ)))) else (if i < 323 then ((0xe595b900e585b915ec05ec16dc05b805b8152900ed254120990525053d255d052800ec45404524053c455c00980 : ℕ)) else (if i < 324 then ((0x6e0056105600 : ℕ)) else ((0x69806a506a40 : ℕ))))))))))
def stored10 (i : ℕ) := if i < 222 then (if i < 111 then (if i < 55 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then (([s0,s2,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 2 then (([s0,s5,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s0,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 4 then (([s0,s230,s63,s152,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 5 then (([s0,s230,s63,s103,s250,s22,s47,s49,s27,s166,s272] : Row)) else (([s0,s143,s230,s64,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 9 then (if i < 7 then (([s0,s230,s66,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 8 then (([s0,s230,s152,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s0,s145,s230,s63,s103,s250,s22,s47,s55,s27,s272] : Row)))) else (if i < 11 then (if i < 10 then (([s0,s145,s230,s63,s103,s250,s22,s47,s56,s27,s272] : Row)) else (([s0,s145,s230,s63,s103,s250,s22,s85,s56,s27,s272] : Row))) else (if i < 12 then (([s0,s145,s230,s63,s103,s250,s22,s128,s56,s27,s272] : Row)) else (([s0,s145,s230,s63,s103,s250,s22,s211,s56,s27,s272] : Row)))))) else (if i < 20 then (if i < 16 then (if i < 14 then (([s0,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 15 then (([s0,s145,s230,s63,s103,s250,s22,s56,s27,s272,s306] : Row)) else (([s0,s143,s230,s64,s91,s93,s250,s22,s56,s27,s272] : Row)))) else (if i < 18 then (if i < 17 then (([s0,s142,s230,s150,s91,s99,s250,s22,s56,s27,s272] : Row)) else (([s1,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 19 then (([s1,s145,s230,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s1,s142,s143,s230,s107,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 23 then (if i < 21 then (([s1,s145,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row)) else (if i < 22 then (([s1,s142,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s1,s142,s143,s230,s91,s99,s250,s22,s56,s27,s272] : Row)))) else (if i < 25 then (if i < 24 then (([s2,s4,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s9,s93,s250,s22,s56,s27,s272] : Row))) else (if i < 26 then (([s2,s143,s230,s63,s12,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))))))) else (if i < 41 then (if i < 34 then (if i < 30 then (if i < 28 then (([s2,s143,s230,s63,s103,s250,s22,s47,s49,s27,s274] : Row)) else (if i < 29 then (([s2,s143,s230,s63,s103,s252,s22,s47,s49,s27,s272] : Row)) else (([s2,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 32 then (if i < 31 then (([s2,s230,s63,s150,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s230,s63,s103,s250,s22,s47,s49,s27,s165,s272] : Row))) else (if i < 33 then (([s2,s143,s230,s63,s104,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s107,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 37 then (if i < 35 then (([s2,s143,s230,s63,s250,s22,s114,s47,s49,s27,s272] : Row)) else (if i < 36 then (([s2,s143,s230,s64,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s230,s65,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 39 then (if i < 38 then (([s2,s143,s230,s70,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s230,s150,s91,s99,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 40 then (([s2,s143,s230,s63,s103,s250,s22,s47,s51,s27,s272] : Row)) else (([s2,s143,s230,s63,s103,s250,s22,s47,s55,s27,s272] : Row)))))) else (if i < 48 then (if i < 44 then (if i < 42 then (([s2,s143,s230,s63,s103,s250,s22,s47,s56,s27,s272] : Row)) else (if i < 43 then (([s2,s143,s230,s63,s103,s250,s22,s47,s27,s60,s272] : Row)) else (([s2,s143,s230,s63,s103,s250,s22,s85,s56,s27,s272] : Row)))) else (if i < 46 then (if i < 45 then (([s2,s143,s230,s63,s103,s250,s22,s128,s56,s27,s272] : Row)) else (([s2,s142,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row))) else (if i < 47 then (([s2,s143,s230,s63,s103,s250,s22,s172,s56,s27,s272] : Row)) else (([s2,s143,s230,s63,s103,s250,s22,s173,s56,s27,s272] : Row))))) else (if i < 51 then (if i < 49 then (([s2,s143,s230,s63,s103,s250,s22,s179,s56,s27,s272] : Row)) else (if i < 50 then (([s2,s143,s230,s63,s103,s250,s22,s180,s56,s27,s272] : Row)) else (([s2,s143,s230,s63,s103,s250,s22,s211,s56,s27,s272] : Row)))) else (if i < 53 then (if i < 52 then (([s2,s143,s230,s63,s103,s250,s22,s212,s56,s27,s272] : Row)) else (([s2,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row))) else (if i < 54 then (([s2,s143,s230,s63,s103,s250,s22,s56,s27,s272,s306] : Row)) else (([s2,s143,s230,s64,s91,s93,s250,s22,s56,s27,s272] : Row)))))))) else (if i < 83 then (if i < 69 then (if i < 62 then (if i < 58 then (if i < 56 then (([s2,s143,s230,s63,s103,s250,s23,s47,s49,s27,s272] : Row)) else (if i < 57 then (([s2,s143,s230,s63,s93,s250,s25,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s63,s91,s250,s112,s47,s55,s27,s272] : Row)))) else (if i < 60 then (if i < 59 then (([s3,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s3,s143,s230,s91,s99,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 61 then (([s3,s143,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s5,s230,s63,s103,s250,s22,s47,s85,s49,s27,s272] : Row))))) else (if i < 65 then (if i < 63 then (([s5,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 64 then (([s5,s230,s63,s91,s93,s250,s22,s47,s49,s27,s276] : Row)) else (([s5,s230,s63,s91,s96,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 67 then (if i < 66 then (([s5,s230,s63,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s5,s230,s63,s91,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 68 then (([s5,s230,s63,s91,s250,s22,s112,s47,s49,s27,s272] : Row)) else (([s5,s230,s63,s103,s250,s22,s47,s49,s27,s120,s272] : Row)))))) else (if i < 76 then (if i < 72 then (if i < 70 then (([s5,s230,s63,s103,s250,s22,s47,s128,s49,s27,s272] : Row)) else (if i < 71 then (([s142,s5,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s5,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 74 then (if i < 73 then (([s5,s230,s63,s103,s250,s22,s172,s47,s49,s27,s272] : Row)) else (([s5,s230,s63,s103,s250,s22,s47,s179,s49,s27,s272] : Row))) else (if i < 75 then (([s5,s230,s63,s197,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s5,s230,s63,s103,s250,s22,s47,s211,s49,s27,s272] : Row))))) else (if i < 79 then (if i < 77 then (([s5,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 78 then (([s5,s230,s63,s103,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s5,s230,s66,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 81 then (if i < 80 then (([s5,s230,s63,s91,s93,s250,s24,s47,s49,s27,s272] : Row)) else (([s6,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 82 then (([s145,s230,s8,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s8,s91,s93,s250,s22,s56,s27,s272] : Row))))))) else (if i < 97 then (if i < 90 then (if i < 86 then (if i < 84 then (([s143,s230,s63,s10,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 85 then (([s14,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s15,s143,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 88 then (if i < 87 then (([s16,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s17,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 89 then (([s17,s142,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s18,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 93 then (if i < 91 then (([s18,s142,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 92 then (([s19,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s19,s142,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row)))) else (if i < 95 then (if i < 94 then (([s145,s230,s63,s20,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s20,s93,s250,s22,s56,s27,s272] : Row))) else (if i < 96 then (([s142,s143,s230,s63,s21,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s93,s250,s22,s25,s47,s49,s27,s272] : Row)))))) else (if i < 104 then (if i < 100 then (if i < 98 then (([s142,s143,s230,s63,s93,s250,s22,s25,s56,s27,s272] : Row)) else (if i < 99 then (([s142,s143,s230,s63,s250,s22,s26,s47,s49,s27,s272] : Row)) else (([s37,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 102 then (if i < 101 then (([s37,s145,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s38,s49,s27,s272] : Row))) else (if i < 103 then (([s142,s143,s230,s63,s91,s93,s250,s22,s39,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s40,s272] : Row))))) else (if i < 107 then (if i < 105 then (([s145,s230,s63,s91,s93,s250,s22,s56,s27,s40,s272] : Row)) else (if i < 106 then (([s41,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s41,s145,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row)))) else (if i < 109 then (if i < 108 then (([s41,s142,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s42,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 110 then (([s42,s145,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s42,s142,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row))))))))) else (if i < 166 then (if i < 138 then (if i < 124 then (if i < 117 then (if i < 114 then (if i < 112 then (([s43,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 113 then (([s43,s145,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s43,s142,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row)))) else (if i < 115 then (([s145,s230,s63,s91,s93,s250,s22,s44,s49,s27,s272] : Row)) else (if i < 116 then (([s142,s143,s230,s63,s103,s250,s22,s44,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s91,s93,s250,s22,s45,s27,s272] : Row))))) else (if i < 120 then (if i < 118 then (([s46,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 119 then (([s46,s145,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s48,s49,s27,s272] : Row)))) else (if i < 122 then (if i < 121 then (([s145,s230,s63,s103,s250,s22,s47,s49,s56,s27,s272] : Row)) else (([s81,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 123 then (([s82,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s83,s103,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 131 then (if i < 127 then (if i < 125 then (([s145,s230,s63,s103,s250,s22,s47,s84,s49,s27,s272] : Row)) else (if i < 126 then (([s145,s230,s63,s103,s250,s22,s47,s85,s49,s27,s272] : Row)) else (([s230,s63,s152,s103,s250,s22,s47,s85,s49,s27,s272] : Row)))) else (if i < 129 then (if i < 128 then (([s230,s63,s103,s250,s22,s47,s85,s49,s27,s166,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s86,s49,s27,s272] : Row))) else (if i < 130 then (([s145,s230,s63,s103,s250,s22,s47,s49,s88,s27,s272] : Row)) else (([s89,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 134 then (if i < 132 then (([s90,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 133 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s273] : Row)))) else (if i < 136 then (if i < 135 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s274] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s276] : Row))) else (if i < 137 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s277] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s278] : Row))))))) else (if i < 152 then (if i < 145 then (if i < 141 then (if i < 139 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s279] : Row)) else (if i < 140 then (([s145,s230,s63,s91,s93,s250,s22,s47,s49,s27,s280] : Row)) else (([s145,s63,s231,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 143 then (if i < 142 then (([s145,s63,s232,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s63,s91,s233,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 144 then (([s146,s230,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s63,s151,s91,s93,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 148 then (if i < 146 then (([s230,s63,s152,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 147 then (([s230,s63,s154,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s63,s91,s156,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 150 then (if i < 149 then (([s230,s63,s91,s93,s250,s22,s47,s49,s27,s168,s272] : Row)) else (([s145,s230,s63,s91,s94,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 151 then (([s143,s230,s63,s91,s95,s252,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s95,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 159 then (if i < 155 then (if i < 153 then (([s145,s230,s63,s91,s96,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 154 then (([s145,s230,s63,s91,s97,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s98,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 157 then (if i < 156 then (([s145,s230,s63,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s63,s152,s91,s99,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 158 then (([s230,s63,s91,s99,s250,s22,s47,s49,s27,s166,s272] : Row)) else (([s145,s230,s63,s91,s102,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 162 then (if i < 160 then (([s145,s230,s63,s91,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 161 then (([s230,s63,s152,s91,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s63,s91,s103,s250,s22,s47,s49,s27,s166,s272] : Row)))) else (if i < 164 then (if i < 163 then (([s145,s230,s63,s91,s107,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s250,s22,s111,s47,s49,s27,s272] : Row))) else (if i < 165 then (([s145,s230,s63,s91,s250,s22,s112,s47,s49,s27,s272] : Row)) else (([s230,s63,s152,s91,s250,s22,s112,s47,s49,s27,s272] : Row)))))))) else (if i < 194 then (if i < 180 then (if i < 173 then (if i < 169 then (if i < 167 then (([s230,s63,s91,s250,s22,s112,s47,s49,s27,s166,s272] : Row)) else (if i < 168 then (([s145,s230,s63,s91,s250,s22,s113,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s250,s22,s114,s47,s49,s27,s272] : Row)))) else (if i < 171 then (if i < 170 then (([s145,s230,s63,s91,s250,s22,s47,s115,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s250,s22,s47,s49,s27,s116,s272] : Row))) else (if i < 172 then (([s145,s230,s63,s91,s250,s22,s47,s49,s27,s122,s281] : Row)) else (([s145,s63,s91,s234,s250,s22,s47,s49,s27,s122,s272] : Row))))) else (if i < 176 then (if i < 174 then (([s145,s230,s63,s91,s250,s22,s47,s130,s49,s27,s281] : Row)) else (if i < 175 then (([s145,s63,s91,s201,s234,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s92,s99,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 178 then (if i < 177 then (([s145,s230,s63,s92,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s92,s107,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 179 then (([s145,s230,s63,s92,s250,s22,s112,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s107,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 187 then (if i < 183 then (if i < 181 then (([s145,s230,s63,s103,s250,s22,s110,s47,s49,s27,s272] : Row)) else (if i < 182 then (([s145,s230,s63,s103,s250,s22,s114,s47,s49,s27,s272] : Row)) else (([s117,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 185 then (if i < 184 then (([s145,s230,s63,s118,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s119,s272] : Row))) else (if i < 186 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s120,s272] : Row)) else (([s230,s63,s152,s103,s250,s22,s47,s49,s27,s120,s272] : Row))))) else (if i < 190 then (if i < 188 then (([s230,s63,s103,s250,s22,s47,s49,s27,s166,s120,s272] : Row)) else (if i < 189 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s121,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s123,s272] : Row)))) else (if i < 192 then (if i < 191 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s124,s272] : Row)) else (([s125,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 193 then (([s145,s230,s63,s126,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s127,s49,s27,s272] : Row))))))) else (if i < 208 then (if i < 201 then (if i < 197 then (if i < 195 then (([s145,s230,s63,s103,s250,s22,s47,s128,s49,s27,s272] : Row)) else (if i < 196 then (([s230,s63,s152,s103,s250,s22,s47,s128,s49,s27,s272] : Row)) else (([s230,s63,s103,s250,s22,s47,s128,s49,s27,s166,s272] : Row)))) else (if i < 199 then (if i < 198 then (([s145,s230,s63,s103,s250,s22,s47,s129,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s131,s49,s27,s272] : Row))) else (if i < 200 then (([s145,s230,s63,s103,s250,s22,s47,s132,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s133,s49,s27,s272] : Row))))) else (if i < 204 then (if i < 202 then (([s145,s230,s63,s103,s250,s22,s47,s49,s136,s27,s272] : Row)) else (if i < 203 then (([s145,s230,s63,s103,s250,s22,s47,s49,s137,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s138,s27,s272] : Row)))) else (if i < 206 then (if i < 205 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s139,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s140,s272] : Row))) else (if i < 207 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s141,s272] : Row)) else (([s193,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 215 then (if i < 211 then (if i < 209 then (([s145,s230,s63,s103,s250,s22,s47,s194,s49,s27,s272] : Row)) else (if i < 210 then (([s195,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s196,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 213 then (if i < 212 then (([s145,s230,s63,s197,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s199,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 214 then (([s145,s230,s63,s200,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s203,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 218 then (if i < 216 then (([s145,s230,s63,s103,s250,s22,s204,s47,s49,s27,s272] : Row)) else (if i < 217 then (([s145,s230,s63,s103,s250,s22,s205,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s206,s47,s49,s27,s272] : Row)))) else (if i < 220 then (if i < 219 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s207,s272] : Row)) else (([s208,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 221 then (([s145,s230,s63,s103,s250,s22,s47,s210,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s211,s49,s27,s272] : Row)))))))))) else (if i < 333 then (if i < 277 then (if i < 249 then (if i < 235 then (if i < 228 then (if i < 225 then (if i < 223 then (([s145,s230,s63,s103,s250,s22,s47,s213,s49,s27,s272] : Row)) else (if i < 224 then (([s145,s230,s63,s103,s250,s22,s47,s214,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s218,s49,s27,s272] : Row)))) else (if i < 226 then (([s145,s230,s63,s103,s250,s22,s47,s219,s49,s27,s272] : Row)) else (if i < 227 then (([s145,s230,s63,s103,s250,s22,s47,s220,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s224,s27,s272] : Row))))) else (if i < 231 then (if i < 229 then (([s145,s230,s63,s103,s250,s22,s47,s49,s225,s27,s272] : Row)) else (if i < 230 then (([s145,s230,s63,s103,s250,s22,s47,s49,s226,s27,s272] : Row)) else (([s228,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 233 then (if i < 232 then (([s229,s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s237,s47,s49,s27,s272] : Row))) else (if i < 234 then (([s145,s230,s63,s103,s250,s22,s47,s238,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s241,s272] : Row)))))) else (if i < 242 then (if i < 238 then (if i < 236 then (([s145,s230,s63,s242,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 237 then (([s145,s230,s63,s243,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s245,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 240 then (if i < 239 then (([s145,s230,s63,s103,s250,s22,s47,s246,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s247,s49,s27,s272] : Row))) else (if i < 241 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s248,s272] : Row)) else (([s145,s230,s63,s103,s250,s271,s22,s47,s49,s27,s272] : Row))))) else (if i < 245 then (if i < 243 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 244 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s282] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s283] : Row)))) else (if i < 247 then (if i < 246 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s284] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s286] : Row))) else (if i < 248 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s288] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s289] : Row))))))) else (if i < 263 then (if i < 256 then (if i < 252 then (if i < 250 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s290] : Row)) else (if i < 251 then (([s145,s230,s292,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s293,s103,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 254 then (if i < 253 then (([s145,s230,s63,s103,s250,s22,s296,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s297,s49,s27,s272] : Row))) else (if i < 255 then (([s145,s230,s63,s103,s250,s22,s47,s298,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s302] : Row))))) else (if i < 259 then (if i < 257 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s303] : Row)) else (if i < 258 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s304] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s305] : Row)))) else (if i < 261 then (if i < 260 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s230,s63,s152,s103,s250,s22,s172,s47,s49,s27,s272] : Row))) else (if i < 262 then (([s230,s63,s152,s103,s250,s22,s47,s179,s49,s27,s272] : Row)) else (([s230,s63,s152,s197,s103,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 270 then (if i < 266 then (if i < 264 then (([s230,s63,s152,s103,s250,s22,s47,s211,s49,s27,s272] : Row)) else (if i < 265 then (([s230,s63,s152,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s63,s152,s103,s250,s22,s47,s49,s27,s272,s306] : Row)))) else (if i < 268 then (if i < 267 then (([s230,s63,s103,s250,s22,s47,s49,s27,s164,s165,s272] : Row)) else (([s230,s63,s103,s250,s22,s47,s49,s27,s164,s166,s272] : Row))) else (if i < 269 then (([s230,s63,s103,s250,s22,s172,s47,s49,s27,s166,s272] : Row)) else (([s230,s63,s103,s250,s22,s47,s179,s49,s27,s166,s272] : Row))))) else (if i < 273 then (if i < 271 then (([s230,s63,s197,s103,s250,s22,s47,s49,s27,s166,s272] : Row)) else (if i < 272 then (([s230,s63,s103,s250,s22,s47,s211,s49,s27,s166,s272] : Row)) else (([s230,s63,s103,s250,s22,s47,s49,s27,s166,s272] : Row)))) else (if i < 275 then (if i < 274 then (([s230,s63,s103,s250,s22,s47,s49,s27,s166,s272,s306] : Row)) else (([s143,s230,s64,s103,s250,s22,s47,s85,s49,s27,s272] : Row))) else (if i < 276 then (([s143,s230,s64,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s47,s49,s27,s274] : Row)))))))) else (if i < 305 then (if i < 291 then (if i < 284 then (if i < 280 then (if i < 278 then (([s143,s230,s64,s91,s93,s252,s22,s47,s49,s27,s272] : Row)) else (if i < 279 then (([s145,s230,s64,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s64,s150,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 282 then (if i < 281 then (([s230,s64,s152,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s64,s91,s93,s250,s22,s47,s49,s27,s165,s272] : Row))) else (if i < 283 then (([s143,s230,s64,s91,s95,s250,s22,s47,s49,s27,s272] : Row)) else (([s143,s230,s64,s91,s99,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 287 then (if i < 285 then (([s143,s230,s64,s91,s100,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 286 then (([s143,s230,s64,s91,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s143,s230,s64,s91,s250,s22,s112,s47,s49,s27,s272] : Row)))) else (if i < 289 then (if i < 288 then (([s143,s230,s64,s103,s250,s22,s47,s49,s27,s120,s272] : Row)) else (([s143,s230,s64,s103,s250,s22,s47,s128,s49,s27,s272] : Row))) else (if i < 290 then (([s142,s143,s230,s64,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s143,s230,s64,s103,s250,s22,s172,s47,s49,s27,s272] : Row)))))) else (if i < 298 then (if i < 294 then (if i < 292 then (([s143,s230,s64,s103,s250,s22,s173,s47,s49,s27,s272] : Row)) else (if i < 293 then (([s143,s230,s64,s103,s250,s22,s47,s179,s49,s27,s272] : Row)) else (([s143,s230,s64,s103,s250,s22,s47,s180,s49,s27,s272] : Row)))) else (if i < 296 then (if i < 295 then (([s143,s230,s64,s197,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s143,s230,s64,s198,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 297 then (([s143,s230,s64,s103,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s143,s230,s64,s103,s250,s22,s47,s212,s49,s27,s272] : Row))))) else (if i < 301 then (if i < 299 then (([s143,s230,s64,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 300 then (([s143,s230,s64,s103,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s230,s66,s91,s93,s250,s22,s47,s85,s49,s27,s272] : Row)))) else (if i < 303 then (if i < 302 then (([s230,s66,s91,s93,s250,s22,s47,s49,s27,s120,s272] : Row)) else (([s230,s66,s91,s93,s250,s22,s47,s128,s49,s27,s272] : Row))) else (if i < 304 then (([s142,s230,s66,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s66,s91,s93,s250,s22,s47,s49,s27,s272] : Row))))))) else (if i < 319 then (if i < 312 then (if i < 308 then (if i < 306 then (([s230,s66,s91,s93,s250,s22,s172,s47,s49,s27,s272] : Row)) else (if i < 307 then (([s230,s66,s91,s93,s250,s22,s47,s179,s49,s27,s272] : Row)) else (([s230,s66,s91,s197,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 310 then (if i < 309 then (([s230,s66,s91,s93,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s230,s66,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 311 then (([s230,s66,s91,s93,s250,s22,s47,s49,s27,s272,s306] : Row)) else (([s145,s230,s67,s91,s93,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 315 then (if i < 313 then (([s142,s143,s230,s67,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 314 then (([s143,s230,s68,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s91,s93,s250,s75,s22,s47,s49,s27,s272] : Row)))) else (if i < 317 then (if i < 316 then (([s142,s143,s230,s103,s250,s75,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s91,s93,s250,s22,s47,s76,s49,s27,s272] : Row))) else (if i < 318 then (([s230,s152,s91,s93,s250,s22,s79,s47,s49,s27,s272] : Row)) else (([s142,s230,s150,s103,s250,s22,s79,s47,s49,s27,s272] : Row)))))) else (if i < 326 then (if i < 322 then (if i < 320 then (([s230,s152,s91,s99,s250,s22,s47,s85,s49,s27,s272] : Row)) else (if i < 321 then (([s145,s230,s103,s250,s22,s47,s85,s49,s27,s272,s282] : Row)) else (([s230,s152,s91,s92,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 324 then (if i < 323 then (([s142,s150,s231,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s152,s242,s91,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 325 then (([s142,s230,s150,s91,s98,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s152,s91,s99,s250,s22,s47,s49,s27,s120,s272] : Row))))) else (if i < 329 then (if i < 327 then (([s230,s152,s91,s99,s250,s22,s47,s49,s27,s122,s272] : Row)) else (if i < 328 then (([s230,s152,s91,s99,s250,s22,s47,s128,s49,s27,s272] : Row)) else (([s230,s152,s91,s99,s250,s22,s47,s130,s49,s27,s272] : Row)))) else (if i < 331 then (if i < 330 then (([s142,s230,s152,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s230,s91,s99,s250,s22,s47,s49,s27,s167,s272] : Row))) else (if i < 332 then (([s145,s230,s148,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s152,s91,s99,s250,s22,s47,s49,s27,s272] : Row))))))))) else (if i < 389 then (if i < 361 then (if i < 347 then (if i < 340 then (if i < 336 then (if i < 334 then (([s145,s230,s91,s99,s250,s264,s22,s47,s49,s27,s272] : Row)) else (if i < 335 then (([s230,s148,s150,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s148,s152,s91,s99,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 338 then (if i < 337 then (([s230,s148,s91,s99,s250,s22,s47,s49,s27,s165,s272] : Row)) else (([s230,s152,s91,s99,s250,s22,s172,s47,s49,s27,s272] : Row))) else (if i < 339 then (([s230,s152,s91,s99,s250,s22,s47,s179,s49,s27,s272] : Row)) else (([s230,s152,s91,s197,s99,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 343 then (if i < 341 then (([s230,s152,s91,s201,s99,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 342 then (([s230,s152,s91,s99,s250,s22,s47,s211,s49,s27,s272] : Row)) else (([s230,s152,s91,s99,s250,s22,s47,s215,s49,s27,s272] : Row)))) else (if i < 345 then (if i < 344 then (([s230,s152,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s152,s91,s99,s250,s22,s47,s49,s27,s272,s306] : Row))) else (if i < 346 then (([s143,s230,s64,s91,s93,s250,s22,s47,s51,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s85,s55,s27,s272] : Row)))))) else (if i < 354 then (if i < 350 then (if i < 348 then (([s145,s230,s63,s103,s250,s22,s47,s87,s55,s27,s272] : Row)) else (if i < 349 then (([s145,s230,s63,s91,s99,s250,s22,s47,s55,s27,s272] : Row)) else (([s145,s230,s63,s91,s103,s250,s22,s47,s55,s27,s272] : Row)))) else (if i < 352 then (if i < 351 then (([s145,s230,s63,s91,s250,s22,s112,s47,s55,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s55,s27,s120,s272] : Row))) else (if i < 353 then (([s145,s230,s63,s103,s250,s22,s47,s128,s55,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s134,s55,s27,s272] : Row))))) else (if i < 357 then (if i < 355 then (([s142,s145,s230,s63,s103,s250,s22,s47,s55,s27,s272] : Row)) else (if i < 356 then (([s142,s230,s63,s150,s103,s250,s22,s47,s55,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s172,s47,s55,s27,s272] : Row)))) else (if i < 359 then (if i < 358 then (([s145,s230,s63,s103,s250,s22,s47,s179,s55,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s187,s55,s27,s272] : Row))) else (if i < 360 then (([s145,s230,s63,s197,s103,s250,s22,s47,s55,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s211,s55,s27,s272] : Row))))))) else (if i < 375 then (if i < 368 then (if i < 364 then (if i < 362 then (([s145,s230,s63,s103,s250,s22,s47,s221,s55,s27,s272] : Row)) else (if i < 363 then (([s145,s230,s63,s103,s250,s22,s47,s55,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s55,s27,s272,s306] : Row)))) else (if i < 366 then (if i < 365 then (([s143,s230,s64,s91,s93,s250,s22,s47,s55,s27,s272] : Row)) else (([s142,s143,s230,s70,s93,s250,s22,s47,s55,s27,s272] : Row))) else (if i < 367 then (([s142,s230,s150,s91,s99,s250,s22,s47,s55,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s85,s56,s27,s272] : Row))))) else (if i < 371 then (if i < 369 then (([s145,s230,s63,s103,s250,s22,s47,s87,s56,s27,s272] : Row)) else (if i < 370 then (([s145,s230,s63,s91,s103,s250,s22,s47,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s56,s27,s120,s272] : Row)))) else (if i < 373 then (if i < 372 then (([s145,s230,s63,s103,s250,s22,s47,s128,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s134,s56,s27,s272] : Row))) else (if i < 374 then (([s145,s230,s63,s197,s103,s250,s22,s47,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s211,s56,s27,s272] : Row)))))) else (if i < 382 then (if i < 378 then (if i < 376 then (([s145,s230,s63,s103,s250,s22,s47,s221,s56,s27,s272] : Row)) else (if i < 377 then (([s145,s230,s63,s103,s250,s22,s47,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s56,s27,s272,s306] : Row)))) else (if i < 380 then (if i < 379 then (([s143,s230,s64,s91,s93,s250,s22,s47,s56,s27,s272] : Row)) else (([s142,s230,s150,s91,s99,s250,s22,s47,s56,s27,s272] : Row))) else (if i < 381 then (([s145,s230,s63,s103,s250,s22,s47,s239,s87,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s134,s263,s27,s272] : Row))))) else (if i < 385 then (if i < 383 then (([s142,s143,s230,s91,s93,s22,s47,s77,s257,s27,s272] : Row)) else (if i < 384 then (([s145,s230,s63,s103,s250,s22,s85,s87,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s85,s56,s27,s120,s272] : Row)))) else (if i < 387 then (if i < 386 then (([s145,s230,s63,s103,s250,s22,s85,s128,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s85,s134,s56,s27,s272] : Row))) else (if i < 388 then (([s145,s230,s63,s197,s103,s250,s22,s85,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s85,s211,s56,s27,s272] : Row)))))))) else (if i < 417 then (if i < 403 then (if i < 396 then (if i < 392 then (if i < 390 then (([s145,s230,s63,s103,s250,s22,s85,s221,s56,s27,s272] : Row)) else (if i < 391 then (([s145,s230,s63,s103,s250,s22,s85,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s85,s56,s27,s272,s306] : Row)))) else (if i < 394 then (if i < 393 then (([s145,s230,s63,s103,s250,s22,s128,s130,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s128,s135,s56,s27,s272] : Row))) else (if i < 395 then (([s145,s230,s63,s103,s250,s22,s179,s128,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s128,s187,s56,s27,s272] : Row))))) else (if i < 399 then (if i < 397 then (([s145,s230,s63,s103,s250,s22,s128,s211,s56,s27,s272] : Row)) else (if i < 398 then (([s145,s230,s63,s103,s250,s22,s128,s215,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s128,s223,s56,s27,s272] : Row)))) else (if i < 401 then (if i < 400 then (([s145,s230,s63,s103,s250,s22,s128,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s128,s56,s27,s272,s306] : Row))) else (if i < 402 then (([s145,s230,s63,s103,s250,s22,s211,s216,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s211,s56,s27,s272] : Row)))))) else (if i < 410 then (if i < 406 then (if i < 404 then (([s145,s230,s63,s103,s250,s22,s211,s56,s27,s272,s306] : Row)) else (if i < 405 then (([s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s56,s27,s272,s306] : Row)))) else (if i < 408 then (if i < 407 then (([s143,s230,s64,s91,s93,s250,s22,s85,s56,s27,s272] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s56,s27,s120,s272] : Row))) else (if i < 409 then (([s143,s230,s64,s91,s93,s250,s22,s128,s56,s27,s272] : Row)) else (([s142,s143,s230,s64,s91,s93,s250,s22,s56,s27,s272] : Row))))) else (if i < 413 then (if i < 411 then (([s143,s230,s64,s91,s93,s250,s22,s172,s56,s27,s272] : Row)) else (if i < 412 then (([s143,s230,s64,s91,s93,s250,s22,s173,s56,s27,s272] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s179,s56,s27,s272] : Row)))) else (if i < 415 then (if i < 414 then (([s143,s230,s64,s91,s93,s250,s22,s180,s56,s27,s272] : Row)) else (([s143,s230,s64,s91,s197,s93,s250,s22,s56,s27,s272] : Row))) else (if i < 416 then (([s143,s230,s64,s91,s198,s93,s250,s22,s56,s27,s272] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s211,s56,s27,s272] : Row))))))) else (if i < 431 then (if i < 424 then (if i < 420 then (if i < 418 then (([s143,s230,s64,s91,s93,s250,s22,s212,s56,s27,s272] : Row)) else (if i < 419 then (([s143,s230,s64,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s56,s27,s272,s306] : Row)))) else (if i < 422 then (if i < 421 then (([s142,s143,s230,s67,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s142,s143,s230,s91,s93,s250,s75,s22,s56,s27,s272] : Row))) else (if i < 423 then (([s142,s143,s230,s91,s93,s250,s22,s76,s56,s27,s272] : Row)) else (([s142,s143,s230,s91,s93,s250,s22,s56,s78,s27,s272] : Row))))) else (if i < 427 then (if i < 425 then (([s142,s230,s150,s91,s93,s250,s22,s79,s56,s27,s272] : Row)) else (if i < 426 then (([s145,s230,s91,s93,s250,s22,s85,s56,s27,s272,s282] : Row)) else (([s142,s230,s150,s91,s99,s250,s22,s85,s56,s27,s272] : Row)))) else (if i < 429 then (if i < 428 then (([s142,s230,s150,s91,s92,s93,s250,s22,s56,s27,s272] : Row)) else (([s142,s230,s150,s242,s91,s93,s250,s22,s56,s27,s272] : Row))) else (if i < 430 then (([s142,s230,s150,s91,s99,s250,s22,s56,s27,s120,s272] : Row)) else (([s142,s230,s150,s91,s99,s250,s22,s56,s27,s122,s272] : Row)))))) else (if i < 438 then (if i < 434 then (if i < 432 then (([s142,s230,s150,s91,s99,s250,s22,s128,s56,s27,s272] : Row)) else (if i < 433 then (([s142,s230,s150,s91,s99,s250,s22,s130,s56,s27,s272] : Row)) else (([s142,s230,s150,s91,s197,s99,s250,s22,s56,s27,s272] : Row)))) else (if i < 436 then (if i < 435 then (([s142,s230,s150,s91,s198,s99,s250,s22,s56,s27,s272] : Row)) else (([s142,s230,s150,s91,s202,s99,s250,s22,s56,s27,s272] : Row))) else (if i < 437 then (([s142,s230,s150,s91,s99,s250,s22,s211,s56,s27,s272] : Row)) else (([s142,s230,s150,s91,s99,s250,s22,s212,s56,s27,s272] : Row))))) else (if i < 441 then (if i < 439 then (([s142,s230,s150,s91,s99,s250,s22,s216,s56,s27,s272] : Row)) else (if i < 440 then (([s142,s230,s150,s91,s99,s250,s22,s56,s27,s272] : Row)) else (([s142,s230,s150,s91,s99,s250,s22,s56,s27,s272,s306] : Row)))) else (if i < 443 then (if i < 442 then (([s142,s143,s230,s91,s99,s250,s22,s47,s49,s28,s272] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s47,s49,s29,s272] : Row))) else (if i < 444 then (([s142,s143,s230,s70,s93,s250,s22,s47,s49,s33,s272] : Row)) else (([s142,s143,s230,s91,s99,s250,s22,s47,s80,s60,s272] : Row))))))))))
def route10 (i : ℕ) := if i < 222 then (if i < 111 then (if i < 55 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then ((0x148014000c0 : ℕ)) else (if i < 2 then ((0x1880040 : ℕ)) else ((0xc0 : ℕ)))) else (if i < 4 then ((0x1000080 : ℕ)) else (if i < 5 then ((0x1c801c90108 : ℕ)) else ((0x140 : ℕ))))) else (if i < 9 then (if i < 7 then ((0x1800040 : ℕ)) else (if i < 8 then ((0x1c00080 : ℕ)) else ((0x12801e0 : ℕ)))) else (if i < 11 then (if i < 10 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 12 then ((0x0 : ℕ)) else ((0x0 : ℕ)))))) else (if i < 20 then (if i < 16 then (if i < 14 then ((0x1801180128012000100110010801000000 : ℕ)) else (if i < 15 then ((0x0 : ℕ)) else ((0x140 : ℕ)))) else (if i < 18 then (if i < 17 then ((0x1d001c0 : ℕ)) else ((0x240020017c04b482d002d014c6818c01b101a80 : ℕ))) else (if i < 19 then ((0x2800200558028402880 : ℕ)) else ((0x2c0020055c027d028102814 : ℕ))))) else (if i < 23 then (if i < 21 then ((0x24002800282198825c81b984c2818882e882e8a1ac8 : ℕ)) else (if i < 22 then ((0x2c002401a604b881c6826e819e81ce02ee82eec : ℕ)) else ((0x2c0028056004e504ed04ed4 : ℕ)))) else (if i < 25 then (if i < 24 then ((0x30006480380064c03840900 : ℕ)) else ((0x74004400680075010c006900450 : ℕ))) else (if i < 26 then ((0x340078003c00ed011100ad00910 : ℕ)) else ((0x44042481e401780 : ℕ))))))) else (if i < 41 then (if i < 34 then (if i < 30 then (if i < 28 then ((0x48042c82d402d4134641e801800 : ℕ)) else (if i < 29 then ((0x488428834a417541ec01900 : ℕ)) else ((0x4c0180043082d802d814ca019001bd01f00 : ℕ)))) else (if i < 32 then (if i < 31 then ((0x500040043c81b401f40 : ℕ)) else ((0x6c806c905081d0043481fc0 : ℕ))) else (if i < 33 then ((0x5405448175420001bd0 : ℕ)) else ((0x580040054d820401b50 : ℕ))))) else (if i < 37 then (if i < 35 then ((0x5c007c007c1548820c01d10 : ℕ)) else (if i < 36 then ((0x6001e8056402dc02dc157d01ec020001f00 : ℕ)) else ((0x640038056802140 : ℕ)))) else (if i < 39 then (if i < 38 then ((0x68056c026801e50 : ℕ)) else ((0x6c00400570028c0 : ℕ))) else (if i < 40 then ((0x5482d4044082dc02d80 : ℕ)) else ((0x5c807c0450830402f00 : ℕ)))))) else (if i < 48 then (if i < 44 then (if i < 42 then ((0x44c8328031c0 : ℕ)) else (if i < 43 then ((0x58806c8444830d02f10 : ℕ)) else ((0x454842003700 : ℕ)))) else (if i < 46 then (if i < 45 then ((0x458845803940 : ℕ)) else ((0x4c01a2045c81ca827201a281ca045c031e0 : ℕ))) else (if i < 47 then ((0x33e4460833ec46003720 : ℕ)) else ((0x464846403724 : ℕ))))) else (if i < 51 then (if i < 49 then ((0x3424470846803950 : ℕ)) else (if i < 50 then ((0x474846c03954 : ℕ)) else ((0x478847803bc0 : ℕ)))) else (if i < 53 then (if i < 52 then ((0x47c847c03bc4 : ℕ)) else ((0x348058805c805c0034005800508050003000480060813904808054807000488054006001398480004c031e43f00 : ℕ))) else (if i < 54 then ((0x484848404040 : ℕ)) else ((0x600428056485440581042c0440044024300 : ℕ)))))))) else (if i < 83 then (if i < 69 then (if i < 62 then (if i < 58 then (if i < 56 then ((0x7003464581834a457d04ca0 : ℕ)) else (if i < 57 then ((0x740589856d04260 : ℕ)) else ((0x7c807c058e858e05020 : ℕ)))) else (if i < 60 then (if i < 59 then ((0x84008004bc81e401a80 : ℕ)) else ((0x880080057402880 : ℕ))) else (if i < 61 then ((0x84008800882260842401ac8 : ℕ)) else ((0xc0048c82100 : ℕ))))) else (if i < 65 then (if i < 63 then ((0x908090021482140 : ℕ)) else (if i < 64 then ((0x988094021c81708170955602180 : ℕ)) else ((0xb0809c02e4817002200 : ℕ)))) else (if i < 67 then (if i < 66 then ((0xbc80a0031182240 : ℕ)) else ((0xb8832c822c0 : ℕ))) else (if i < 68 then ((0xb480f000f010a4030882300 : ℕ)) else ((0xc0848882340 : ℕ)))))) else (if i < 76 then (if i < 72 then (if i < 70 then ((0xc4049082380 : ℕ)) else (if i < 71 then ((0xc80494823c01780 : ℕ)) else ((0xcc0184049882e002e014ce019401c102400 : ℕ)))) else (if i < 74 then (if i < 73 then ((0xd0049c82440 : ℕ)) else ((0xd404a482480 : ℕ))) else (if i < 75 then ((0xd484a0824c0 : ℕ)) else ((0xd804a882500 : ℕ))))) else (if i < 79 then (if i < 77 then ((0x3590bc003580bc10b800b810dc00b400b410a4008c00a0009400e4813d04ac80b000b010e80098009c00a8014182540 : ℕ)) else (if i < 78 then ((0xe004b082580 : ℕ)) else ((0xe400a80218057802e402e41585021c022002202 : ℕ)))) else (if i < 81 then (if i < 80 then ((0xe880e805560585855685850 : ℕ)) else ((0xfc00f400f800f8226482140 : ℕ))) else (if i < 82 then ((0x10801040 : ℕ)) else ((0x10901080 : ℕ))))))) else (if i < 97 then (if i < 90 then (if i < 86 then (if i < 84 then ((0x10c02680 : ℕ)) else (if i < 85 then ((0x1140 : ℕ)) else ((0x118042481e401780 : ℕ)))) else (if i < 88 then (if i < 87 then ((0x11c811c021482140 : ℕ)) else ((0x1200 : ℕ))) else (if i < 89 then ((0x1200 : ℕ)) else ((0x12402d802d814ca01bd0 : ℕ))))) else (if i < 93 then (if i < 91 then ((0x12401ca827201ca00440 : ℕ)) else (if i < 92 then ((0x1280 : ℕ)) else ((0x1280 : ℕ)))) else (if i < 95 then (if i < 94 then ((0x12c042601780 : ℕ)) else ((0x1e6017a012c0 : ℕ))) else (if i < 96 then ((0x134021601300 : ℕ)) else ((0x1380446044611d104360 : ℕ)))))) else (if i < 104 then (if i < 100 then (if i < 98 then ((0x20601b601f601380 : ℕ)) else (if i < 99 then ((0x14002260226113c0 : ℕ)) else ((0x1440 : ℕ)))) else (if i < 102 then (if i < 101 then ((0x1440 : ℕ)) else ((0x17881480 : ℕ))) else (if i < 103 then ((0x14d014c0 : ℕ)) else ((0x3380338115004d204d08 : ℕ))))) else (if i < 107 then (if i < 105 then ((0x1d584d604d6215002748 : ℕ)) else (if i < 106 then ((0x1540 : ℕ)) else ((0x1540 : ℕ)))) else (if i < 109 then (if i < 108 then ((0x1540 : ℕ)) else ((0x15802d002d01 : ℕ))) else (if i < 110 then ((0x15801b98 : ℕ)) else ((0x15801c68 : ℕ))))))))) else (if i < 166 then (if i < 138 then (if i < 124 then (if i < 117 then (if i < 114 then (if i < 112 then ((0x15c02d802d81 : ℕ)) else (if i < 113 then ((0x15c01bd8 : ℕ)) else ((0x15c01ca80440 : ℕ)))) else (if i < 115 then ((0x17881600 : ℕ)) else (if i < 116 then ((0x17a01600 : ℕ)) else ((0x16801640 : ℕ))))) else (if i < 120 then (if i < 118 then ((0x16c0 : ℕ)) else (if i < 119 then ((0x16c0 : ℕ)) else ((0x334035004e20 : ℕ)))) else (if i < 122 then (if i < 121 then ((0x16c0 : ℕ)) else ((0x3600 : ℕ))) else (if i < 123 then ((0x3640 : ℕ)) else ((0x3680 : ℕ)))))) else (if i < 131 then (if i < 127 then (if i < 125 then ((0x36c0 : ℕ)) else (if i < 126 then ((0x3700 : ℕ)) else ((0x37402780 : ℕ)))) else (if i < 129 then (if i < 128 then ((0x4f084f493780 : ℕ)) else ((0x37c0 : ℕ))) else (if i < 130 then ((0x3800 : ℕ)) else ((0x3840 : ℕ))))) else (if i < 134 then (if i < 132 then ((0x3880 : ℕ)) else (if i < 133 then ((0x17881780 : ℕ)) else ((0x198817c0 : ℕ)))) else (if i < 136 then (if i < 135 then ((0x19081800 : ℕ)) else ((0x19481840 : ℕ))) else (if i < 137 then ((0x2848284918c81880 : ℕ)) else ((0x1a4817d0 : ℕ))))))) else (if i < 152 then (if i < 145 then (if i < 141 then (if i < 139 then ((0x19c84e684e691890 : ℕ)) else (if i < 140 then ((0x1a081810 : ℕ)) else ((0x19d818d027c0 : ℕ)))) else (if i < 143 then (if i < 142 then ((0x1a581990 : ℕ)) else ((0x1a181910 : ℕ))) else (if i < 144 then ((0x1ac81a8028802882 : ℕ)) else ((0x1cc81b00 : ℕ))))) else (if i < 148 then (if i < 146 then ((0x1d081b4028c028c2 : ℕ)) else (if i < 147 then ((0x1c481b80 : ℕ)) else ((0x1c881bc0 : ℕ)))) else (if i < 150 then (if i < 149 then ((0x290829091d481d40290029021000 : ℕ)) else ((0x2e881b10 : ℕ))) else (if i < 151 then ((0x2d481754 : ℕ)) else ((0x2d881bd0 : ℕ)))))) else (if i < 159 then (if i < 155 then (if i < 153 then ((0x2e081c10 : ℕ)) else (if i < 154 then ((0x2d081b90 : ℕ)) else ((0x2ed81a902800 : ℕ)))) else (if i < 157 then (if i < 156 then ((0x2f181b5028c0 : ℕ)) else ((0x30181d802a00 : ℕ))) else (if i < 158 then ((0x319831992fd81dc02900 : ℕ)) else ((0x2ec84ee84ee91ad0 : ℕ))))) else (if i < 162 then (if i < 160 then ((0x31c8 : ℕ)) else (if i < 161 then ((0x324829802a40 : ℕ)) else ((0x330833093208 : ℕ)))) else (if i < 164 then (if i < 163 then ((0x33582980 : ℕ)) else ((0x2e981cd0 : ℕ))) else (if i < 165 then ((0x2f08502050211d10 : ℕ)) else ((0x2f88552855291dd029c02ac0 : ℕ)))))))) else (if i < 194 then (if i < 180 then (if i < 173 then (if i < 169 then (if i < 167 then ((0x314831492f485958552055211e00 : ℕ)) else (if i < 168 then ((0x338850a050a11d5029c0 : ℕ)) else ((0x334850605061 : ℕ)))) else (if i < 171 then (if i < 170 then ((0x2d981c90 : ℕ)) else ((0x2d181c50 : ℕ))) else (if i < 172 then ((0x33c8 : ℕ)) else ((0x33d8 : ℕ))))) else (if i < 176 then (if i < 174 then ((0x3408 : ℕ)) else (if i < 175 then ((0x3418 : ℕ)) else ((0x34d81b502a00 : ℕ)))) else (if i < 178 then (if i < 177 then ((0x35181b502a40 : ℕ)) else ((0x35582a80 : ℕ))) else (if i < 179 then ((0x358a522252231d502ac0 : ℕ)) else ((0x35d82b00 : ℕ)))))) else (if i < 187 then (if i < 183 then (if i < 181 then ((0x350850e050e11d10 : ℕ)) else (if i < 182 then ((0x35c851205121 : ℕ)) else ((0x3648 : ℕ)))) else (if i < 185 then (if i < 184 then ((0x36c8 : ℕ)) else ((0x3688 : ℕ))) else (if i < 186 then ((0x3708 : ℕ)) else ((0x37882b80 : ℕ))))) else (if i < 190 then (if i < 188 then ((0x4d884d893748 : ℕ)) else (if i < 189 then ((0x37d8 : ℕ)) else ((0x3808 : ℕ)))) else (if i < 192 then (if i < 191 then ((0x37c8 : ℕ)) else ((0x38c0 : ℕ))) else (if i < 193 then ((0x3900 : ℕ)) else ((0x3908 : ℕ))))))) else (if i < 208 then (if i < 201 then (if i < 197 then (if i < 195 then ((0x3940 : ℕ)) else (if i < 196 then ((0x39802bc0 : ℕ)) else ((0x4f884fc93988 : ℕ)))) else (if i < 199 then (if i < 198 then ((0x39c0 : ℕ)) else ((0x3a00 : ℕ))) else (if i < 200 then ((0x3a40 : ℕ)) else ((0x3a80 : ℕ))))) else (if i < 204 then (if i < 202 then ((0x3a08 : ℕ)) else (if i < 203 then ((0x3ac0 : ℕ)) else ((0x3b00 : ℕ)))) else (if i < 206 then (if i < 205 then ((0x39c8 : ℕ)) else ((0x3b40 : ℕ))) else (if i < 207 then ((0x3ac8 : ℕ)) else ((0x3858 : ℕ)))))) else (if i < 215 then (if i < 211 then (if i < 209 then ((0x38980458 : ℕ)) else (if i < 210 then ((0x38d8 : ℕ)) else ((0x3918 : ℕ)))) else (if i < 213 then (if i < 212 then ((0x3958 : ℕ)) else ((0x3a18 : ℕ))) else (if i < 214 then ((0x3a98 : ℕ)) else ((0x3b18 : ℕ))))) else (if i < 218 then (if i < 216 then ((0x39e8 : ℕ)) else (if i < 217 then ((0x3ae8 : ℕ)) else ((0x3a68 : ℕ)))) else (if i < 220 then (if i < 219 then ((0x3b58 : ℕ)) else ((0x3b80 : ℕ))) else (if i < 221 then ((0x3b98 : ℕ)) else ((0x3bc0 : ℕ)))))))))) else (if i < 333 then (if i < 277 then (if i < 249 then (if i < 235 then (if i < 228 then (if i < 225 then (if i < 223 then ((0x3c00 : ℕ)) else (if i < 224 then ((0x3c40 : ℕ)) else ((0x3c80 : ℕ)))) else (if i < 226 then ((0x3c60 : ℕ)) else (if i < 227 then ((0x3cc0 : ℕ)) else ((0x3c18 : ℕ))))) else (if i < 231 then (if i < 229 then ((0x3c88 : ℕ)) else (if i < 230 then ((0x3cd8 : ℕ)) else ((0x3d00 : ℕ)))) else (if i < 233 then (if i < 232 then ((0x3d08 : ℕ)) else ((0x3d4011c0 : ℕ))) else (if i < 234 then ((0x3d801310 : ℕ)) else ((0x3e0013104e88 : ℕ)))))) else (if i < 242 then (if i < 238 then (if i < 236 then ((0x3e0813582b40 : ℕ)) else (if i < 237 then ((0x3d881358 : ℕ)) else ((0x3dc81358 : ℕ)))) else (if i < 240 then (if i < 239 then ((0x3e4014e0 : ℕ)) else ((0x3e8014e0 : ℕ))) else (if i < 241 then ((0x3e4814e0 : ℕ)) else ((0x3ec0164810401660 : ℕ))))) else (if i < 245 then (if i < 243 then ((0x4592f1004582f1131c031c13f002f002f011d1009101b501d001b400900 : ℕ)) else (if i < 244 then ((0x119911983d58 : ℕ)) else ((0x12c912c83e1851605161 : ℕ)))) else (if i < 247 then (if i < 246 then ((0x12c912c83d98 : ℕ)) else ((0x12c912c83dd8 : ℕ))) else (if i < 248 then ((0x148114803e68 : ℕ)) else ((0x148114803e98 : ℕ))))))) else (if i < 263 then (if i < 256 then (if i < 252 then (if i < 250 then ((0x1088160116003ec816a8 : ℕ)) else (if i < 251 then ((0x3f40 : ℕ)) else ((0x3f80 : ℕ)))) else (if i < 254 then (if i < 253 then ((0x3fc0 : ℕ)) else ((0x3f88 : ℕ))) else (if i < 255 then ((0x4000 : ℕ)) else ((0x3f58 : ℕ))))) else (if i < 259 then (if i < 257 then ((0x3f98 : ℕ)) else (if i < 258 then ((0x3fd8 : ℕ)) else ((0x4018 : ℕ)))) else (if i < 261 then (if i < 260 then ((0x4040 : ℕ)) else ((0x40802b90 : ℕ))) else (if i < 262 then ((0x40c02bd0 : ℕ)) else ((0x41002c00 : ℕ)))))) else (if i < 270 then (if i < 266 then (if i < 264 then ((0x41402c40 : ℕ)) else (if i < 265 then ((0x5d92fd005d82fd13200320141802f402f411dd00a101d40274002101d802b002c800f402b40 : ℕ)) else ((0x41c02cc0 : ℕ)))) else (if i < 268 then (if i < 267 then ((0x1d005188518934e0 : ℕ)) else ((0x51c851c93560 : ℕ))) else (if i < 269 then ((0x524852494088 : ℕ)) else ((0x52c853094108 : ℕ))))) else (if i < 273 then (if i < 271 then ((0x5288528940c8 : ℕ)) else (if i < 272 then ((0x534853894148 : ℕ)) else ((0x2d805994e09301053c805984e08301153c93240324141884d082f802f811e000a501d401dc00fc84e88 : ℕ)))) else (if i < 275 then (if i < 274 then ((0x5408540941c8 : ℕ)) else ((0x4200 : ℕ))) else (if i < 276 then ((0x42401e40 : ℕ)) else ((0x42801e80 : ℕ)))))))) else (if i < 305 then (if i < 291 then (if i < 284 then (if i < 280 then (if i < 278 then ((0x42c01ec0 : ℕ)) else (if i < 279 then ((0x43001f00 : ℕ)) else ((0x43401f40 : ℕ)))) else (if i < 282 then (if i < 281 then ((0x43801f8029402942 : ℕ)) else ((0x5708570943c01fc0 : ℕ))) else (if i < 283 then ((0x44002000 : ℕ)) else ((0x4440204028c0 : ℕ))))) else (if i < 287 then (if i < 285 then ((0x448020802940 : ℕ)) else (if i < 286 then ((0x44c0 : ℕ)) else ((0x450058e058e120c0 : ℕ)))) else (if i < 289 then (if i < 288 then ((0x4540 : ℕ)) else ((0x4580 : ℕ))) else (if i < 290 then ((0x45c01f00 : ℕ)) else ((0x4600 : ℕ)))))) else (if i < 298 then (if i < 294 then (if i < 292 then ((0x4640 : ℕ)) else (if i < 293 then ((0x4680 : ℕ)) else ((0x46c0 : ℕ)))) else (if i < 296 then (if i < 295 then ((0x4700 : ℕ)) else ((0x4740 : ℕ))) else (if i < 297 then ((0x4780 : ℕ)) else ((0x47c0 : ℕ))))) else (if i < 301 then (if i < 299 then ((0x75930d0075830d13280328148003040304120c00ad020801fc01f800384 : ℕ)) else (if i < 300 then ((0x4840 : ℕ)) else ((0x48802100 : ℕ)))) else (if i < 303 then (if i < 302 then ((0x48c02340 : ℕ)) else ((0x49002380 : ℕ))) else (if i < 304 then ((0x494023c0 : ℕ)) else ((0x49802400 : ℕ))))))) else (if i < 319 then (if i < 312 then (if i < 308 then (if i < 306 then ((0x49c02440 : ℕ)) else (if i < 307 then ((0x4a002480 : ℕ)) else ((0x4a4024c0 : ℕ)))) else (if i < 310 then (if i < 309 then ((0x4a802500 : ℕ)) else ((0x79931100798311132c032c14ac030803081230003d2230203d022c022c2254022802282 : ℕ))) else (if i < 311 then ((0x4b002580 : ℕ)) else ((0x558855894b4025c0 : ℕ))))) else (if i < 315 then (if i < 313 then ((0x560856094b8025c0 : ℕ)) else (if i < 314 then ((0x574857494bc02600 : ℕ)) else ((0x4c0026c0 : ℕ)))) else (if i < 317 then (if i < 316 then ((0x4c4026c0 : ℕ)) else ((0x4c802700 : ℕ))) else (if i < 318 then ((0x4d005950595129c029c22740 : ℕ)) else ((0x4d405910591129102740 : ℕ)))))) else (if i < 326 then (if i < 322 then (if i < 320 then ((0x4d802780 : ℕ)) else (if i < 321 then ((0x27004dc0 : ℕ)) else ((0x4e0029802a40 : ℕ)))) else (if i < 324 then (if i < 323 then ((0x4e40285027c0 : ℕ)) else ((0x4e802b402140 : ℕ))) else (if i < 325 then ((0x4ec028902800 : ℕ)) else ((0x4f002b80 : ℕ))))) else (if i < 329 then (if i < 327 then ((0x4f402b82 : ℕ)) else (if i < 328 then ((0x4f802bc0 : ℕ)) else ((0x4fc02bc2 : ℕ)))) else (if i < 331 then (if i < 330 then ((0x50402990 : ℕ)) else ((0x59805981508029d02900 : ℕ))) else (if i < 332 then ((0x50c02a5028c0 : ℕ)) else ((0x51002b10 : ℕ))))))))) else (if i < 389 then (if i < 361 then (if i < 347 then (if i < 340 then (if i < 336 then (if i < 334 then ((0x51401e522b50 : ℕ)) else (if i < 335 then ((0x51802a1028c0 : ℕ)) else ((0x51c02a90 : ℕ)))) else (if i < 338 then (if i < 337 then ((0x59c059c152002ad02900 : ℕ)) else ((0x52402b90 : ℕ))) else (if i < 339 then ((0x52802bd0 : ℕ)) else ((0x52c02c00 : ℕ))))) else (if i < 343 then (if i < 341 then ((0x53002c02 : ℕ)) else (if i < 342 then ((0x53402c40 : ℕ)) else ((0x53802c42 : ℕ)))) else (if i < 345 then (if i < 344 then ((0x7d9319007d831913300330153c03140314129c008122ac2041029802a822c8029000f80 : ℕ)) else ((0x54002cc0 : ℕ))) else (if i < 346 then ((0x54402dc0 : ℕ)) else ((0x40a84f20 : ℕ)))))) else (if i < 354 then (if i < 350 then (if i < 348 then ((0x178040a94f60 : ℕ)) else (if i < 349 then ((0x2f9850a052202fc03140 : ℕ)) else ((0x3258506050e0 : ℕ)))) else (if i < 352 then (if i < 351 then ((0x300851a8300051a0 : ℕ)) else ((0x37985260 : ℕ))) else (if i < 353 then ((0x412852e0 : ℕ)) else ((0x178041295320 : ℕ))))) else (if i < 357 then (if i < 355 then ((0x32283320 : ℕ)) else (if i < 356 then ((0x2f6831a8591031802f40 : ℕ)) else ((0x37684da0 : ℕ)))) else (if i < 359 then (if i < 358 then ((0x40e84fa0 : ℕ)) else ((0x178040e94fe0 : ℕ))) else (if i < 360 then ((0x39a852a0 : ℕ)) else ((0x41685360 : ℕ))))))) else (if i < 375 then (if i < 368 then (if i < 364 then (if i < 362 then ((0x1780416953a0 : ℕ)) else (if i < 363 then ((0x8693380052835813340354141a8516034c002a05120300053e00bd04d682fc02f802f400b40 : ℕ)) else ((0x41e85420 : ℕ)))) else (if i < 366 then (if i < 365 then ((0x548058e058e23040 : ℕ)) else ((0x54c0572030c0 : ℕ))) else (if i < 367 then ((0x5500599059d231803140 : ℕ)) else ((0x0 : ℕ))))) else (if i < 371 then (if i < 369 then ((0x1780380016c0 : ℕ)) else (if i < 370 then ((0x39401280 : ℕ)) else ((0x39c81440 : ℕ)))) else (if i < 373 then (if i < 372 then ((0x0 : ℕ)) else ((0x17803a0816c0 : ℕ))) else (if i < 374 then ((0x3bc01440 : ℕ)) else ((0x0 : ℕ)))))) else (if i < 382 then (if i < 378 then (if i < 376 then ((0x17803c1816c0 : ℕ)) else (if i < 377 then ((0xc9833503f5804d8351012903340350012803d9015503a00128032500b903700114032103d80154032403a10129032000b80 : ℕ)) else ((0x0 : ℕ)))) else (if i < 380 then (if i < 379 then ((0x3280 : ℕ)) else ((0x33103300 : ℕ))) else (if i < 381 then ((0x2d00 : ℕ)) else ((0x2d90 : ℕ))))) else (if i < 385 then (if i < 383 then ((0x34903440 : ℕ)) else (if i < 384 then ((0x38003680 : ℕ)) else ((0x3b403600 : ℕ)))) else (if i < 387 then (if i < 386 then ((0x39c036c0 : ℕ)) else ((0x3ac03640 : ℕ))) else (if i < 388 then ((0x3c403600 : ℕ)) else ((0x3c4036c0 : ℕ)))))))) else (if i < 417 then (if i < 403 then (if i < 396 then (if i < 392 then (if i < 390 then ((0x3cd83640 : ℕ)) else (if i < 391 then ((0xd1840983fd8125837d01290380031c040a837c012803e5015903a40144837900c104dc037503e40158037803a50146037400c00 : ℕ)) else ((0x0 : ℕ)))) else (if i < 394 then (if i < 393 then ((0x3a003908 : ℕ)) else ((0x3b0038c0 : ℕ))) else (if i < 395 then ((0x3bc036c0 : ℕ)) else ((0x3c183640 : ℕ))))) else (if i < 399 then (if i < 397 then ((0x0 : ℕ)) else (if i < 398 then ((0x3c103908 : ℕ)) else ((0x3ca038c0 : ℕ)))) else (if i < 401 then (if i < 400 then ((0xd5840d83fa815d839c812903a0831c041283a8012803fa015d03a0031c841200d5039c0129840d03e80384039883c00146039800c40 : ℕ)) else ((0x0 : ℕ))) else (if i < 402 then ((0x3c803b98 : ℕ)) else ((0xd984158401838983c4812903c1831c041683c601280401038903c1031c841600d903c40129841504000388041483c0031e041400d80 : ℕ)))))) else (if i < 410 then (if i < 406 then (if i < 404 then ((0x0 : ℕ)) else (if i < 405 then ((0x3e2802583f580cd80dd835d0419812903e1802681500114035c041a812803ee03d203d5012103dd015503e1002603dd81558380811403b00128035c841a012803f500cd00dd03d5812181520114038001140150811403e20025035d8419012983ec83d083e0002483dc015403d4012003ec03d003dc815483e0802403de8156835e0418812903b101290382011403de015603b18129835e8418012983f400cc00dc0 : ℕ)) else ((0xe1841d841e841e00e1041d041c841c00e00 : ℕ)))) else (if i < 408 then (if i < 407 then ((0x4200 : ℕ)) else ((0x4540 : ℕ))) else (if i < 409 then ((0x4580 : ℕ)) else ((0x45c04300 : ℕ))))) else (if i < 413 then (if i < 411 then ((0x4600 : ℕ)) else (if i < 412 then ((0x4640 : ℕ)) else ((0x4680 : ℕ)))) else (if i < 415 then (if i < 414 then ((0x46c0 : ℕ)) else ((0x4700 : ℕ))) else (if i < 416 then ((0x4740 : ℕ)) else ((0x4780 : ℕ))))))) else (if i < 431 then (if i < 424 then (if i < 420 then (if i < 418 then ((0x47c0 : ℕ)) else (if i < 419 then ((0xed854d05480450006924502069044c044c248004480448243c043800644 : ℕ)) else ((0x4840 : ℕ)))) else (if i < 422 then (if i < 421 then ((0x55c84b804b40 : ℕ)) else ((0x4c404c00 : ℕ))) else (if i < 423 then ((0x4c904c80 : ℕ)) else ((0x4cd04cc0 : ℕ))))) else (if i < 427 then (if i < 425 then ((0x5960509050924d404d00 : ℕ)) else (if i < 426 then ((0x4c804dc0 : ℕ)) else ((0x4d904d80 : ℕ)))) else (if i < 429 then (if i < 428 then ((0x505050d04e00 : ℕ)) else ((0x515042444e80 : ℕ))) else (if i < 430 then ((0x52504f00 : ℕ)) else ((0x52524f40 : ℕ)))))) else (if i < 438 then (if i < 434 then (if i < 432 then ((0x52904f80 : ℕ)) else (if i < 433 then ((0x52924fc0 : ℕ)) else ((0x52d052c0 : ℕ)))) else (if i < 436 then (if i < 435 then ((0x531052c4 : ℕ)) else ((0x53125304 : ℕ))) else (if i < 437 then ((0x53505340 : ℕ)) else ((0x53905344 : ℕ))))) else (if i < 441 then (if i < 439 then ((0x53925384 : ℕ)) else (if i < 440 then ((0xf185510550050900892521206d0505051d253d0508008845204504051c453c006c0 : ℕ)) else ((0x54105400 : ℕ)))) else (if i < 443 then (if i < 442 then ((0x560055c05580 : ℕ)) else ((0x56485640 : ℕ))) else (if i < 444 then ((0x580057c0 : ℕ)) else ((0x59485940598059845900 : ℕ))))))))))
def stored9 (i : ℕ) := if i < 180 then (if i < 90 then (if i < 45 then (if i < 22 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then (([s0,s5,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s0,s230,s66,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 3 then (([s0,s230,s152,s107,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 4 then (([s0,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s0,s230,s63,s152,s103,s250,s22,s56,s27,s272] : Row))))) else (if i < 8 then (if i < 6 then (([s0,s143,s230,s64,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 7 then (([s0,s230,s66,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s0,s230,s152,s91,s99,s250,s22,s56,s27,s272] : Row)))) else (if i < 9 then (([s1,s145,s230,s107,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 10 then (([s1,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s1,s145,s230,s91,s99,s250,s22,s56,s27,s272] : Row)))))) else (if i < 16 then (if i < 13 then (if i < 12 then (([s1,s142,s143,s230,s107,s250,s22,s56,s27,s272] : Row)) else (([s2,s4,s230,s63,s103,s250,s22,s56,s27,s272] : Row))) else (if i < 14 then (([s2,s143,s230,s63,s12,s250,s22,s56,s27,s272] : Row)) else (if i < 15 then (([s2,s230,s65,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s2,s143,s230,s73,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 19 then (if i < 17 then (([s2,s230,s150,s107,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 18 then (([s2,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s2,s143,s230,s63,s103,s250,s22,s56,s27,s274] : Row)))) else (if i < 20 then (([s2,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 21 then (([s2,s230,s63,s150,s103,s250,s22,s56,s27,s272] : Row)) else (([s2,s143,s230,s63,s104,s250,s22,s56,s27,s272] : Row))))))) else (if i < 33 then (if i < 27 then (if i < 24 then (if i < 23 then (([s2,s143,s230,s63,s107,s250,s22,s56,s27,s272] : Row)) else (([s2,s143,s230,s63,s250,s22,s114,s56,s27,s272] : Row))) else (if i < 25 then (([s2,s143,s230,s64,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 26 then (([s2,s230,s65,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s2,s143,s230,s70,s93,s250,s22,s56,s27,s272] : Row))))) else (if i < 30 then (if i < 28 then (([s2,s230,s150,s91,s99,s250,s22,s56,s27,s272] : Row)) else (if i < 29 then (([s2,s143,s230,s63,s103,s250,s23,s56,s27,s272] : Row)) else (([s2,s143,s230,s63,s93,s250,s25,s56,s27,s272] : Row)))) else (if i < 31 then (([s2,s143,s230,s63,s250,s26,s47,s49,s27,s272] : Row)) else (if i < 32 then (([s2,s143,s230,s63,s250,s114,s47,s55,s27,s272] : Row)) else (([s3,s143,s230,s107,s250,s22,s47,s49,s27,s272] : Row)))))) else (if i < 39 then (if i < 36 then (if i < 34 then (([s3,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 35 then (([s3,s143,s230,s91,s99,s250,s22,s56,s27,s272] : Row)) else (([s5,s230,s63,s12,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 37 then (([s5,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 38 then (([s5,s230,s63,s103,s250,s22,s47,s49,s27,s276] : Row)) else (([s5,s230,s63,s103,s253,s22,s47,s49,s27,s272] : Row))))) else (if i < 42 then (if i < 40 then (([s5,s230,s63,s105,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 41 then (([s5,s230,s63,s107,s250,s22,s47,s49,s27,s272] : Row)) else (([s5,s230,s63,s250,s22,s114,s47,s49,s27,s272] : Row)))) else (if i < 43 then (([s5,s230,s66,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 44 then (([s5,s230,s70,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s5,s230,s63,s103,s250,s22,s47,s52,s27,s272] : Row)))))))) else (if i < 67 then (if i < 56 then (if i < 50 then (if i < 47 then (if i < 46 then (([s5,s230,s63,s103,s250,s22,s47,s55,s27,s272] : Row)) else (([s5,s230,s63,s103,s250,s22,s47,s56,s27,s272] : Row))) else (if i < 48 then (([s5,s230,s63,s103,s250,s22,s47,s27,s60,s272] : Row)) else (if i < 49 then (([s5,s230,s63,s103,s250,s22,s85,s56,s27,s272] : Row)) else (([s5,s230,s63,s103,s250,s22,s128,s56,s27,s272] : Row))))) else (if i < 53 then (if i < 51 then (([s142,s5,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 52 then (([s5,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s5,s230,s63,s103,s250,s22,s172,s56,s27,s272] : Row)))) else (if i < 54 then (([s5,s230,s63,s103,s250,s22,s179,s56,s27,s272] : Row)) else (if i < 55 then (([s5,s230,s63,s103,s250,s22,s211,s56,s27,s272] : Row)) else (([s5,s230,s63,s103,s250,s22,s56,s27,s272] : Row)))))) else (if i < 61 then (if i < 58 then (if i < 57 then (([s5,s230,s63,s103,s250,s22,s56,s27,s272,s306] : Row)) else (([s5,s230,s66,s91,s93,s250,s22,s56,s27,s272] : Row))) else (if i < 59 then (([s5,s230,s63,s103,s250,s24,s47,s49,s27,s272] : Row)) else (if i < 60 then (([s5,s230,s63,s93,s250,s25,s47,s49,s27,s272] : Row)) else (([s5,s230,s63,s91,s250,s112,s47,s55,s27,s272] : Row))))) else (if i < 64 then (if i < 62 then (([s6,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 63 then (([s6,s230,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s6,s230,s63,s91,s93,s250,s22,s56,s27,s272] : Row)))) else (if i < 65 then (([s7,s63,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 66 then (([s145,s230,s8,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s8,s91,s93,s250,s22,s56,s27,s272] : Row))))))) else (if i < 78 then (if i < 72 then (if i < 69 then (if i < 68 then (([s143,s230,s63,s10,s93,s250,s22,s56,s27,s272] : Row)) else (([s230,s63,s11,s93,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 70 then (([s14,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 71 then (([s15,s143,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s16,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 75 then (if i < 73 then (([s17,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 74 then (([s18,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s19,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)))) else (if i < 76 then (([s145,s230,s63,s20,s93,s250,s22,s56,s27,s272] : Row)) else (if i < 77 then (([s145,s230,s63,s21,s250,s22,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s21,s250,s22,s56,s27,s272] : Row)))))) else (if i < 84 then (if i < 81 then (if i < 79 then (([s145,s230,s63,s93,s250,s22,s25,s56,s27,s272] : Row)) else (if i < 80 then (([s145,s230,s63,s250,s22,s26,s47,s49,s27,s272] : Row)) else (([s142,s143,s230,s63,s250,s22,s26,s56,s27,s272] : Row)))) else (if i < 82 then (([s37,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 83 then (([s145,s230,s63,s103,s250,s22,s38,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s39,s27,s272] : Row))))) else (if i < 87 then (if i < 85 then (([s145,s230,s63,s103,s250,s22,s56,s27,s40,s272] : Row)) else (if i < 86 then (([s41,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s42,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)))) else (if i < 88 then (([s43,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 89 then (([s145,s230,s63,s103,s250,s22,s44,s49,s27,s272] : Row)) else (([s145,s230,s63,s91,s93,s250,s22,s45,s27,s272] : Row))))))))) else (if i < 135 then (if i < 112 then (if i < 101 then (if i < 95 then (if i < 92 then (if i < 91 then (([s142,s143,s230,s63,s103,s250,s22,s45,s27,s272] : Row)) else (([s46,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row))) else (if i < 93 then (([s230,s63,s91,s96,s253,s22,s47,s49,s27,s272] : Row)) else (if i < 94 then (([s63,s91,s158,s234,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 98 then (if i < 96 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s273] : Row)) else (if i < 97 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s274] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s276] : Row)))) else (if i < 99 then (([s145,s230,s63,s103,s250,s22,s47,s49,s27,s277] : Row)) else (if i < 100 then (([s145,s230,s63,s103,s251,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s252,s22,s47,s49,s27,s272] : Row)))))) else (if i < 106 then (if i < 103 then (if i < 102 then (([s145,s230,s63,s103,s253,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s254,s22,s47,s49,s27,s272] : Row))) else (if i < 104 then (([s145,s230,s63,s103,s22,s255,s47,s49,s27,s272] : Row)) else (if i < 105 then (([s145,s230,s63,s103,s22,s47,s256,s49,s27,s272] : Row)) else (([s145,s230,s63,s103,s22,s47,s49,s27,s259,s272] : Row))))) else (if i < 109 then (if i < 107 then (([s146,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 108 then (([s147,s230,s63,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s63,s151,s103,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 110 then (([s230,s63,s152,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 111 then (([s230,s63,s154,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s63,s156,s103,s250,s22,s47,s49,s27,s272] : Row))))))) else (if i < 123 then (if i < 117 then (if i < 114 then (if i < 113 then (([s230,s63,s103,s159,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s63,s103,s250,s160,s22,s47,s49,s27,s272] : Row))) else (if i < 115 then (([s230,s63,s103,s250,s22,s47,s161,s49,s27,s272] : Row)) else (if i < 116 then (([s230,s63,s103,s250,s22,s47,s49,s163,s27,s272] : Row)) else (([s230,s63,s103,s250,s22,s47,s49,s27,s166,s272] : Row))))) else (if i < 120 then (if i < 118 then (([s230,s63,s103,s250,s22,s47,s49,s27,s168,s272] : Row)) else (if i < 119 then (([s230,s63,s152,s107,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s63,s107,s250,s22,s47,s49,s27,s166,s272] : Row)))) else (if i < 121 then (([s230,s63,s250,s22,s114,s47,s49,s27,s166,s272] : Row)) else (if i < 122 then (([s143,s230,s64,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s143,s230,s64,s103,s250,s22,s47,s49,s27,s274] : Row)))))) else (if i < 129 then (if i < 126 then (if i < 124 then (([s143,s230,s64,s103,s252,s22,s47,s49,s27,s272] : Row)) else (if i < 125 then (([s145,s230,s64,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s64,s150,s103,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 127 then (([s230,s64,s152,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 128 then (([s230,s64,s103,s250,s22,s47,s49,s27,s165,s272] : Row)) else (([s143,s230,s64,s104,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 132 then (if i < 130 then (([s143,s230,s64,s107,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 131 then (([s143,s230,s64,s108,s250,s22,s47,s49,s27,s272] : Row)) else (([s143,s230,s64,s250,s22,s114,s47,s49,s27,s272] : Row)))) else (if i < 133 then (([s230,s66,s103,s250,s22,s47,s85,s49,s27,s272] : Row)) else (if i < 134 then (([s230,s66,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s66,s91,s93,s250,s22,s47,s49,s27,s276] : Row)))))))) else (if i < 157 then (if i < 146 then (if i < 140 then (if i < 137 then (if i < 136 then (([s230,s66,s91,s93,s253,s22,s47,s49,s27,s272] : Row)) else (([s230,s66,s91,s96,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 138 then (([s230,s66,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 139 then (([s230,s66,s91,s101,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s66,s91,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 143 then (if i < 141 then (([s230,s66,s91,s250,s22,s112,s47,s49,s27,s272] : Row)) else (if i < 142 then (([s230,s66,s103,s250,s22,s47,s49,s27,s120,s272] : Row)) else (([s230,s66,s103,s250,s22,s47,s128,s49,s27,s272] : Row)))) else (if i < 144 then (([s142,s230,s66,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 145 then (([s145,s230,s66,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s66,s103,s250,s22,s172,s47,s49,s27,s272] : Row)))))) else (if i < 151 then (if i < 148 then (if i < 147 then (([s230,s66,s103,s250,s22,s47,s179,s49,s27,s272] : Row)) else (([s230,s66,s197,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 149 then (([s230,s66,s103,s250,s22,s47,s211,s49,s27,s272] : Row)) else (if i < 150 then (([s230,s66,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s66,s103,s250,s22,s47,s49,s27,s272,s306] : Row))))) else (if i < 154 then (if i < 152 then (([s145,s230,s67,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 153 then (([s143,s230,s68,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s69,s91,s93,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 155 then (([s143,s230,s71,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 156 then (([s145,s230,s103,s250,s75,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s103,s250,s22,s47,s76,s49,s27,s272] : Row))))))) else (if i < 168 then (if i < 162 then (if i < 159 then (if i < 158 then (([s230,s152,s103,s250,s22,s79,s47,s49,s27,s272] : Row)) else (([s230,s152,s107,s250,s22,s47,s85,s49,s27,s272] : Row))) else (if i < 160 then (([s152,s231,s91,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 161 then (([s230,s152,s91,s98,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s91,s99,s251,s22,s47,s49,s27,s272] : Row))))) else (if i < 165 then (if i < 163 then (([s146,s230,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 164 then (([s230,s152,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s91,s99,s250,s22,s47,s49,s27,s168,s272] : Row)))) else (if i < 166 then (([s230,s152,s91,s100,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 167 then (([s230,s152,s91,s107,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s152,s91,s250,s22,s113,s47,s49,s27,s272] : Row)))))) else (if i < 174 then (if i < 171 then (if i < 169 then (([s230,s152,s92,s99,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 170 then (([s230,s152,s92,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s152,s92,s107,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 172 then (([s230,s152,s92,s250,s22,s112,s47,s49,s27,s272] : Row)) else (if i < 173 then (([s230,s152,s103,s107,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s152,s242,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 177 then (if i < 175 then (([s230,s152,s107,s250,s22,s47,s49,s27,s120,s272] : Row)) else (if i < 176 then (([s230,s152,s107,s250,s22,s47,s128,s49,s27,s272] : Row)) else (([s230,s152,s197,s107,s250,s22,s47,s49,s27,s272] : Row)))) else (if i < 178 then (([s230,s152,s107,s250,s22,s47,s211,s49,s27,s272] : Row)) else (if i < 179 then (([s230,s152,s107,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s152,s107,s250,s22,s47,s49,s27,s272,s306] : Row)))))))))) else (if i < 270 then (if i < 225 then (if i < 202 then (if i < 191 then (if i < 185 then (if i < 182 then (if i < 181 then (([s145,s230,s63,s103,s250,s22,s47,s50,s27,s272] : Row)) else (([s143,s230,s63,s103,s250,s22,s47,s51,s27,s274] : Row))) else (if i < 183 then (([s145,s230,s63,s103,s250,s22,s47,s51,s27,s272] : Row)) else (if i < 184 then (([s143,s230,s64,s103,s250,s22,s47,s51,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s52,s27,s272] : Row))))) else (if i < 188 then (if i < 186 then (([s230,s66,s91,s93,s250,s22,s47,s52,s27,s272] : Row)) else (if i < 187 then (([s145,s230,s63,s103,s250,s22,s47,s53,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s54,s27,s272] : Row)))) else (if i < 189 then (([s145,s230,s63,s103,s250,s22,s47,s55,s27,s272] : Row)) else (if i < 190 then (([s230,s63,s152,s103,s250,s22,s47,s55,s27,s272] : Row)) else (([s230,s63,s103,s250,s22,s47,s55,s27,s166,s272] : Row)))))) else (if i < 196 then (if i < 193 then (if i < 192 then (([s145,s230,s63,s107,s250,s22,s47,s55,s27,s272] : Row)) else (([s145,s230,s63,s250,s22,s114,s47,s55,s27,s272] : Row))) else (if i < 194 then (([s143,s230,s64,s103,s250,s22,s47,s55,s27,s272] : Row)) else (if i < 195 then (([s230,s66,s91,s93,s250,s22,s47,s55,s27,s272] : Row)) else (([s145,s230,s70,s93,s250,s22,s47,s55,s27,s272] : Row))))) else (if i < 199 then (if i < 197 then (([s142,s143,s230,s73,s250,s22,s47,s55,s27,s272] : Row)) else (if i < 198 then (([s230,s152,s91,s99,s250,s22,s47,s55,s27,s272] : Row)) else (([s142,s230,s150,s107,s250,s22,s47,s55,s27,s272] : Row)))) else (if i < 200 then (([s145,s230,s63,s103,s250,s22,s47,s56,s27,s272] : Row)) else (if i < 201 then (([s230,s63,s152,s103,s250,s22,s47,s56,s27,s272] : Row)) else (([s230,s63,s103,s250,s22,s47,s56,s27,s166,s272] : Row))))))) else (if i < 213 then (if i < 207 then (if i < 204 then (if i < 203 then (([s143,s230,s64,s103,s250,s22,s47,s56,s27,s272] : Row)) else (([s230,s66,s91,s93,s250,s22,s47,s56,s27,s272] : Row))) else (if i < 205 then (([s230,s152,s91,s99,s250,s22,s47,s56,s27,s272] : Row)) else (if i < 206 then (([s145,s230,s63,s103,s250,s22,s47,s59,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s47,s27,s61,s272] : Row))))) else (if i < 210 then (if i < 208 then (([s145,s230,s63,s103,s22,s47,s87,s257,s27,s272] : Row)) else (if i < 209 then (([s145,s230,s63,s103,s22,s47,s134,s257,s27,s272] : Row)) else (([s145,s230,s91,s93,s22,s47,s77,s257,s27,s272] : Row)))) else (if i < 211 then (([s145,s91,s93,s250,s22,s47,s235,s77,s27,s272] : Row)) else (if i < 212 then (([s145,s230,s63,s103,s250,s22,s48,s55,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s48,s56,s27,s272] : Row)))))) else (if i < 219 then (if i < 216 then (if i < 214 then (([s145,s230,s63,s103,s250,s22,s48,s59,s27,s272] : Row)) else (if i < 215 then (([s145,s230,s63,s103,s250,s22,s48,s27,s60,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s56,s59,s27,s272] : Row)))) else (if i < 217 then (([s81,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 218 then (([s82,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s145,s230,s63,s83,s103,s250,s22,s56,s27,s272] : Row))))) else (if i < 222 then (if i < 220 then (([s145,s230,s63,s103,s250,s22,s84,s56,s27,s272] : Row)) else (if i < 221 then (([s145,s230,s63,s103,s250,s22,s85,s56,s27,s272] : Row)) else (([s230,s63,s152,s103,s250,s22,s85,s56,s27,s272] : Row)))) else (if i < 223 then (([s230,s63,s103,s250,s22,s85,s56,s27,s166,s272] : Row)) else (if i < 224 then (([s145,s230,s63,s103,s250,s22,s86,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s56,s88,s27,s272] : Row)))))))) else (if i < 247 then (if i < 236 then (if i < 230 then (if i < 227 then (if i < 226 then (([s89,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s90,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row))) else (if i < 228 then (([s125,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 229 then (([s145,s230,s63,s126,s103,s250,s22,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s128,s56,s27,s272] : Row))))) else (if i < 233 then (if i < 231 then (([s230,s63,s152,s103,s250,s22,s128,s56,s27,s272] : Row)) else (if i < 232 then (([s145,s230,s63,s103,s250,s22,s129,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s131,s56,s27,s272] : Row)))) else (if i < 234 then (([s145,s230,s63,s103,s250,s22,s132,s56,s27,s272] : Row)) else (if i < 235 then (([s145,s230,s63,s103,s250,s22,s133,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s56,s137,s27,s272] : Row)))))) else (if i < 241 then (if i < 238 then (if i < 237 then (([s145,s230,s63,s103,s250,s22,s56,s138,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s56,s27,s140,s272] : Row))) else (if i < 239 then (([s208,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 240 then (([s145,s230,s63,s103,s250,s22,s211,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s213,s56,s27,s272] : Row))))) else (if i < 244 then (if i < 242 then (([s145,s230,s63,s103,s250,s22,s214,s56,s27,s272] : Row)) else (if i < 243 then (([s145,s230,s63,s103,s250,s22,s218,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s220,s56,s27,s272] : Row)))) else (if i < 245 then (([s228,s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 246 then (([s145,s230,s63,s103,s250,s22,s237,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s238,s56,s27,s272] : Row))))))) else (if i < 258 then (if i < 252 then (if i < 249 then (if i < 248 then (([s145,s230,s63,s103,s250,s22,s56,s240,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s56,s27,s241,s272] : Row))) else (if i < 250 then (([s145,s230,s63,s103,s250,s22,s246,s56,s27,s272] : Row)) else (if i < 251 then (([s145,s230,s63,s103,s250,s22,s247,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s271,s22,s56,s27,s272] : Row))))) else (if i < 255 then (if i < 253 then (([s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 254 then (([s145,s230,s292,s63,s103,s250,s22,s56,s27,s272] : Row)) else (([s145,s230,s63,s293,s103,s250,s22,s56,s27,s272] : Row)))) else (if i < 256 then (([s145,s230,s63,s103,s250,s22,s296,s56,s27,s272] : Row)) else (if i < 257 then (([s145,s230,s63,s103,s250,s22,s298,s56,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s56,s27,s272,s306] : Row)))))) else (if i < 264 then (if i < 261 then (if i < 259 then (([s230,s63,s152,s103,s250,s22,s172,s56,s27,s272] : Row)) else (if i < 260 then (([s230,s63,s152,s103,s250,s22,s179,s56,s27,s272] : Row)) else (([s230,s63,s152,s197,s103,s250,s22,s56,s27,s272] : Row)))) else (if i < 262 then (([s230,s63,s152,s103,s250,s22,s211,s56,s27,s272] : Row)) else (if i < 263 then (([s230,s63,s152,s103,s250,s22,s56,s27,s272] : Row)) else (([s230,s63,s152,s103,s250,s22,s56,s27,s272,s306] : Row))))) else (if i < 267 then (if i < 265 then (([s143,s230,s64,s103,s250,s22,s85,s56,s27,s272] : Row)) else (if i < 266 then (([s143,s230,s64,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s56,s27,s274] : Row)))) else (if i < 268 then (([s143,s230,s64,s91,s93,s252,s22,s56,s27,s272] : Row)) else (if i < 269 then (([s145,s230,s64,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s230,s64,s150,s91,s93,s250,s22,s56,s27,s272] : Row))))))))) else (if i < 315 then (if i < 292 then (if i < 281 then (if i < 275 then (if i < 272 then (if i < 271 then (([s230,s64,s152,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s230,s64,s91,s93,s250,s22,s56,s27,s165,s272] : Row))) else (if i < 273 then (([s143,s230,s64,s91,s95,s250,s22,s56,s27,s272] : Row)) else (if i < 274 then (([s143,s230,s64,s91,s99,s250,s22,s56,s27,s272] : Row)) else (([s143,s230,s64,s91,s100,s250,s22,s56,s27,s272] : Row))))) else (if i < 278 then (if i < 276 then (([s143,s230,s64,s91,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 277 then (([s143,s230,s64,s91,s250,s22,s112,s56,s27,s272] : Row)) else (([s143,s230,s64,s103,s250,s22,s56,s27,s120,s272] : Row)))) else (if i < 279 then (([s143,s230,s64,s103,s250,s22,s128,s56,s27,s272] : Row)) else (if i < 280 then (([s142,s143,s230,s64,s103,s250,s22,s56,s27,s272] : Row)) else (([s143,s230,s64,s103,s250,s22,s172,s56,s27,s272] : Row)))))) else (if i < 286 then (if i < 283 then (if i < 282 then (([s143,s230,s64,s103,s250,s22,s173,s56,s27,s272] : Row)) else (([s143,s230,s64,s103,s250,s22,s179,s56,s27,s272] : Row))) else (if i < 284 then (([s143,s230,s64,s103,s250,s22,s180,s56,s27,s272] : Row)) else (if i < 285 then (([s143,s230,s64,s197,s103,s250,s22,s56,s27,s272] : Row)) else (([s143,s230,s64,s198,s103,s250,s22,s56,s27,s272] : Row))))) else (if i < 289 then (if i < 287 then (([s143,s230,s64,s103,s250,s22,s211,s56,s27,s272] : Row)) else (if i < 288 then (([s143,s230,s64,s103,s250,s22,s212,s56,s27,s272] : Row)) else (([s143,s230,s64,s103,s250,s22,s56,s27,s272] : Row)))) else (if i < 290 then (([s143,s230,s64,s103,s250,s22,s56,s27,s272,s306] : Row)) else (if i < 291 then (([s230,s66,s91,s93,s250,s22,s85,s56,s27,s272] : Row)) else (([s230,s66,s91,s93,s250,s22,s56,s27,s120,s272] : Row))))))) else (if i < 303 then (if i < 297 then (if i < 294 then (if i < 293 then (([s230,s66,s91,s93,s250,s22,s128,s56,s27,s272] : Row)) else (([s142,s230,s66,s91,s93,s250,s22,s56,s27,s272] : Row))) else (if i < 295 then (([s145,s230,s66,s91,s93,s250,s22,s56,s27,s272] : Row)) else (if i < 296 then (([s230,s66,s91,s93,s250,s22,s172,s56,s27,s272] : Row)) else (([s230,s66,s91,s93,s250,s22,s179,s56,s27,s272] : Row))))) else (if i < 300 then (if i < 298 then (([s230,s66,s91,s197,s93,s250,s22,s56,s27,s272] : Row)) else (if i < 299 then (([s230,s66,s91,s93,s250,s22,s211,s56,s27,s272] : Row)) else (([s230,s66,s91,s93,s250,s22,s56,s27,s272] : Row)))) else (if i < 301 then (([s230,s66,s91,s93,s250,s22,s56,s27,s272,s306] : Row)) else (if i < 302 then (([s145,s230,s67,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s142,s143,s230,s67,s103,s250,s22,s56,s27,s272] : Row)))))) else (if i < 309 then (if i < 306 then (if i < 304 then (([s143,s230,s68,s91,s93,s250,s22,s56,s27,s272] : Row)) else (if i < 305 then (([s145,s230,s91,s93,s250,s75,s22,s56,s27,s272] : Row)) else (([s142,s143,s230,s103,s250,s75,s22,s56,s27,s272] : Row)))) else (if i < 307 then (([s145,s230,s91,s93,s250,s22,s76,s56,s27,s272] : Row)) else (if i < 308 then (([s145,s230,s91,s93,s250,s22,s56,s78,s27,s272] : Row)) else (([s230,s152,s91,s93,s250,s22,s79,s56,s27,s272] : Row))))) else (if i < 312 then (if i < 310 then (([s142,s230,s150,s103,s250,s22,s79,s56,s27,s272] : Row)) else (if i < 311 then (([s230,s152,s91,s99,s250,s22,s85,s56,s27,s272] : Row)) else (([s145,s230,s103,s250,s22,s85,s56,s27,s272,s282] : Row)))) else (if i < 313 then (([s230,s152,s91,s92,s93,s250,s22,s56,s27,s272] : Row)) else (if i < 314 then (([s142,s150,s231,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s230,s152,s242,s91,s93,s250,s22,s56,s27,s272] : Row)))))))) else (if i < 337 then (if i < 326 then (if i < 320 then (if i < 317 then (if i < 316 then (([s142,s230,s150,s91,s98,s250,s22,s56,s27,s272] : Row)) else (([s230,s152,s91,s99,s250,s22,s56,s27,s120,s272] : Row))) else (if i < 318 then (([s230,s152,s91,s99,s250,s22,s56,s27,s122,s272] : Row)) else (if i < 319 then (([s230,s152,s91,s99,s250,s22,s128,s56,s27,s272] : Row)) else (([s230,s152,s91,s99,s250,s22,s130,s56,s27,s272] : Row))))) else (if i < 323 then (if i < 321 then (([s142,s230,s150,s91,s99,s250,s22,s56,s27,s272] : Row)) else (if i < 322 then (([s142,s230,s152,s91,s99,s250,s22,s56,s27,s272] : Row)) else (([s142,s230,s91,s99,s250,s22,s56,s27,s167,s272] : Row)))) else (if i < 324 then (([s145,s230,s148,s91,s99,s250,s22,s56,s27,s272] : Row)) else (if i < 325 then (([s145,s230,s152,s91,s99,s250,s22,s56,s27,s272] : Row)) else (([s145,s230,s91,s99,s250,s264,s22,s56,s27,s272] : Row)))))) else (if i < 331 then (if i < 328 then (if i < 327 then (([s230,s148,s150,s91,s99,s250,s22,s56,s27,s272] : Row)) else (([s230,s148,s152,s91,s99,s250,s22,s56,s27,s272] : Row))) else (if i < 329 then (([s230,s148,s91,s99,s250,s22,s56,s27,s165,s272] : Row)) else (if i < 330 then (([s230,s152,s91,s99,s250,s22,s172,s56,s27,s272] : Row)) else (([s230,s152,s91,s99,s250,s22,s179,s56,s27,s272] : Row))))) else (if i < 334 then (if i < 332 then (([s230,s152,s91,s197,s99,s250,s22,s56,s27,s272] : Row)) else (if i < 333 then (([s230,s152,s91,s201,s99,s250,s22,s56,s27,s272] : Row)) else (([s230,s152,s91,s99,s250,s22,s211,s56,s27,s272] : Row)))) else (if i < 335 then (([s230,s152,s91,s99,s250,s22,s215,s56,s27,s272] : Row)) else (if i < 336 then (([s230,s152,s91,s99,s250,s22,s56,s27,s272] : Row)) else (([s230,s152,s91,s99,s250,s22,s56,s27,s272,s306] : Row))))))) else (if i < 348 then (if i < 342 then (if i < 339 then (if i < 338 then (([s143,s230,s64,s91,s93,s250,s22,s57,s27,s272] : Row)) else (([s143,s230,s64,s91,s93,s250,s22,s59,s27,s272] : Row))) else (if i < 340 then (([s142,s143,s230,s70,s93,s250,s22,s59,s27,s272] : Row)) else (if i < 341 then (([s142,s230,s150,s91,s99,s250,s22,s59,s27,s272] : Row)) else (([s142,s143,s230,s91,s93,s22,s78,s258,s27,s272] : Row))))) else (if i < 345 then (if i < 343 then (([s145,s230,s91,s99,s250,s22,s47,s49,s28,s272] : Row)) else (if i < 344 then (([s142,s143,s230,s107,s250,s22,s47,s49,s28,s272] : Row)) else (([s142,s143,s230,s91,s99,s250,s22,s56,s28,s272] : Row)))) else (if i < 346 then (([s143,s230,s64,s103,s250,s22,s47,s49,s29,s272] : Row)) else (if i < 347 then (([s230,s65,s91,s93,s250,s22,s47,s49,s29,s272] : Row)) else (([s143,s230,s70,s93,s250,s22,s47,s49,s29,s272] : Row)))))) else (if i < 354 then (if i < 351 then (if i < 349 then (([s230,s150,s91,s99,s250,s22,s47,s49,s29,s272] : Row)) else (if i < 350 then (([s143,s230,s91,s99,s250,s22,s47,s49,s30,s272] : Row)) else (([s230,s66,s91,s93,s250,s22,s47,s49,s31,s272] : Row)))) else (if i < 352 then (([s145,s230,s70,s93,s250,s22,s47,s49,s33,s272] : Row)) else (if i < 353 then (([s142,s143,s230,s70,s93,s250,s22,s56,s33,s272] : Row)) else (([s142,s143,s230,s73,s250,s22,s47,s49,s34,s272] : Row))))) else (if i < 357 then (if i < 355 then (([s142,s143,s230,s70,s93,s250,s22,s49,s35,s272] : Row)) else (if i < 356 then (([s142,s230,s150,s91,s99,s250,s22,s49,s35,s272] : Row)) else (([s145,s230,s91,s99,s250,s22,s47,s80,s60,s272] : Row)))) else (if i < 358 then (([s142,s143,s230,s107,s250,s22,s47,s80,s60,s272] : Row)) else (if i < 359 then (([s142,s230,s91,s99,s250,s22,s47,s167,s60,s272] : Row)) else (([s230,s148,s91,s99,s250,s22,s47,s165,s60,s272] : Row))))))))))
def route9 (i : ℕ) := if i < 180 then (if i < 90 then (if i < 45 then (if i < 22 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then ((0x80000 : ℕ)) else ((0x0 : ℕ))) else (if i < 3 then ((0x40 : ℕ)) else (if i < 4 then ((0x0 : ℕ)) else ((0x40 : ℕ))))) else (if i < 8 then (if i < 6 then ((0x0 : ℕ)) else (if i < 7 then ((0x0 : ℕ)) else ((0x40 : ℕ)))) else (if i < 9 then ((0x8024000b500b90 : ℕ)) else (if i < 10 then ((0x800f001a0810d81b280fc810501000 : ℕ)) else ((0x8024401cc01d00 : ℕ)))))) else (if i < 16 then (if i < 13 then (if i < 12 then ((0x8024801c501c901c94 : ℕ)) else ((0xc800c000cc00c402c0 : ℕ))) else (if i < 14 then ((0x180010004d00710045002d0 : ℕ)) else (if i < 15 then ((0xc024c00900 : ℕ)) else ((0x10025000b100910 : ℕ))))) else (if i < 19 then (if i < 17 then ((0x14025400bc0 : ℕ)) else (if i < 18 then ((0x128812800ec0 : ℕ)) else ((0x13080e6c0ea412c00f40 : ℕ)))) else (if i < 20 then ((0xf40134811181b600f4811101340 : ℕ)) else (if i < 21 then ((0x140140810801380 : ℕ)) else ((0x21880e6414401110 : ℕ))))))) else (if i < 33 then (if i < 27 then (if i < 24 then (if i < 23 then ((0x140229814801090 : ℕ)) else ((0x1c02208150010a0 : ℕ))) else (if i < 25 then ((0x12c0258021802790130014401340 : ℕ)) else (if i < 26 then ((0xc024cc1580 : ℕ)) else ((0x25c01ac01290 : ℕ))))) else (if i < 30 then (if i < 28 then ((0x14026001d40 : ℕ)) else (if i < 29 then ((0xea427980eac27901b60 : ℕ)) else ((0x285825d012a0 : ℕ)))) else (if i < 31 then ((0x18028a8271015a0 : ℕ)) else (if i < 32 then ((0x1c0292828e01d60 : ℕ)) else ((0x20026400b90 : ℕ)))))) else (if i < 39 then (if i < 36 then (if i < 34 then ((0x2001a4812801000 : ℕ)) else (if i < 35 then ((0x20026801d00 : ℕ)) else ((0x24005000280051007400290 : ℕ)))) else (if i < 37 then ((0x2c015880900 : ℕ)) else (if i < 38 then ((0x30016080c800c8123a00940 : ℕ)) else ((0x30815c823e008c00980 : ℕ))))) else (if i < 42 then (if i < 40 then ((0x34021c808c009c0 : ℕ)) else (if i < 41 then ((0x38022d80a00 : ℕ)) else ((0x3c00540054122480a80 : ℕ)))) else (if i < 43 then ((0x400094026c00cc00cc127d0098009c0 : ℕ)) else (if i < 44 then ((0x44027000b00 : ℕ)) else ((0x3480c8016480cc0 : ℕ)))))))) else (if i < 67 then (if i < 56 then (if i < 50 then (if i < 47 then (if i < 46 then ((0x3c8054017480d00 : ℕ)) else ((0x17080dc0 : ℕ))) else (if i < 48 then ((0x38816880d50 : ℕ)) else (if i < 49 then ((0x17881540 : ℕ)) else ((0x17c817c0 : ℕ))))) else (if i < 53 then (if i < 51 then ((0x180818000ec0 : ℕ)) else (if i < 52 then ((0xf80184811581ba00f8811501840 : ℕ)) else ((0x18881880 : ℕ)))) else (if i < 54 then ((0x190818c0 : ℕ)) else (if i < 55 then ((0x19481940 : ℕ)) else ((0x248038803c803c00240038003000408081019880348048003080340040008181980 : ℕ)))))) else (if i < 61 then (if i < 58 then (if i < 57 then ((0x19c819c0 : ℕ)) else ((0x40015c026c821c02810160016401642 : ℕ))) else (if i < 59 then ((0x48023a0281823e027d0 : ℕ)) else (if i < 60 then ((0x4c028982510 : ℕ)) else ((0x548054029682960 : ℕ))))) else (if i < 64 then (if i < 62 then ((0x5c005801a880900 : ℕ)) else (if i < 63 then ((0x60005802740 : ℕ)) else ((0x5c0060006020ac81580 : ℕ)))) else (if i < 65 then ((0x68806890648064006800682 : ℕ)) else (if i < 66 then ((0x6c0 : ℕ)) else ((0x6c0 : ℕ))))))) else (if i < 78 then (if i < 72 then (if i < 69 then (if i < 68 then ((0x1ac0 : ℕ)) else ((0x7000b00 : ℕ))) else (if i < 70 then ((0x0 : ℕ)) else (if i < 71 then ((0x128812800ec0 : ℕ)) else ((0x78015880900 : ℕ))))) else (if i < 75 then (if i < 73 then ((0x0 : ℕ)) else (if i < 74 then ((0x11181b601110 : ℕ)) else ((0x0 : ℕ)))) else (if i < 76 then ((0x12a00ec0 : ℕ)) else (if i < 77 then ((0x7c015a0 : ℕ)) else ((0x92007c0 : ℕ)))))) else (if i < 84 then (if i < 81 then (if i < 79 then ((0x14a010a013a0 : ℕ)) else (if i < 80 then ((0x80016a016a1 : ℕ)) else ((0xa200800 : ℕ)))) else (if i < 82 then ((0x0 : ℕ)) else (if i < 83 then ((0xec0 : ℕ)) else ((0x840 : ℕ))))) else (if i < 87 then (if i < 85 then ((0x11981be01bc8 : ℕ)) else (if i < 86 then ((0x0 : ℕ)) else ((0x10d8 : ℕ)))) else (if i < 88 then ((0x1118 : ℕ)) else (if i < 89 then ((0xec0 : ℕ)) else ((0x880 : ℕ))))))))) else (if i < 135 then (if i < 112 then (if i < 101 then (if i < 95 then (if i < 92 then (if i < 91 then ((0x880 : ℕ)) else ((0x0 : ℕ))) else (if i < 93 then ((0xc8808c0 : ℕ)) else (if i < 94 then ((0xe48 : ℕ)) else ((0xec0 : ℕ))))) else (if i < 98 then (if i < 96 then ((0xf00 : ℕ)) else (if i < 97 then ((0xf40 : ℕ)) else ((0xf80 : ℕ)))) else (if i < 99 then ((0x1cc81cc90fc0 : ℕ)) else (if i < 100 then ((0xfc80b50 : ℕ)) else ((0xf48 : ℕ)))))) else (if i < 106 then (if i < 103 then (if i < 102 then ((0xf88 : ℕ)) else ((0xf08 : ℕ))) else (if i < 104 then ((0xfd81c60 : ℕ)) else (if i < 105 then ((0xf58 : ℕ)) else ((0xf18 : ℕ))))) else (if i < 109 then (if i < 107 then ((0x10000b90 : ℕ)) else (if i < 108 then ((0x1d081d091008 : ℕ)) else ((0x1040 : ℕ)))) else (if i < 110 then ((0x10800bc0 : ℕ)) else (if i < 111 then ((0x10c0 : ℕ)) else ((0x1100 : ℕ))))))) else (if i < 123 then (if i < 117 then (if i < 114 then (if i < 113 then ((0x1140 : ℕ)) else ((0x10c8 : ℕ))) else (if i < 115 then ((0x1108 : ℕ)) else (if i < 116 then ((0x1048 : ℕ)) else ((0x1d481d491088 : ℕ))))) else (if i < 120 then (if i < 118 then ((0x1d881d8911800c400640 : ℕ)) else (if i < 119 then ((0x11c0 : ℕ)) else ((0x2358235912000c40 : ℕ)))) else (if i < 121 then ((0x2308230912402a9823202321 : ℕ)) else (if i < 122 then ((0x1280 : ℕ)) else ((0x12c0 : ℕ)))))) else (if i < 129 then (if i < 126 then (if i < 124 then ((0x1300 : ℕ)) else (if i < 125 then ((0x1340 : ℕ)) else ((0x1380 : ℕ)))) else (if i < 127 then ((0x13c00c10 : ℕ)) else (if i < 128 then ((0x260826091400 : ℕ)) else ((0x1440 : ℕ))))) else (if i < 132 then (if i < 130 then ((0x14800bc0 : ℕ)) else (if i < 131 then ((0x14c00c10 : ℕ)) else ((0x150028e028e1 : ℕ)))) else (if i < 133 then ((0x1540 : ℕ)) else (if i < 134 then ((0x15800900 : ℕ)) else ((0x15c00940 : ℕ)))))))) else (if i < 157 then (if i < 146 then (if i < 140 then (if i < 137 then (if i < 136 then ((0x16000980 : ℕ)) else ((0x164009c0 : ℕ))) else (if i < 138 then ((0x16800a00 : ℕ)) else (if i < 139 then ((0x16c00a40 : ℕ)) else ((0x1700 : ℕ))))) else (if i < 143 then (if i < 141 then ((0x1740296029610a80 : ℕ)) else (if i < 142 then ((0x1780 : ℕ)) else ((0x17c0 : ℕ)))) else (if i < 144 then ((0x1800 : ℕ)) else (if i < 145 then ((0x1840 : ℕ)) else ((0x1880 : ℕ)))))) else (if i < 151 then (if i < 148 then (if i < 147 then ((0x18c0 : ℕ)) else ((0x1900 : ℕ))) else (if i < 149 then ((0x1940 : ℕ)) else (if i < 150 then ((0x1990d5001980d510dc00dc119800d000d010a8002900a40 : ℕ)) else ((0x19c0 : ℕ))))) else (if i < 154 then (if i < 152 then ((0x244824491a00 : ℕ)) else (if i < 153 then ((0x268826891a40 : ℕ)) else ((0x274827491a800ac0 : ℕ)))) else (if i < 155 then ((0x1ac0 : ℕ)) else (if i < 156 then ((0x1b00 : ℕ)) else ((0x1b40 : ℕ))))))) else (if i < 168 then (if i < 162 then (if i < 159 then (if i < 158 then ((0x1bc0299029910c50 : ℕ)) else ((0x1c00 : ℕ))) else (if i < 160 then ((0x1c400b40 : ℕ)) else (if i < 161 then ((0x1c800b80 : ℕ)) else ((0x1cc00b50 : ℕ))))) else (if i < 165 then (if i < 163 then ((0x1d000b90 : ℕ)) else (if i < 164 then ((0x1d400bc0 : ℕ)) else ((0x29c029c11d800c400680 : ℕ)))) else (if i < 166 then ((0x1dc00c10 : ℕ)) else (if i < 167 then ((0x1e00 : ℕ)) else ((0x1e402a102a110c50 : ℕ)))))) else (if i < 174 then (if i < 171 then (if i < 169 then ((0x1e800bc0 : ℕ)) else (if i < 170 then ((0x1ec00bc0 : ℕ)) else ((0x1f00 : ℕ)))) else (if i < 172 then ((0x1f402a502a510c50 : ℕ)) else (if i < 173 then ((0x1f80 : ℕ)) else ((0x1fc00900 : ℕ))))) else (if i < 177 then (if i < 175 then ((0x2000 : ℕ)) else (if i < 176 then ((0x2040 : ℕ)) else ((0x2080 : ℕ)))) else (if i < 178 then ((0x20c0 : ℕ)) else (if i < 179 then ((0x1d90d9001d80d910e000e0121000d800d810c5005900c400580 : ℕ)) else ((0x2140 : ℕ)))))))))) else (if i < 270 then (if i < 225 then (if i < 202 then (if i < 191 then (if i < 185 then (if i < 182 then (if i < 181 then ((0x10d8 : ℕ)) else ((0xe6c : ℕ))) else (if i < 183 then ((0x1118 : ℕ)) else (if i < 184 then ((0x2180 : ℕ)) else ((0x1158 : ℕ))))) else (if i < 188 then (if i < 186 then ((0x21c00cc0 : ℕ)) else (if i < 187 then ((0x1058 : ℕ)) else ((0x10281ca0 : ℕ)))) else (if i < 189 then ((0x10a81d60 : ℕ)) else (if i < 190 then ((0x1248236829900d80 : ℕ)) else ((0x1e481f4812182320 : ℕ)))))) else (if i < 196 then (if i < 193 then (if i < 192 then ((0x12201da00d80 : ℕ)) else ((0x11e01ea0 : ℕ))) else (if i < 194 then ((0x220028e0 : ℕ)) else (if i < 195 then ((0x2240296029620d00 : ℕ)) else ((0x22802620 : ℕ))))) else (if i < 199 then (if i < 197 then ((0x22c00d40 : ℕ)) else (if i < 198 then ((0x23002a102a520d80 : ℕ)) else ((0x234029d00d80 : ℕ)))) else (if i < 200 then ((0x0 : ℕ)) else (if i < 201 then ((0xe00 : ℕ)) else ((0x1e081ec8 : ℕ))))))) else (if i < 213 then (if i < 207 then (if i < 204 then (if i < 203 then ((0x0 : ℕ)) else ((0xdc0 : ℕ))) else (if i < 205 then ((0xe00 : ℕ)) else (if i < 206 then ((0x1e20 : ℕ)) else ((0x11981e601e48 : ℕ))))) else (if i < 210 then (if i < 208 then ((0x0 : ℕ)) else (if i < 209 then ((0x0 : ℕ)) else ((0xe80 : ℕ)))) else (if i < 211 then ((0xe90 : ℕ)) else (if i < 212 then ((0x10a81ea0 : ℕ)) else ((0x10a81ee0 : ℕ)))))) else (if i < 219 then (if i < 216 then (if i < 214 then ((0x1f20 : ℕ)) else (if i < 215 then ((0x11981f601f49 : ℕ)) else ((0x1fa0 : ℕ)))) else (if i < 217 then ((0x0 : ℕ)) else (if i < 218 then ((0x0 : ℕ)) else ((0x0 : ℕ))))) else (if i < 222 then (if i < 220 then ((0x0 : ℕ)) else (if i < 221 then ((0x0 : ℕ)) else ((0x1c00 : ℕ)))) else (if i < 223 then ((0x2008 : ℕ)) else (if i < 224 then ((0x0 : ℕ)) else ((0x0 : ℕ)))))))) else (if i < 247 then (if i < 236 then (if i < 230 then (if i < 227 then (if i < 226 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 228 then ((0x0 : ℕ)) else (if i < 229 then ((0x0 : ℕ)) else ((0x0 : ℕ))))) else (if i < 233 then (if i < 231 then ((0x2040 : ℕ)) else (if i < 232 then ((0x0 : ℕ)) else ((0x0 : ℕ)))) else (if i < 234 then ((0x0 : ℕ)) else (if i < 235 then ((0x0 : ℕ)) else ((0x0 : ℕ)))))) else (if i < 241 then (if i < 238 then (if i < 237 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 239 then ((0x0 : ℕ)) else (if i < 240 then ((0x0 : ℕ)) else ((0x0 : ℕ))))) else (if i < 244 then (if i < 242 then ((0x0 : ℕ)) else (if i < 243 then ((0x0 : ℕ)) else ((0x0 : ℕ)))) else (if i < 245 then ((0x0 : ℕ)) else (if i < 246 then ((0x780 : ℕ)) else ((0x7d0 : ℕ))))))) else (if i < 258 then (if i < 252 then (if i < 249 then (if i < 248 then ((0x7d0 : ℕ)) else ((0x7d01fc8 : ℕ))) else (if i < 250 then ((0x860 : ℕ)) else (if i < 251 then ((0x860 : ℕ)) else ((0x88806c008a0 : ℕ))))) else (if i < 255 then (if i < 253 then ((0x2d8109810a810a002d010901088108002c0 : ℕ)) else (if i < 254 then ((0x0 : ℕ)) else ((0x0 : ℕ)))) else (if i < 256 then ((0x0 : ℕ)) else (if i < 257 then ((0x0 : ℕ)) else ((0x0 : ℕ)))))) else (if i < 264 then (if i < 261 then (if i < 259 then ((0x2010 : ℕ)) else (if i < 260 then ((0x2050 : ℕ)) else ((0x2080 : ℕ)))) else (if i < 262 then ((0x20c0 : ℕ)) else (if i < 263 then ((0x3d8120812481210039011801bc0009011c01f80210005c01fc0 : ℕ)) else ((0x2140 : ℕ))))) else (if i < 267 then (if i < 265 then ((0x0 : ℕ)) else (if i < 266 then ((0x1280 : ℕ)) else ((0x12c0 : ℕ)))) else (if i < 268 then ((0x1300 : ℕ)) else (if i < 269 then ((0x1340 : ℕ)) else ((0x1380 : ℕ))))))))) else (if i < 315 then (if i < 292 then (if i < 281 then (if i < 275 then (if i < 272 then (if i < 271 then ((0x13c01dc01dc2 : ℕ)) else ((0x25481400 : ℕ))) else (if i < 273 then ((0x1440 : ℕ)) else (if i < 274 then ((0x14801d40 : ℕ)) else ((0x14c01dc0 : ℕ))))) else (if i < 278 then (if i < 276 then ((0x0 : ℕ)) else (if i < 277 then ((0x29201500 : ℕ)) else ((0x0 : ℕ)))) else (if i < 279 then ((0x0 : ℕ)) else (if i < 280 then ((0x1340 : ℕ)) else ((0x0 : ℕ)))))) else (if i < 286 then (if i < 283 then (if i < 282 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 284 then ((0x0 : ℕ)) else (if i < 285 then ((0x0 : ℕ)) else ((0x0 : ℕ))))) else (if i < 289 then (if i < 287 then ((0x0 : ℕ)) else (if i < 288 then ((0x0 : ℕ)) else ((0x4d8229022001500045014c0140013c000c4 : ℕ)))) else (if i < 290 then ((0x0 : ℕ)) else (if i < 291 then ((0x1540 : ℕ)) else ((0x1780 : ℕ))))))) else (if i < 303 then (if i < 297 then (if i < 294 then (if i < 293 then ((0x17c0 : ℕ)) else ((0x1800 : ℕ))) else (if i < 295 then ((0x1840 : ℕ)) else (if i < 296 then ((0x1880 : ℕ)) else ((0x18c0 : ℕ))))) else (if i < 300 then (if i < 298 then ((0x1900 : ℕ)) else (if i < 299 then ((0x1940 : ℕ)) else ((0x51822d02240174001121742011017001702198016c016c2 : ℕ)))) else (if i < 301 then ((0x19c0 : ℕ)) else (if i < 302 then ((0x24081a00 : ℕ)) else ((0x24881a00 : ℕ)))))) else (if i < 309 then (if i < 306 then (if i < 304 then ((0x26481a40 : ℕ)) else (if i < 305 then ((0x1b00 : ℕ)) else ((0x1b00 : ℕ)))) else (if i < 307 then ((0x1b40 : ℕ)) else (if i < 308 then ((0x1b80 : ℕ)) else ((0x2a901e401e421bc0 : ℕ))))) else (if i < 312 then (if i < 310 then ((0x29a01d901bc0 : ℕ)) else (if i < 311 then ((0x1c00 : ℕ)) else ((0x1b40 : ℕ)))) else (if i < 313 then ((0x1e001ec0 : ℕ)) else (if i < 314 then ((0x1cd01c40 : ℕ)) else ((0x1fc01580 : ℕ)))))))) else (if i < 337 then (if i < 326 then (if i < 320 then (if i < 317 then (if i < 316 then ((0x1d101c80 : ℕ)) else ((0x2000 : ℕ))) else (if i < 318 then ((0x2002 : ℕ)) else (if i < 319 then ((0x2040 : ℕ)) else ((0x2042 : ℕ))))) else (if i < 323 then (if i < 321 then ((0x1d501d40 : ℕ)) else (if i < 322 then ((0x1e10 : ℕ)) else ((0x2a081e501d80 : ℕ)))) else (if i < 324 then ((0x1ed01d40 : ℕ)) else (if i < 325 then ((0x1f90 : ℕ)) else ((0x12921fd0 : ℕ)))))) else (if i < 331 then (if i < 328 then (if i < 327 then ((0x1e901d40 : ℕ)) else ((0x1f10 : ℕ))) else (if i < 329 then ((0x2a4c1f501d80 : ℕ)) else (if i < 330 then ((0x2010 : ℕ)) else ((0x2050 : ℕ))))) else (if i < 334 then (if i < 332 then ((0x2080 : ℕ)) else (if i < 333 then ((0x2082 : ℕ)) else ((0x20c0 : ℕ)))) else (if i < 335 then ((0x20c2 : ℕ)) else (if i < 336 then ((0x558235023001e4002121f4201501e001f0221001d800600 : ℕ)) else ((0x2140 : ℕ))))))) else (if i < 348 then (if i < 342 then (if i < 339 then (if i < 338 then ((0x2180 : ℕ)) else ((0x292029222200 : ℕ))) else (if i < 340 then ((0x25602280 : ℕ)) else (if i < 341 then ((0x2a202a6023402300 : ℕ)) else ((0x23d02380 : ℕ))))) else (if i < 345 then (if i < 343 then ((0x24402400 : ℕ)) else (if i < 344 then ((0x24802400 : ℕ)) else ((0x24802440 : ℕ)))) else (if i < 346 then ((0x2580 : ℕ)) else (if i < 347 then ((0x24cc24c0 : ℕ)) else ((0x25c0 : ℕ)))))) else (if i < 354 then (if i < 351 then (if i < 349 then ((0x26002540 : ℕ)) else (if i < 350 then ((0x26802640 : ℕ)) else ((0x26c826c0 : ℕ)))) else (if i < 352 then ((0x2780 : ℕ)) else (if i < 353 then ((0x2780 : ℕ)) else ((0x280027c0 : ℕ))))) else (if i < 357 then (if i < 355 then ((0x2840 : ℕ)) else (if i < 356 then ((0x290028c0 : ℕ)) else ((0x2988298029c0 : ℕ)))) else (if i < 358 then ((0x2a802a002a042980 : ℕ)) else (if i < 359 then ((0x2a082a0029c0 : ℕ)) else ((0x2a4c2a4029c0 : ℕ))))))))))
def stored8 (i : ℕ) := if i < 85 then (if i < 42 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then (([s0,s230,s66,s103,s250,s22,s56,s27,s272] : Row)) else (([s0,s230,s152,s107,s250,s22,s56,s27,s272] : Row))) else (if i < 3 then (([s1,s145,s230,s107,s250,s22,s56,s27,s272] : Row)) else (if i < 4 then (([s2,s230,s65,s103,s250,s22,s56,s27,s272] : Row)) else (([s2,s143,s230,s73,s250,s22,s56,s27,s272] : Row))))) else (if i < 7 then (if i < 6 then (([s2,s230,s150,s107,s250,s22,s56,s27,s272] : Row)) else (([s2,s143,s230,s63,s250,s26,s56,s27,s272] : Row))) else (if i < 8 then (([s2,s143,s230,s63,s250,s114,s59,s27,s272] : Row)) else (if i < 9 then (([s3,s143,s230,s107,s250,s22,s56,s27,s272] : Row)) else (([s5,s230,s63,s12,s250,s22,s56,s27,s272] : Row)))))) else (if i < 15 then (if i < 12 then (if i < 11 then (([s5,s230,s73,s250,s22,s47,s49,s27,s272] : Row)) else (([s5,s230,s63,s103,s250,s22,s56,s27,s272] : Row))) else (if i < 13 then (([s5,s230,s63,s103,s250,s22,s56,s27,s276] : Row)) else (if i < 14 then (([s5,s230,s63,s105,s250,s22,s56,s27,s272] : Row)) else (([s5,s230,s63,s107,s250,s22,s56,s27,s272] : Row))))) else (if i < 18 then (if i < 16 then (([s5,s230,s63,s250,s22,s114,s56,s27,s272] : Row)) else (if i < 17 then (([s5,s230,s66,s103,s250,s22,s56,s27,s272] : Row)) else (([s5,s230,s70,s93,s250,s22,s56,s27,s272] : Row)))) else (if i < 19 then (([s5,s230,s63,s103,s250,s24,s56,s27,s272] : Row)) else (if i < 20 then (([s5,s230,s63,s93,s250,s25,s56,s27,s272] : Row)) else (([s5,s230,s63,s250,s26,s47,s49,s27,s272] : Row))))))) else (if i < 31 then (if i < 26 then (if i < 23 then (if i < 22 then (([s5,s230,s63,s250,s114,s47,s55,s27,s272] : Row)) else (([s6,s230,s107,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 24 then (([s6,s230,s63,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 25 then (([s6,s230,s91,s99,s250,s22,s56,s27,s272] : Row)) else (([s7,s63,s103,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 28 then (if i < 27 then (([s7,s91,s99,s250,s22,s47,s49,s27,s272] : Row)) else (([s145,s230,s8,s103,s250,s22,s56,s27,s272] : Row))) else (if i < 29 then (([s230,s63,s11,s93,s250,s22,s56,s27,s272] : Row)) else (if i < 30 then (([s230,s63,s13,s250,s22,s47,s49,s27,s272] : Row)) else (([s16,s230,s63,s103,s250,s22,s56,s27,s272] : Row)))))) else (if i < 36 then (if i < 33 then (if i < 32 then (([s145,s230,s63,s21,s250,s22,s56,s27,s272] : Row)) else (([s145,s230,s63,s250,s22,s26,s56,s27,s272] : Row))) else (if i < 34 then (([s145,s230,s63,s103,s250,s22,s39,s27,s272] : Row)) else (if i < 35 then (([s145,s230,s63,s103,s250,s22,s45,s27,s272] : Row)) else (([s230,s63,s105,s253,s22,s47,s49,s27,s272] : Row))))) else (if i < 39 then (if i < 37 then (([s230,s66,s103,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 38 then (([s230,s66,s103,s250,s22,s47,s49,s27,s276] : Row)) else (([s230,s66,s103,s253,s22,s47,s49,s27,s272] : Row)))) else (if i < 40 then (([s230,s66,s105,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 41 then (([s230,s66,s107,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s66,s109,s250,s22,s47,s49,s27,s272] : Row)))))))) else (if i < 63 then (if i < 52 then (if i < 47 then (if i < 44 then (if i < 43 then (([s230,s66,s250,s22,s114,s47,s49,s27,s272] : Row)) else (([s230,s69,s103,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 45 then (([s230,s72,s93,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 46 then (([s152,s231,s103,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s152,s106,s250,s22,s47,s49,s27,s272] : Row))))) else (if i < 49 then (if i < 48 then (([s230,s152,s107,s250,s22,s47,s49,s27,s272] : Row)) else (([s230,s157,s107,s250,s22,s47,s49,s27,s272] : Row))) else (if i < 50 then (([s230,s107,s250,s22,s47,s49,s27,s168,s272] : Row)) else (if i < 51 then (([s230,s63,s103,s250,s22,s47,s52,s27,s276] : Row)) else (([s230,s66,s103,s250,s22,s47,s52,s27,s272] : Row)))))) else (if i < 57 then (if i < 54 then (if i < 53 then (([s230,s66,s103,s250,s22,s47,s55,s27,s272] : Row)) else (([s145,s230,s73,s250,s22,s47,s55,s27,s272] : Row))) else (if i < 55 then (([s230,s152,s107,s250,s22,s47,s55,s27,s272] : Row)) else (if i < 56 then (([s230,s66,s103,s250,s22,s47,s56,s27,s272] : Row)) else (([s230,s152,s107,s250,s22,s47,s56,s27,s272] : Row))))) else (if i < 60 then (if i < 58 then (([s63,s103,s250,s22,s47,s162,s235,s27,s272] : Row)) else (if i < 59 then (([s145,s230,s103,s22,s47,s77,s257,s27,s272] : Row)) else (([s145,s230,s63,s103,s250,s22,s56,s27,s272] : Row)))) else (if i < 61 then (([s145,s230,s63,s103,s250,s22,s56,s27,s273] : Row)) else (if i < 62 then (([s145,s230,s63,s103,s250,s22,s56,s27,s274] : Row)) else (([s145,s230,s63,s103,s250,s22,s56,s27,s276] : Row))))))) else (if i < 74 then (if i < 68 then (if i < 65 then (if i < 64 then (([s145,s230,s63,s103,s250,s22,s56,s27,s277] : Row)) else (([s146,s230,s63,s103,s250,s22,s56,s27,s272] : Row))) else (if i < 66 then (([s230,s63,s151,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 67 then (([s230,s63,s152,s103,s250,s22,s56,s27,s272] : Row)) else (([s230,s63,s154,s103,s250,s22,s56,s27,s272] : Row))))) else (if i < 71 then (if i < 69 then (([s230,s63,s156,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 70 then (([s230,s63,s103,s159,s250,s22,s56,s27,s272] : Row)) else (([s230,s63,s103,s250,s22,s56,s27,s168,s272] : Row)))) else (if i < 72 then (([s230,s63,s152,s107,s250,s22,s56,s27,s272] : Row)) else (if i < 73 then (([s230,s63,s107,s250,s22,s56,s27,s166,s272] : Row)) else (([s230,s63,s250,s22,s114,s56,s27,s166,s272] : Row)))))) else (if i < 79 then (if i < 76 then (if i < 75 then (([s143,s230,s64,s103,s250,s22,s56,s27,s272] : Row)) else (([s143,s230,s64,s103,s250,s22,s56,s27,s274] : Row))) else (if i < 77 then (([s143,s230,s64,s103,s252,s22,s56,s27,s272] : Row)) else (if i < 78 then (([s145,s230,s64,s103,s250,s22,s56,s27,s272] : Row)) else (([s230,s64,s150,s103,s250,s22,s56,s27,s272] : Row))))) else (if i < 82 then (if i < 80 then (([s230,s64,s152,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 81 then (([s230,s64,s103,s250,s22,s56,s27,s165,s272] : Row)) else (([s143,s230,s64,s104,s250,s22,s56,s27,s272] : Row)))) else (if i < 83 then (([s143,s230,s64,s107,s250,s22,s56,s27,s272] : Row)) else (if i < 84 then (([s143,s230,s64,s108,s250,s22,s56,s27,s272] : Row)) else (([s143,s230,s64,s250,s22,s114,s56,s27,s272] : Row))))))))) else (if i < 128 then (if i < 106 then (if i < 95 then (if i < 90 then (if i < 87 then (if i < 86 then (([s230,s66,s103,s250,s22,s85,s56,s27,s272] : Row)) else (([s230,s66,s91,s93,s250,s22,s56,s27,s272] : Row))) else (if i < 88 then (([s230,s66,s91,s93,s250,s22,s56,s27,s276] : Row)) else (if i < 89 then (([s230,s66,s91,s93,s253,s22,s56,s27,s272] : Row)) else (([s230,s66,s91,s96,s250,s22,s56,s27,s272] : Row))))) else (if i < 92 then (if i < 91 then (([s230,s66,s91,s99,s250,s22,s56,s27,s272] : Row)) else (([s230,s66,s91,s101,s250,s22,s56,s27,s272] : Row))) else (if i < 93 then (([s230,s66,s91,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 94 then (([s230,s66,s91,s250,s22,s112,s56,s27,s272] : Row)) else (([s230,s66,s103,s250,s22,s56,s27,s120,s272] : Row)))))) else (if i < 100 then (if i < 97 then (if i < 96 then (([s230,s66,s103,s250,s22,s128,s56,s27,s272] : Row)) else (([s142,s230,s66,s103,s250,s22,s56,s27,s272] : Row))) else (if i < 98 then (([s145,s230,s66,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 99 then (([s230,s66,s103,s250,s22,s172,s56,s27,s272] : Row)) else (([s230,s66,s103,s250,s22,s179,s56,s27,s272] : Row))))) else (if i < 103 then (if i < 101 then (([s230,s66,s197,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 102 then (([s230,s66,s103,s250,s22,s211,s56,s27,s272] : Row)) else (([s230,s66,s103,s250,s22,s56,s27,s272] : Row)))) else (if i < 104 then (([s230,s66,s103,s250,s22,s56,s27,s272,s306] : Row)) else (if i < 105 then (([s145,s230,s67,s103,s250,s22,s56,s27,s272] : Row)) else (([s143,s230,s68,s103,s250,s22,s56,s27,s272] : Row))))))) else (if i < 117 then (if i < 111 then (if i < 108 then (if i < 107 then (([s230,s69,s91,s93,s250,s22,s56,s27,s272] : Row)) else (([s143,s230,s71,s93,s250,s22,s56,s27,s272] : Row))) else (if i < 109 then (([s145,s230,s103,s250,s75,s22,s56,s27,s272] : Row)) else (if i < 110 then (([s145,s230,s103,s250,s22,s76,s56,s27,s272] : Row)) else (([s145,s230,s103,s250,s22,s56,s78,s27,s272] : Row))))) else (if i < 114 then (if i < 112 then (([s230,s152,s103,s250,s22,s79,s56,s27,s272] : Row)) else (if i < 113 then (([s230,s152,s107,s250,s22,s85,s56,s27,s272] : Row)) else (([s152,s231,s91,s93,s250,s22,s56,s27,s272] : Row)))) else (if i < 115 then (([s230,s152,s91,s98,s250,s22,s56,s27,s272] : Row)) else (if i < 116 then (([s145,s230,s91,s99,s251,s22,s56,s27,s272] : Row)) else (([s146,s230,s91,s99,s250,s22,s56,s27,s272] : Row)))))) else (if i < 122 then (if i < 119 then (if i < 118 then (([s230,s152,s91,s99,s250,s22,s56,s27,s272] : Row)) else (([s230,s91,s99,s250,s22,s56,s27,s168,s272] : Row))) else (if i < 120 then (([s230,s152,s91,s100,s250,s22,s56,s27,s272] : Row)) else (if i < 121 then (([s230,s152,s91,s107,s250,s22,s56,s27,s272] : Row)) else (([s230,s152,s91,s250,s22,s113,s56,s27,s272] : Row))))) else (if i < 125 then (if i < 123 then (([s230,s152,s92,s99,s250,s22,s56,s27,s272] : Row)) else (if i < 124 then (([s230,s152,s92,s103,s250,s22,s56,s27,s272] : Row)) else (([s230,s152,s92,s107,s250,s22,s56,s27,s272] : Row)))) else (if i < 126 then (([s230,s152,s92,s250,s22,s112,s56,s27,s272] : Row)) else (if i < 127 then (([s230,s152,s103,s107,s250,s22,s56,s27,s272] : Row)) else (([s230,s152,s242,s103,s250,s22,s56,s27,s272] : Row)))))))) else (if i < 149 then (if i < 138 then (if i < 133 then (if i < 130 then (if i < 129 then (([s230,s152,s107,s250,s22,s56,s27,s120,s272] : Row)) else (([s230,s152,s107,s250,s22,s128,s56,s27,s272] : Row))) else (if i < 131 then (([s230,s152,s197,s107,s250,s22,s56,s27,s272] : Row)) else (if i < 132 then (([s230,s152,s107,s250,s22,s211,s56,s27,s272] : Row)) else (([s230,s152,s107,s250,s22,s56,s27,s272] : Row))))) else (if i < 135 then (if i < 134 then (([s230,s152,s107,s250,s22,s56,s27,s272,s306] : Row)) else (([s143,s230,s64,s103,s250,s22,s57,s27,s272] : Row))) else (if i < 136 then (([s230,s66,s91,s93,s250,s22,s58,s27,s272] : Row)) else (if i < 137 then (([s143,s230,s64,s103,s250,s22,s59,s27,s272] : Row)) else (([s230,s66,s91,s93,s250,s22,s59,s27,s272] : Row)))))) else (if i < 143 then (if i < 140 then (if i < 139 then (([s145,s230,s70,s93,s250,s22,s59,s27,s272] : Row)) else (([s142,s143,s230,s73,s250,s22,s59,s27,s272] : Row))) else (if i < 141 then (([s230,s152,s91,s99,s250,s22,s59,s27,s272] : Row)) else (if i < 142 then (([s142,s230,s150,s107,s250,s22,s59,s27,s272] : Row)) else (([s145,s230,s91,s93,s22,s78,s258,s27,s272] : Row))))) else (if i < 146 then (if i < 144 then (([s145,s91,s93,s250,s22,s236,s78,s27,s272] : Row)) else (if i < 145 then (([s145,s230,s107,s250,s22,s47,s49,s28,s272] : Row)) else (([s145,s230,s91,s99,s250,s22,s56,s28,s272] : Row)))) else (if i < 147 then (([s142,s143,s230,s107,s250,s22,s56,s28,s272] : Row)) else (if i < 148 then (([s230,s65,s103,s250,s22,s47,s49,s29,s272] : Row)) else (([s143,s230,s73,s250,s22,s47,s49,s29,s272] : Row))))))) else (if i < 160 then (if i < 154 then (if i < 151 then (if i < 150 then (([s230,s150,s107,s250,s22,s47,s49,s29,s272] : Row)) else (([s143,s230,s64,s103,s250,s22,s56,s29,s272] : Row))) else (if i < 152 then (([s143,s230,s70,s93,s250,s22,s56,s29,s272] : Row)) else (if i < 153 then (([s230,s150,s91,s99,s250,s22,s56,s29,s272] : Row)) else (([s143,s230,s107,s250,s22,s47,s49,s30,s272] : Row))))) else (if i < 157 then (if i < 155 then (([s143,s230,s91,s99,s250,s22,s56,s30,s272] : Row)) else (if i < 156 then (([s230,s66,s103,s250,s22,s47,s49,s31,s272] : Row)) else (([s230,s70,s93,s250,s22,s47,s49,s31,s272] : Row)))) else (if i < 158 then (([s230,s91,s99,s250,s22,s47,s49,s32,s272] : Row)) else (if i < 159 then (([s145,s230,s70,s93,s250,s22,s56,s33,s272] : Row)) else (([s145,s230,s73,s250,s22,s47,s49,s34,s272] : Row)))))) else (if i < 165 then (if i < 162 then (if i < 161 then (([s142,s143,s230,s73,s250,s22,s56,s34,s272] : Row)) else (([s145,s230,s70,s93,s250,s22,s49,s35,s272] : Row))) else (if i < 163 then (([s142,s143,s230,s73,s250,s22,s49,s35,s272] : Row)) else (if i < 164 then (([s230,s152,s91,s99,s250,s22,s49,s35,s272] : Row)) else (([s142,s230,s150,s107,s250,s22,s49,s35,s272] : Row))))) else (if i < 168 then (if i < 166 then (([s142,s230,s150,s91,s99,s250,s22,s36,s272] : Row)) else (if i < 167 then (([s145,s230,s107,s250,s22,s47,s80,s60,s272] : Row)) else (([s230,s91,s99,s250,s22,s47,s168,s60,s272] : Row)))) else (if i < 169 then (([s142,s230,s107,s250,s22,s47,s167,s60,s272] : Row)) else (if i < 170 then (([s230,s148,s107,s250,s22,s47,s165,s60,s272] : Row)) else (([s142,s143,s230,s107,s250,s22,s80,s62,s272] : Row)))))))))
def route8 (i : ℕ) := if i < 85 then (if i < 42 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 3 then ((0x78005100550 : ℕ)) else (if i < 4 then ((0x7c002c0 : ℕ)) else ((0x80004d002d0 : ℕ))))) else (if i < 7 then (if i < 6 then ((0x8400580 : ℕ)) else ((0xa68095002e0 : ℕ))) else (if i < 8 then ((0xaa80aa005a0 : ℕ)) else (if i < 9 then ((0x8800550 : ℕ)) else ((0x400000005002000010 : ℕ)))))) else (if i < 15 then (if i < 12 then (if i < 11 then ((0x8c00240 : ℕ)) else ((0x2c802c0 : ℕ))) else (if i < 13 then ((0x348028807600300 : ℕ)) else (if i < 14 then ((0x64802800380 : ℕ)) else ((0x6d803c0 : ℕ))))) else (if i < 18 then (if i < 16 then ((0x8006880440 : ℕ)) else (if i < 17 then ((0x300090006400a1003400380 : ℕ)) else ((0x94004c0 : ℕ)))) else (if i < 19 then ((0x7600a1807680a10 : ℕ)) else (if i < 20 then ((0xa580810 : ℕ)) else ((0x400ad808d0 : ℕ))))))) else (if i < 31 then (if i < 26 then (if i < 23 then (if i < 22 then ((0x800b680b20 : ℕ)) else ((0xc00980 : ℕ))) else (if i < 24 then ((0xc0048802c0 : ℕ)) else (if i < 25 then ((0xc009c0 : ℕ)) else ((0x188018901400100 : ℕ))))) else (if i < 28 then (if i < 27 then ((0x1c001c101800100 : ℕ)) else ((0x0 : ℕ))) else (if i < 29 then ((0x4c0 : ℕ)) else (if i < 30 then ((0x2000240 : ℕ)) else ((0x2c802c0 : ℕ)))))) else (if i < 36 then (if i < 33 then (if i < 32 then ((0x2e0 : ℕ)) else ((0x3e0 : ℕ))) else (if i < 34 then ((0x0 : ℕ)) else (if i < 35 then ((0x0 : ℕ)) else ((0x280 : ℕ))))) else (if i < 39 then (if i < 37 then ((0x2c0 : ℕ)) else (if i < 38 then ((0x300 : ℕ)) else ((0x340 : ℕ)))) else (if i < 40 then ((0x380 : ℕ)) else (if i < 41 then ((0x3c0 : ℕ)) else ((0x400 : ℕ)))))))) else (if i < 63 then (if i < 52 then (if i < 47 then (if i < 44 then (if i < 43 then ((0x4400b200b21 : ℕ)) else ((0x9c809c90480 : ℕ))) else (if i < 45 then ((0x4c0 : ℕ)) else (if i < 46 then ((0x500 : ℕ)) else ((0x540 : ℕ))))) else (if i < 49 then (if i < 48 then ((0x580 : ℕ)) else ((0x5c0 : ℕ))) else (if i < 50 then ((0xb800b8106000100 : ℕ)) else (if i < 51 then ((0x288 : ℕ)) else ((0x640 : ℕ)))))) else (if i < 57 then (if i < 54 then (if i < 53 then ((0x6800b20 : ℕ)) else ((0x6c0 : ℕ))) else (if i < 55 then ((0x7000b90 : ℕ)) else (if i < 56 then ((0x0 : ℕ)) else ((0x0 : ℕ))))) else (if i < 60 then (if i < 58 then ((0x0 : ℕ)) else (if i < 59 then ((0x0 : ℕ)) else ((0x0 : ℕ)))) else (if i < 61 then ((0x0 : ℕ)) else (if i < 62 then ((0x0 : ℕ)) else ((0x0 : ℕ))))))) else (if i < 74 then (if i < 68 then (if i < 65 then (if i < 64 then ((0x518 : ℕ)) else ((0x550 : ℕ))) else (if i < 66 then ((0x0 : ℕ)) else (if i < 67 then ((0x580 : ℕ)) else ((0x0 : ℕ))))) else (if i < 71 then (if i < 69 then ((0x0 : ℕ)) else (if i < 70 then ((0x0 : ℕ)) else ((0x60806000140 : ℕ)))) else (if i < 72 then ((0x0 : ℕ)) else (if i < 73 then ((0x7180600 : ℕ)) else ((0x7080bd80720 : ℕ)))))) else (if i < 79 then (if i < 76 then (if i < 75 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 77 then ((0x0 : ℕ)) else (if i < 78 then ((0x0 : ℕ)) else ((0x0 : ℕ))))) else (if i < 82 then (if i < 80 then ((0x5d0 : ℕ)) else (if i < 81 then ((0x848 : ℕ)) else ((0x0 : ℕ)))) else (if i < 83 then ((0x580 : ℕ)) else (if i < 84 then ((0x5d0 : ℕ)) else ((0xaa0 : ℕ))))))))) else (if i < 128 then (if i < 106 then (if i < 95 then (if i < 90 then (if i < 87 then (if i < 86 then ((0x0 : ℕ)) else ((0x2c0 : ℕ))) else (if i < 88 then ((0x300 : ℕ)) else (if i < 89 then ((0x340 : ℕ)) else ((0x380 : ℕ))))) else (if i < 92 then (if i < 91 then ((0x3c0 : ℕ)) else ((0x400 : ℕ))) else (if i < 93 then ((0x0 : ℕ)) else (if i < 94 then ((0xb600440 : ℕ)) else ((0x0 : ℕ)))))) else (if i < 100 then (if i < 97 then (if i < 96 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 98 then ((0x0 : ℕ)) else (if i < 99 then ((0x0 : ℕ)) else ((0x0 : ℕ))))) else (if i < 103 then (if i < 101 then ((0x0 : ℕ)) else (if i < 102 then ((0x0 : ℕ)) else ((0x5806d00680044000100400 : ℕ)))) else (if i < 104 then ((0x0 : ℕ)) else (if i < 105 then ((0x788 : ℕ)) else ((0x888 : ℕ))))))) else (if i < 117 then (if i < 111 then (if i < 108 then (if i < 107 then ((0x9880480 : ℕ)) else ((0x0 : ℕ))) else (if i < 109 then ((0x0 : ℕ)) else (if i < 110 then ((0x0 : ℕ)) else ((0x0 : ℕ))))) else (if i < 114 then (if i < 112 then ((0xbd00610 : ℕ)) else (if i < 113 then ((0x0 : ℕ)) else ((0x500 : ℕ)))) else (if i < 115 then ((0x540 : ℕ)) else (if i < 116 then ((0x510 : ℕ)) else ((0x550 : ℕ)))))) else (if i < 122 then (if i < 119 then (if i < 118 then ((0x580 : ℕ)) else ((0xb8806000180 : ℕ))) else (if i < 120 then ((0x5d0 : ℕ)) else (if i < 121 then ((0x0 : ℕ)) else ((0xc100610 : ℕ))))) else (if i < 125 then (if i < 123 then ((0x580 : ℕ)) else (if i < 124 then ((0x580 : ℕ)) else ((0x0 : ℕ)))) else (if i < 126 then ((0xc500610 : ℕ)) else (if i < 127 then ((0x0 : ℕ)) else ((0x2c0 : ℕ)))))))) else (if i < 149 then (if i < 138 then (if i < 133 then (if i < 130 then (if i < 129 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 131 then ((0x0 : ℕ)) else (if i < 132 then ((0x0 : ℕ)) else ((0x9807100700061000d0060000c0 : ℕ))))) else (if i < 135 then (if i < 134 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 136 then ((0x640 : ℕ)) else (if i < 137 then ((0xaa0 : ℕ)) else ((0xb600b620680 : ℕ)))))) else (if i < 143 then (if i < 140 then (if i < 139 then ((0x860 : ℕ)) else ((0x6c0 : ℕ))) else (if i < 141 then ((0xc100c520700 : ℕ)) else (if i < 142 then ((0xba00700 : ℕ)) else ((0x740 : ℕ))))) else (if i < 146 then (if i < 144 then ((0x750 : ℕ)) else (if i < 145 then ((0x780 : ℕ)) else ((0x780 : ℕ)))) else (if i < 147 then ((0x780 : ℕ)) else (if i < 148 then ((0x7c0 : ℕ)) else ((0x800 : ℕ))))))) else (if i < 160 then (if i < 154 then (if i < 151 then (if i < 150 then ((0x840 : ℕ)) else ((0x0 : ℕ))) else (if i < 152 then ((0x0 : ℕ)) else (if i < 153 then ((0x840 : ℕ)) else ((0x880 : ℕ))))) else (if i < 157 then (if i < 155 then ((0x880 : ℕ)) else (if i < 156 then ((0x900 : ℕ)) else ((0x940 : ℕ)))) else (if i < 158 then ((0x9c00980 : ℕ)) else (if i < 159 then ((0x0 : ℕ)) else ((0xa00 : ℕ)))))) else (if i < 165 then (if i < 162 then (if i < 161 then ((0xa00 : ℕ)) else ((0x0 : ℕ))) else (if i < 163 then ((0xa40 : ℕ)) else (if i < 164 then ((0xa80 : ℕ)) else ((0xa80 : ℕ))))) else (if i < 168 then (if i < 166 then ((0xb400b00 : ℕ)) else (if i < 167 then ((0xbc00b80 : ℕ)) else ((0xb880b8001c0 : ℕ)))) else (if i < 169 then ((0xc000b80 : ℕ)) else (if i < 170 then ((0xc400b80 : ℕ)) else ((0xc000c040bc0 : ℕ)))))))))
def stored7 (i : ℕ) := if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then (([s5,s230,s73,s250,s22,s56,s27,s272] : Row)) else (if i < 2 then (([s5,s230,s63,s250,s26,s56,s27,s272] : Row)) else (([s5,s230,s63,s250,s114,s59,s27,s272] : Row)))) else (if i < 4 then (([s6,s230,s107,s250,s22,s56,s27,s272] : Row)) else (if i < 5 then (([s7,s107,s250,s22,s47,s49,s27,s272] : Row)) else (([s7,s63,s103,s250,s22,s56,s27,s272] : Row))))) else (if i < 9 then (if i < 7 then (([s7,s91,s99,s250,s22,s56,s27,s272] : Row)) else (if i < 8 then (([s7,s91,s99,s250,s22,s47,s60,s272] : Row)) else (([s230,s63,s13,s250,s22,s56,s27,s272] : Row)))) else (if i < 10 then (([s230,s74,s250,s22,s47,s49,s27,s272] : Row)) else (if i < 11 then (([s230,s63,s105,s253,s22,s56,s27,s272] : Row)) else (([s230,s66,s103,s250,s22,s56,s27,s272] : Row)))))) else (if i < 18 then (if i < 15 then (if i < 13 then (([s230,s66,s103,s250,s22,s56,s27,s276] : Row)) else (if i < 14 then (([s230,s66,s103,s253,s22,s56,s27,s272] : Row)) else (([s230,s66,s105,s250,s22,s56,s27,s272] : Row)))) else (if i < 16 then (([s230,s66,s107,s250,s22,s56,s27,s272] : Row)) else (if i < 17 then (([s230,s66,s109,s250,s22,s56,s27,s272] : Row)) else (([s230,s66,s250,s22,s114,s56,s27,s272] : Row))))) else (if i < 21 then (if i < 19 then (([s230,s69,s103,s250,s22,s56,s27,s272] : Row)) else (if i < 20 then (([s230,s72,s93,s250,s22,s56,s27,s272] : Row)) else (([s152,s231,s103,s250,s22,s56,s27,s272] : Row)))) else (if i < 23 then (if i < 22 then (([s230,s152,s106,s250,s22,s56,s27,s272] : Row)) else (([s230,s152,s107,s250,s22,s56,s27,s272] : Row))) else (if i < 24 then (([s230,s157,s107,s250,s22,s56,s27,s272] : Row)) else (([s230,s107,s250,s22,s56,s27,s168,s272] : Row))))))) else (if i < 37 then (if i < 31 then (if i < 28 then (if i < 26 then (([s230,s66,s103,s250,s22,s58,s27,s272] : Row)) else (if i < 27 then (([s230,s66,s103,s250,s22,s59,s27,s272] : Row)) else (([s145,s230,s73,s250,s22,s59,s27,s272] : Row)))) else (if i < 29 then (([s230,s152,s107,s250,s22,s59,s27,s272] : Row)) else (if i < 30 then (([s145,s230,s103,s22,s78,s258,s27,s272] : Row)) else (([s145,s230,s107,s250,s22,s56,s28,s272] : Row))))) else (if i < 34 then (if i < 32 then (([s230,s65,s103,s250,s22,s56,s29,s272] : Row)) else (if i < 33 then (([s143,s230,s73,s250,s22,s56,s29,s272] : Row)) else (([s230,s150,s107,s250,s22,s56,s29,s272] : Row)))) else (if i < 35 then (([s143,s230,s107,s250,s22,s56,s30,s272] : Row)) else (if i < 36 then (([s230,s73,s250,s22,s47,s49,s31,s272] : Row)) else (([s230,s66,s103,s250,s22,s56,s31,s272] : Row)))))) else (if i < 43 then (if i < 40 then (if i < 38 then (([s230,s70,s93,s250,s22,s56,s31,s272] : Row)) else (if i < 39 then (([s230,s107,s250,s22,s47,s49,s32,s272] : Row)) else (([s230,s91,s99,s250,s22,s56,s32,s272] : Row)))) else (if i < 41 then (([s145,s230,s73,s250,s22,s56,s34,s272] : Row)) else (if i < 42 then (([s145,s230,s73,s250,s22,s49,s35,s272] : Row)) else (([s230,s152,s107,s250,s22,s49,s35,s272] : Row))))) else (if i < 46 then (if i < 44 then (([s142,s143,s230,s73,s250,s22,s36,s272] : Row)) else (if i < 45 then (([s230,s152,s91,s99,s250,s22,s36,s272] : Row)) else (([s142,s230,s150,s107,s250,s22,s36,s272] : Row)))) else (if i < 48 then (if i < 47 then (([s230,s107,s250,s22,s47,s168,s60,s272] : Row)) else (([s145,s230,s107,s250,s22,s80,s62,s272] : Row))) else (if i < 49 then (([s142,s230,s107,s250,s22,s167,s62,s272] : Row)) else (([s230,s148,s107,s250,s22,s165,s62,s272] : Row)))))))
def route7 (i : ℕ) := if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then ((0xc00080 : ℕ)) else (if i < 2 then ((0x15800d0 : ℕ)) else ((0x1a801a0 : ℕ)))) else (if i < 4 then ((0x100 : ℕ)) else (if i < 5 then ((0x4000410000 : ℕ)) else ((0x80000 : ℕ))))) else (if i < 9 then (if i < 7 then ((0x480000 : ℕ)) else (if i < 8 then ((0x480040 : ℕ)) else ((0x80 : ℕ)))) else (if i < 10 then ((0x80 : ℕ)) else (if i < 11 then ((0x0 : ℕ)) else ((0x0 : ℕ)))))) else (if i < 18 then (if i < 15 then (if i < 13 then ((0x0 : ℕ)) else (if i < 14 then ((0x0 : ℕ)) else ((0x0 : ℕ)))) else (if i < 16 then ((0x0 : ℕ)) else (if i < 17 then ((0x0 : ℕ)) else ((0x1a0 : ℕ))))) else (if i < 21 then (if i < 19 then ((0x108 : ℕ)) else (if i < 20 then ((0x0 : ℕ)) else ((0x0 : ℕ)))) else (if i < 23 then (if i < 22 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 24 then ((0x0 : ℕ)) else ((0x1c00000 : ℕ))))))) else (if i < 37 then (if i < 31 then (if i < 28 then (if i < 26 then ((0x0 : ℕ)) else (if i < 27 then ((0x1a0 : ℕ)) else ((0x0 : ℕ)))) else (if i < 29 then ((0x1d0 : ℕ)) else (if i < 30 then ((0x0 : ℕ)) else ((0x0 : ℕ))))) else (if i < 34 then (if i < 32 then ((0x0 : ℕ)) else (if i < 33 then ((0x0 : ℕ)) else ((0x0 : ℕ)))) else (if i < 35 then ((0x0 : ℕ)) else (if i < 36 then ((0xc0 : ℕ)) else ((0x0 : ℕ)))))) else (if i < 43 then (if i < 40 then (if i < 38 then ((0x0 : ℕ)) else (if i < 39 then ((0x100 : ℕ)) else ((0x100 : ℕ)))) else (if i < 41 then ((0x0 : ℕ)) else (if i < 42 then ((0x0 : ℕ)) else ((0x0 : ℕ))))) else (if i < 46 then (if i < 44 then ((0x140 : ℕ)) else (if i < 45 then ((0x180 : ℕ)) else ((0x180 : ℕ)))) else (if i < 48 then (if i < 47 then ((0x1c00040 : ℕ)) else ((0x1c0 : ℕ))) else (if i < 49 then ((0x1c0 : ℕ)) else ((0x1c0 : ℕ)))))))
def stored6 (i : ℕ) := if i < 4 then (if i < 2 then (if i < 1 then (([s7,s107,s250,s22,s56,s27,s272] : Row)) else (([s7,s107,s250,s22,s47,s60,s272] : Row))) else (if i < 3 then (([s230,s74,s250,s22,s56,s27,s272] : Row)) else (([s230,s73,s250,s22,s56,s31,s272] : Row)))) else (if i < 6 then (if i < 5 then (([s230,s107,s250,s22,s56,s32,s272] : Row)) else (([s145,s230,s73,s250,s22,s36,s272] : Row))) else (if i < 7 then (([s230,s152,s107,s250,s22,s36,s272] : Row)) else (([s230,s107,s250,s22,s168,s62,s272] : Row))))
def route6 (i : ℕ) := if i < 4 then (if i < 2 then (if i < 1 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 3 then ((0x0 : ℕ)) else ((0x0 : ℕ)))) else (if i < 6 then (if i < 5 then ((0x0 : ℕ)) else ((0x0 : ℕ))) else (if i < 7 then ((0x0 : ℕ)) else ((0x0 : ℕ))))
def stored5 (_i : ℕ) := ([s7,s107,s250,s22,s62,s272] : Row)
def route5 (_i : ℕ) := (0x0 : ℕ)
def stored : ℕ → ℕ → Row
  | 13 => stored13
  | 12 => stored12
  | 11 => stored11
  | 10 => stored10
  | 9 => stored9
  | 8 => stored8
  | 7 => stored7
  | 6 => stored6
  | 5 => stored5
  | _ => fun _ => []
def route : ℕ → ℕ → ℕ
  | 13 => route13
  | 12 => route12
  | 11 => route11
  | 10 => route10
  | 9 => route9
  | 8 => route8
  | 7 => route7
  | 6 => route6
  | 5 => route5
  | _ => fun _ => 0
def sizeAt : Array ℕ := #[0x0,0x0,0x0,0x0,0x0,0x1,0x8,0x32,0xab,0x168,0x1bd,0x145,0x8d,0x1c]
def startRoute : ℕ := 0x28e024e0496019e02a601e4018302c702150195014802cc024c019c0181028b05cb051602e7028302c901da04da0466022e02430218049b02cf05e504e402a50285028d05c3051b024f04e703a401e501d5024d04d70467049502ca05c004d402e402c1028805e004ea05c80515024a04d2039002240211024804e20422051003d00490019a02e2022001600191019802a301ea02e1022102a001e00182028601d401940140018002c2024202c40214028001d00190034a064605940364034103480643059a064505950640059003600340000a008600540024000100080083005a0085005500800050002000000100030a060605540324030103080603055a06050555060005500320030006c000c00680
def words : Array ℕ := #[0x0,0x1,0x2,0x11,0x3,0x19,0x1a,0xd1,0x4,0x21,0x22,0x111,0x23,0x119,0x11a,0x8d1,0x5,0x29,0x2a,0x151,0x2b,0x159,0x15a,0xad1,0x2c,0x161,0x162,0xb11,0x163,0xb19,0xb1a,0x58d1,0x25,0x129,0x12a,0x951,0x12b,0x959,0x95a,0x4ad1,0x12c,0x961,0x962,0x4b11,0x963,0x4b19,0x4b1a,0x258d1]
def sym1 (x : Sig) : Sig := ((x.1 &&& 0xff0000ffffffffffffffffff) ||| ((x.1 &&& 0xff000000000000000000) <<< 8) ||| ((x.1 &&& 0xff00000000000000000000) >>> 8), x.2)
def sym2 (x : Sig) : Sig := ((x.1 &&& 0xffffffff0000ffffffffffff) ||| ((x.1 &&& 0xff000000000000) <<< 8) ||| ((x.1 &&& 0xff00000000000000) >>> 8), x.2)
def sym3 (x : Sig) : Sig := ((x.1 &&& 0xffffffffffffffffff0000ff) ||| ((x.1 &&& 0xff00) <<< 8) ||| ((x.1 &&& 0xff0000) >>> 8), x.2)
def sym4 (x : Sig) : Sig := (((x.1 &&& 0xffffff00000000ff) <<< 24) ||| (x.1 &&& 0xffff00) ||| ((x.1 &&& 0xffffff00000000ff000000) >>> 24) ||| ((x.1 &&& 0xff00000000) <<< 56) ||| ((x.1 &&& 0xff0000000000000000000000) >>> 56), (x.2 &&& 0xc3c3c3c3c3c3c3c3c3c3c3c3) ||| ((x.2 &&& 0xc0c0c0c0c0c0c0c0c0c0c0c) <<< 2) ||| ((x.2 &&& 0x303030303030303030303030) >>> 2))
def sym5 (x : Sig) : Sig := (((x.1 &&& 0xff) <<< 32) ||| ((x.1 &&& 0xffff00) <<< 40) ||| ((x.1 &&& 0xff000000) <<< 16) ||| ((x.1 &&& 0xff00000000) >>> 32) ||| ((x.1 &&& 0xff0000000000) >>> 16) ||| ((x.1 &&& 0xffff000000000000) >>> 40) ||| ((x.1 &&& 0xff0000000000000000) <<< 24) ||| (x.1 &&& 0xffff000000000000000000) ||| ((x.1 &&& 0xff0000000000000000000000) >>> 24), (x.2 &&& 0x999999999999999999999999) ||| ((x.2 &&& 0x222222222222222222222222) <<< 1) ||| ((x.2 &&& 0x444444444444444444444444) >>> 1))
def single : ℕ → Sig → Sig
  | 1 => sym1 | 2 => sym2 | 3 => sym3 | 4 => sym4 | 5 => sym5 | _ => id

def act : ℕ → ℕ → Sig → Sig
  | 0,_ => id
  | n+1,w => if w=0 then id else act n (w >>> 3) ∘ single (w &&& 7)

def moved (q : ℕ) (v : Row) : Row := canon (v.map (act 6 (words[q]?.getD 0)))

def depthSize (k : ℕ) := sizeAt[k]?.getD 0
def walk (k : ℕ) : List Row → ℕ → Bool
  | [],_ => true
  | w::ws,rt => let i := (rt >>> 6) &&& 1023; let q := rt &&& 63
                 decide (i<depthSize k) && (stored k i == moved q w) && walk k ws (rt >>> 16)


abbrev Piece := Bool × ℕ × Mask
def shiftPiece (p : Piece) (x : Mask) := if p.1 then (x &&& p.2.2) <<< p.2.1 else (x &&& p.2.2) >>> p.2.1
def stencil : List Piece → Mask → Mask
  | [],_ => 0
  | p::ps,x => shiftPiece p x ||| stencil ps x
def slot (p : Piece) (i : ℕ) := if p.1 then i-p.2.1 else p.2.1+i
def activeBit (p : Piece) (i : ℕ) := (if p.1 then decide (i<96) && !decide (i<p.2.1) else true) && p.2.2.getLsbD (slot p i)
def positions : List Piece → ℕ → List ℕ
  | [],_ => []
  | p::ps,i => if activeBit p i then slot p i :: positions ps i else positions ps i
lemma pieceRead (p : Piece) (x : Mask) (i : ℕ) : (shiftPiece p x).getLsbD i = (activeBit p i && x.getLsbD (slot p i)) := by
  rcases p with ⟨b,n,m⟩;cases b <;> simp [shiftPiece,activeBit,slot,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]
lemma stencilRead (ps : List Piece) (x : Mask) (i : ℕ) : (stencil ps x).getLsbD i = (positions ps i).any x.getLsbD := by
  induction ps with
  | nil => simp [stencil,positions]
  | cons p ps ih => cases h:activeBit p i <;> simp [positions,stencil,pieceRead,ih,h]
def permCheck (ps : List Piece) := (List.finRange 96).all fun i => let j := (positions ps i.val).headD 96; decide (j<96) && (positions ps i.val == [j]) && (positions ps j == [i.val])
lemma permAt {ps} (h : permCheck ps=true) (i : ℕ) (hi : i<96) : ∃ j<96, positions ps i=[j] ∧ positions ps j=[i] := by
  have q := List.all_eq_true.mp h (⟨i,hi⟩ : Fin 96) (by simp)
  rcases Bool.and_eq_true_iff.mp q with ⟨p,t⟩;rcases Bool.and_eq_true_iff.mp p with ⟨a,b⟩
  exact ⟨_,of_decide_eq_true a,eq_of_beq b,eq_of_beq t⟩
lemma readAt {ps i j} (h : positions ps i=[j]) (x : Mask) : (stencil ps x).getLsbD i = x.getLsbD j := by simp [stencilRead,h]
lemma flipTwice {ps} (h : permCheck ps=true) (x : Mask) : stencil ps (stencil ps x)=x := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi;obtain ⟨j,_,a,b⟩ := permAt h i hi;rw [readAt a,readAt b]
lemma keepAnd {ps} (h : permCheck ps=true) (x y : Mask) : stencil ps (x &&& y) = stencil ps x &&& stencil ps y := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi;obtain ⟨j,_,a,_⟩ := permAt h i hi;simp only [BitVec.getLsbD_and,readAt a]
lemma keepOr {ps} (h : permCheck ps=true) (x y : Mask) : stencil ps (x ||| y) = stencil ps x ||| stencil ps y := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi;obtain ⟨j,_,a,_⟩ := permAt h i hi;simp only [BitVec.getLsbD_or,readAt a]
def actionPair (p n : List Piece) (x : Sig) : Sig := (stencil p x.1,stencil n x.2)
lemma actionTwice {p n} (hp : permCheck p=true) (hn : permCheck n=true) (x : Sig) : actionPair p n (actionPair p n x)=x := by rcases x with ⟨a,b⟩;simp [actionPair,flipTwice hp,flipTwice hn]
lemma actionBin {p n} (hp : permCheck p=true) (hn : permCheck n=true) (o : Bool) (x y : Sig) : actionPair p n (bin o x y) = bin o (actionPair p n x) (actionPair p n y) := by cases o <;> simp [bin,actionPair,keepAnd hp,keepAnd hn,keepOr hp,keepOr hn]
def p1 : List Piece := [(false,0,0xff0000ffffffffffffffffff),(true,8,0xff000000000000000000),(false,8,0xff00000000000000000000)]
lemma p1Checks : permCheck p1=true := by decide +kernel
def n1 : List Piece := [(false,0,0xffffffffffffffffffffffff)]
lemma n1Checks : permCheck n1=true := by decide +kernel
lemma same1 (x : Sig) : sym1 x = actionPair p1 n1 x := by
  rcases x with ⟨a,b⟩;apply Prod.ext <;> simp [sym1,actionPair,p1,n1,stencil,shiftPiece,BitVec.or_assoc]
  exact BitVec.and_allOnes.symm
lemma sym1_iso (x : Sig) : sym1 (sym1 x) = x := by simp only [same1];exact actionTwice p1Checks n1Checks x
lemma sym1_bin (o : Bool) (x y : Sig) : sym1 (bin o x y) = bin o (sym1 x) (sym1 y) := by simp only [same1];exact actionBin p1Checks n1Checks o x y
lemma sym1_goal : sym1 goal = goal := by decide +kernel
def p2 : List Piece := [(false,0,0xffffffff0000ffffffffffff),(true,8,0xff000000000000),(false,8,0xff00000000000000)]
lemma p2Checks : permCheck p2=true := by decide +kernel
def n2 : List Piece := [(false,0,0xffffffffffffffffffffffff)]
lemma n2Checks : permCheck n2=true := by decide +kernel
lemma same2 (x : Sig) : sym2 x = actionPair p2 n2 x := by
  rcases x with ⟨a,b⟩;apply Prod.ext <;> simp [sym2,actionPair,p2,n2,stencil,shiftPiece,BitVec.or_assoc]
  exact BitVec.and_allOnes.symm
lemma sym2_iso (x : Sig) : sym2 (sym2 x) = x := by simp only [same2];exact actionTwice p2Checks n2Checks x
lemma sym2_bin (o : Bool) (x y : Sig) : sym2 (bin o x y) = bin o (sym2 x) (sym2 y) := by simp only [same2];exact actionBin p2Checks n2Checks o x y
lemma sym2_goal : sym2 goal = goal := by decide +kernel
def p3 : List Piece := [(false,0,0xffffffffffffffffff0000ff),(true,8,0xff00),(false,8,0xff0000)]
lemma p3Checks : permCheck p3=true := by decide +kernel
def n3 : List Piece := [(false,0,0xffffffffffffffffffffffff)]
lemma n3Checks : permCheck n3=true := by decide +kernel
lemma same3 (x : Sig) : sym3 x = actionPair p3 n3 x := by
  rcases x with ⟨a,b⟩;apply Prod.ext <;> simp [sym3,actionPair,p3,n3,stencil,shiftPiece,BitVec.or_assoc]
  exact BitVec.and_allOnes.symm
lemma sym3_iso (x : Sig) : sym3 (sym3 x) = x := by simp only [same3];exact actionTwice p3Checks n3Checks x
lemma sym3_bin (o : Bool) (x y : Sig) : sym3 (bin o x y) = bin o (sym3 x) (sym3 y) := by simp only [same3];exact actionBin p3Checks n3Checks o x y
lemma sym3_goal : sym3 goal = goal := by decide +kernel
def p4 : List Piece := [(true,24,0xffffff00000000ff),(false,0,0xffff00),(false,24,0xffffff00000000ff000000),(true,56,0xff00000000),(false,56,0xff0000000000000000000000)]
lemma p4Checks : permCheck p4=true := by decide +kernel
def n4 : List Piece := [(false,0,0xc3c3c3c3c3c3c3c3c3c3c3c3),(true,2,0xc0c0c0c0c0c0c0c0c0c0c0c),(false,2,0x303030303030303030303030)]
lemma n4Checks : permCheck n4=true := by decide +kernel
lemma same4 (x : Sig) : sym4 x = actionPair p4 n4 x := by
  rcases x with ⟨a,b⟩;apply Prod.ext <;> simp [sym4,actionPair,p4,n4,stencil,shiftPiece,BitVec.or_assoc]
lemma sym4_iso (x : Sig) : sym4 (sym4 x) = x := by simp only [same4];exact actionTwice p4Checks n4Checks x
lemma sym4_bin (o : Bool) (x y : Sig) : sym4 (bin o x y) = bin o (sym4 x) (sym4 y) := by simp only [same4];exact actionBin p4Checks n4Checks o x y
lemma sym4_goal : sym4 goal = goal := by decide +kernel
def p5 : List Piece := [(true,32,0xff),(true,40,0xffff00),(true,16,0xff000000),(false,32,0xff00000000),(false,16,0xff0000000000),(false,40,0xffff000000000000),(true,24,0xff0000000000000000),(false,0,0xffff000000000000000000),(false,24,0xff0000000000000000000000)]
lemma p5Checks : permCheck p5=true := by decide +kernel
def n5 : List Piece := [(false,0,0x999999999999999999999999),(true,1,0x222222222222222222222222),(false,1,0x444444444444444444444444)]
lemma n5Checks : permCheck n5=true := by decide +kernel
lemma same5 (x : Sig) : sym5 x = actionPair p5 n5 x := by
  rcases x with ⟨a,b⟩;apply Prod.ext <;> simp [sym5,actionPair,p5,n5,stencil,shiftPiece,BitVec.or_assoc]
lemma sym5_iso (x : Sig) : sym5 (sym5 x) = x := by simp only [same5];exact actionTwice p5Checks n5Checks x
lemma sym5_bin (o : Bool) (x y : Sig) : sym5 (bin o x y) = bin o (sym5 x) (sym5 y) := by simp only [same5];exact actionBin p5Checks n5Checks o x y
lemma sym5_goal : sym5 goal = goal := by decide +kernel
abbrev Tall := Mask × Mask
def countMarks : Row → Tall
  | [] => (0,0)
  | x::xs => let t := countMarks xs; (t.1 ||| mark x,t.2 ||| (t.1 &&& mark x))
def vacate (multi : Mask) (o : Bool) (a b : Sig) := (mark a &&& ~~~multi) &&& (if o then b.2 else ~~~b.1) == 0
def qchoices (room : ℕ) (multi : Mask) (v : Row) (a b : Sig) : List Row :=
  let R := rest v a b
  both.flatMap fun o =>
    let ca := vacate multi o a b
    let cb := vacate multi o b a
    let z := bin o a b
    if (room=0 && !(ca && cb)) || (room=1 && !(ca || cb)) || v.contains z then [] else
    (if ca && cb then [z::R] else []) ++
    (if room>0 && ca then [z::b::R] else []) ++
    (if room>0 && cb then [z::a::R] else []) ++
    (if room>1 then [z::a::b::R] else [])
def qchildren (k : ℕ) (v : Row) : List Row :=
  if v.length>k+2 then [] else
  let room := k+2-v.length
  let multi := (countMarks v).2
  (pairs v).flatMap fun (a,b) => qchoices room multi v a b
def checkedRow (k i : ℕ) : Bool :=
  let v:=stored k i
  !v.contains goal && (match k with | 0 => true | n+1 => walk n (qchildren n v) (route k i))
lemma markPerm {v w : Row} (p : v.Perm w) : countMarks v = countMarks w := by
  induction p with
  | nil => rfl
  | cons a _ ih => simp only [countMarks,ih]
  | swap a b xs =>
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq;intro i hi;simp only [countMarks,BitVec.getLsbD_or,BitVec.getLsbD_and];grind
    · apply BitVec.eq_of_getLsbD_eq;intro i hi;simp only [countMarks,BitVec.getLsbD_or,BitVec.getLsbD_and];grind
  | trans _ _ h1 h2 => exact h1.trans h2
lemma countCover (v : Row) : (countMarks v).1 = cover v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [countMarks,cover,ih,BitVec.or_comm]
lemma permRemove {v : Row} {a b : Sig} (nd : v.Nodup) (ab : a≠b) (ha : a∈v) (hb : b∈v) :
    v.Perm (a :: b :: rest v a b) := by
  have a1 := List.perm_cons_erase ha
  have b1 : b∈v.erase a := by rw [nd.erase_eq_filter];simp [hb,Ne.symm ab]
  have a2 := (List.perm_cons_erase b1).cons a
  have eq : (v.erase a).erase b = rest v a b := by
    rw [(nd.erase a).erase_eq_filter,nd.erase_eq_filter]
    simp only [List.filter_filter,rest]
    congr 1; funext x; simp [Bool.and_comm]; rfl
  simpa only [eq] using a1.trans a2
lemma privateTest {a b : Sig} {R : Row} {o f g : Bool}
    (h : mark (bin o a b) ||| (if f then mark a else 0) ||| (if g then mark b else 0) ||| cover R = -1) :
    (f=true ∨ vacate (countMarks (a::b::R)).2 o a b = true) ∧
    (g=true ∨ vacate (countMarks (a::b::R)).2 o b a = true) := by
  rw [←countCover] at h
  rcases a with ⟨pa,na⟩;rcases b with ⟨pb,nb⟩
  cases o <;> cases f <;> cases g <;> simp [countMarks,vacate,mark,bin] at h ⊢
  all_goals try constructor
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have p := congrArg (fun t : Mask => t.getLsbD i) h
    simp [BitVec.neg_one_eq_allOnes,BitVec.getLsbD_not,hi] at p ⊢
    grind
lemma qOneChoice {a b : Sig} {U : Finset Sig} {o : Bool} {v : Row} {k j : ℕ}
    (ab : a≠b) (nd : v.Nodup) (eqv : v.toFinset = insert a (insert b U))
    (fresh : bin o a b ∉ insert a (insert b U)) (live : Live j (insert (bin o a b) U)) (small : j≤k) :
    ∃ w∈qchoices (k+2-v.length) (countMarks v).2 v a b, w.Nodup ∧ w.toFinset = insert (bin o a b) U := by
  let z := bin o a b
  let f := decide (a∈U); let g := decide (b∈U)
  let R := rest v a b
  let w := z :: (pick f a ++ pick g b ++ R)
  have mem (x : Sig) : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [←List.mem_toFinset,eqv];simp
  have Rmem {x} : x∈R ↔ x∈U ∧ x≠a ∧ x≠b := by simp [R,rest,mem]; tauto
  have fz : z≠a ∧ z≠b ∧ z∉U := by simpa [z] using fresh
  have Rnd : R.Nodup := nd.filter _
  have wn : w.Nodup := by
    by_cases ha:a∈U <;> by_cases hb:b∈U <;> simp [w,pick,f,g,ha,hb,List.nodup_cons,Rmem,Rnd,fz,ab]
  have ws : w.toFinset = insert z U := by
    ext x; by_cases ha:a∈U <;> by_cases hb:b∈U <;> simp [w,pick,f,g,ha,hb,Rmem] <;> grind
  have lw : Live j w.toFinset := ws.symm ▸ live
  have length : w.length ≤ k+1 := by have h := live_size lw; rw [List.toFinset_card_of_nodup wn] at h; omega
  have cov : cover w = -1 := live_cover lw
  have mask : mark z ||| (if f then mark a else 0) ||| (if g then mark b else 0) ||| cover R = -1 := by
    cases hf:f <;> cases hg:g <;> simpa [w,hf,hg,pick,cover,BitVec.or_assoc] using cov
  have ha : a∈v := (mem a).mpr (Or.inl rfl)
  have hb : b∈v := (mem b).mpr (Or.inr (Or.inl rfl))
  have pr := permRemove nd ab ha hb
  have len : v.length = R.length+2 := by simpa [R] using pr.length_eq
  have cond := privateTest (o:=o) (f:=f) (g:=g) mask
  rw [←markPerm pr] at cond
  have bits : f.toNat+g.toNat ≤ k+2-v.length := by
    cases hf:f <;> cases hg:g <;> simp [w,pick,hf,hg] at length ⊢ <;> omega
  have nt : v.contains z = false := by simp [List.contains_eq_mem,mem,fz]
  have notin : bin o a b ∉ v := by simpa [List.contains_eq_mem,z] using nt
  refine ⟨w,?_,wn,ws⟩
  unfold qchoices
  apply List.mem_flatMap.mpr
  refine ⟨o,mem_both _,?_⟩
  change w ∈ if _ || _ || v.contains z then [] else _
  rcases cond with ⟨ca,cb⟩
  cases hf:f <;> cases hg:g <;>
    cases hl:vacate (countMarks v).2 o a b <;> cases hr:vacate (countMarks v).2 o b a <;>
    simp [hf,hg,hl,hr] at ca cb bits <;>
    simp [notin,w,pick,hf,hg,R,z,hl,hr] <;> omega
lemma quick_live {k j v} (nd : v.Nodup) (h : Live (j+1) v.toFinset) (hj : j≤k) : ∃ w∈qchildren k v, w.Nodup ∧ Live j w.toFinset := by
  have len : v.length ≤ k+2 := by have t := live_size h;rw [List.toFinset_card_of_nodup nd] at t;omega
  obtain ⟨U,a,b,o,ab,fresh,eqv,tail⟩ := h
  have ha : a∈v := List.mem_toFinset.mp (eqv ▸ (by simp))
  have hb : b∈v := List.mem_toFinset.mp (eqv ▸ (by simp))
  simp only [qchildren,show ¬v.length>k+2 from by omega,ite_false]
  rcases coverPair ab ha hb with pair|pair
  · obtain ⟨w,hw,wn,we⟩ := qOneChoice ab nd eqv fresh tail hj
    exact ⟨w,List.mem_flatMap.mpr ⟨(a,b),pair,hw⟩,wn,we.symm ▸ tail⟩
  · rw [Finset.insert_comm a b] at eqv fresh
    rw [bin_comm o a b] at fresh tail
    obtain ⟨w,hw,wn,we⟩ := qOneChoice ab.symm nd eqv fresh tail hj
    exact ⟨w,List.mem_flatMap.mpr ⟨(b,a),pair,hw⟩,wn,we.symm ▸ tail⟩
def iso (f : Sig → Sig) : Prop := Function.Injective f ∧ f goal = goal ∧ ∀ o a b, f (bin o a b) = bin o (f a) (f b)
lemma makeIso (f : Sig → Sig) (inv : ∀ x, f (f x) = x) (g : f goal=goal) (bi : ∀ o a b, f (bin o a b) = bin o (f a) (f b)) : iso f := ⟨Function.LeftInverse.injective inv,g,bi⟩
lemma idIso : iso id := ⟨Function.injective_id,rfl,fun _ _ _ => rfl⟩
lemma compIso {f g : Sig → Sig} (hf : iso f) (hg : iso g) : iso (f ∘ g) := ⟨hf.1.comp hg.1,by simp [hg.2.1,hf.2.1],by intro o a b; simp [hg.2.2,hf.2.2]⟩
lemma singleIso (i : ℕ) : iso (single i) := by
  unfold single; split
  · exact makeIso _ sym1_iso sym1_goal sym1_bin
  · exact makeIso _ sym2_iso sym2_goal sym2_bin
  · exact makeIso _ sym3_iso sym3_goal sym3_bin
  · exact makeIso _ sym4_iso sym4_goal sym4_bin
  · exact makeIso _ sym5_iso sym5_goal sym5_bin
  · exact idIso
lemma actIso (n w) : iso (act n w) := by
  induction n generalizing w with
  | zero => exact idIso
  | succ n ih => rw [act]; split; exact idIso; exact compIso (ih _) (singleIso _)
lemma mapLive {k S} (h : Live k S) {f} (hf : iso f) : Live k (S.image f) := by
  induction k generalizing S with
  | zero => change S={goal} at h; change S.image f={goal}; simp [h,hf.2.1]
  | succ k ih =>
    obtain ⟨U,a,b,o,ab,fresh,rfl,t⟩ := h
    rw [Finset.image_insert,Finset.image_insert]
    apply Live.step (fun e => ab (hf.1 e))
    · rw [←hf.2.2]; intro e;apply fresh;rcases Finset.mem_insert.mp e with e|e
      · exact Finset.mem_insert.mpr (.inl (hf.1 e))
      rcases Finset.mem_insert.mp e with e|e
      · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (.inl (hf.1 e)))
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp e
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((hf.1 eq) ▸ hx))
    · simpa [hf.2.2] using ih t

lemma movedLive {k} (q : ℕ) {v : Row} (h : Live k v.toFinset) : Live k (moved q v).toFinset := by
  have t := mapLive h (actIso 6 (words[q]?.getD 0))
  rw [moved,canon_set]; convert t using 1; ext x; simp

lemma walk_sound {k rt xs} (ok : walk k xs rt=true) {w} (mem : w∈xs) : ∃ j<depthSize k, ∃ q, stored k j=moved q w := by
  induction xs generalizing rt with
  | nil => simp at mem
  | cons x xs ih =>
    rcases Bool.and_eq_true_iff.mp ok with ⟨head,tail⟩
    rcases List.mem_cons.mp mem with rfl|mem
    · obtain ⟨bound,eq⟩ := Bool.and_eq_true_iff.mp head
      exact ⟨_,of_decide_eq_true bound,_,eq_of_beq eq⟩
    · exact ih tail mem
lemma checkedSafe (k : ℕ) (cert : ∀ n ≤ k, ∀ i<depthSize n, checkedRow n i = true) (j i : ℕ) (le : j≤k) (bound : i<depthSize k) (nd : (stored k i).Nodup) : ¬Live j (stored k i).toFinset := by
  intro h;have ok := Bool.and_eq_true_iff.mp (cert k (Nat.le_refl _) i bound)
  have off : goal ∉ stored k i := by simpa using ok.1
  cases j with
  | zero => change (stored k i).toFinset={goal} at h; exact off (List.mem_toFinset.mp (h ▸ (by simp)))
  | succ j => cases k with
    | zero => omega
    | succ k =>
      have jc : j≤k := by omega
      obtain ⟨w,mem,_,pos⟩ := quick_live nd h jc
      obtain ⟨n,hn,q,eq⟩ := walk_sound ok.2 mem
      have res : Live j (stored k n).toFinset := eq.symm ▸ movedLive q pos
      have newnd : (stored k n).Nodup := by rw [eq];exact List.nodup_dedup _
      exact checkedSafe k (fun n u => cert n (by omega)) j n jc hn newnd res
termination_by k
def block (k offset n : ℕ) := (List.range n).all fun j => checkedRow k (offset+j)
lemma inBlock {k offset n i : ℕ} (h : block k offset n=true) (lo : offset ≤ i) (hi : i < offset + n) : checkedRow k i=true := by
  have hit := List.all_eq_true.mp h (i-offset) (List.mem_range.mpr (show i-offset<n by omega));simpa [Nat.add_sub_of_le lo] using hit
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_5_0 : block 5 0 1 = true := by decide +kernel
lemma layer5 (i : ℕ) (h : i<depthSize 5) : checkedRow 5 i = true := by
  change i < 1 at h
  exact inBlock check_5_0 (by omega) (by omega)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_6_0 : block 6 0 8 = true := by decide +kernel
lemma layer6 (i : ℕ) (h : i<depthSize 6) : checkedRow 6 i = true := by
  change i < 8 at h
  exact inBlock check_6_0 (by omega) (by omega)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_7_0 : block 7 0 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_7_20 : block 7 20 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_7_40 : block 7 40 10 = true := by decide +kernel
lemma layer7 (i : ℕ) (h : i<depthSize 7) : checkedRow 7 i = true := by
  change i < 50 at h
  by_cases h0 : i < 20
  · exact inBlock check_7_0 (by omega) (by omega)
  by_cases h1 : i < 40
  · exact inBlock check_7_20 (by omega) (by omega)
  exact inBlock check_7_40 (by omega) (by omega)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_8_0 : block 8 0 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_8_20 : block 8 20 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_8_40 : block 8 40 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_8_60 : block 8 60 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_8_80 : block 8 80 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_8_100 : block 8 100 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_8_120 : block 8 120 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_8_140 : block 8 140 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_8_160 : block 8 160 11 = true := by decide +kernel
lemma layer8 (i : ℕ) (h : i<depthSize 8) : checkedRow 8 i = true := by
  change i < 171 at h
  by_cases h0 : i < 20
  · exact inBlock check_8_0 (by omega) (by omega)
  by_cases h1 : i < 40
  · exact inBlock check_8_20 (by omega) (by omega)
  by_cases h2 : i < 60
  · exact inBlock check_8_40 (by omega) (by omega)
  by_cases h3 : i < 80
  · exact inBlock check_8_60 (by omega) (by omega)
  by_cases h4 : i < 100
  · exact inBlock check_8_80 (by omega) (by omega)
  by_cases h5 : i < 120
  · exact inBlock check_8_100 (by omega) (by omega)
  by_cases h6 : i < 140
  · exact inBlock check_8_120 (by omega) (by omega)
  by_cases h7 : i < 160
  · exact inBlock check_8_140 (by omega) (by omega)
  exact inBlock check_8_160 (by omega) (by omega)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_0 : block 9 0 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_20 : block 9 20 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_40 : block 9 40 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_60 : block 9 60 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_80 : block 9 80 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_100 : block 9 100 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_120 : block 9 120 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_140 : block 9 140 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_160 : block 9 160 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_180 : block 9 180 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_200 : block 9 200 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_220 : block 9 220 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_240 : block 9 240 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_260 : block 9 260 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_280 : block 9 280 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_300 : block 9 300 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_320 : block 9 320 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_9_340 : block 9 340 20 = true := by decide +kernel
lemma layer9 (i : ℕ) (h : i<depthSize 9) : checkedRow 9 i = true := by
  change i < 360 at h
  by_cases h0 : i < 20
  · exact inBlock check_9_0 (by omega) (by omega)
  by_cases h1 : i < 40
  · exact inBlock check_9_20 (by omega) (by omega)
  by_cases h2 : i < 60
  · exact inBlock check_9_40 (by omega) (by omega)
  by_cases h3 : i < 80
  · exact inBlock check_9_60 (by omega) (by omega)
  by_cases h4 : i < 100
  · exact inBlock check_9_80 (by omega) (by omega)
  by_cases h5 : i < 120
  · exact inBlock check_9_100 (by omega) (by omega)
  by_cases h6 : i < 140
  · exact inBlock check_9_120 (by omega) (by omega)
  by_cases h7 : i < 160
  · exact inBlock check_9_140 (by omega) (by omega)
  by_cases h8 : i < 180
  · exact inBlock check_9_160 (by omega) (by omega)
  by_cases h9 : i < 200
  · exact inBlock check_9_180 (by omega) (by omega)
  by_cases h10 : i < 220
  · exact inBlock check_9_200 (by omega) (by omega)
  by_cases h11 : i < 240
  · exact inBlock check_9_220 (by omega) (by omega)
  by_cases h12 : i < 260
  · exact inBlock check_9_240 (by omega) (by omega)
  by_cases h13 : i < 280
  · exact inBlock check_9_260 (by omega) (by omega)
  by_cases h14 : i < 300
  · exact inBlock check_9_280 (by omega) (by omega)
  by_cases h15 : i < 320
  · exact inBlock check_9_300 (by omega) (by omega)
  by_cases h16 : i < 340
  · exact inBlock check_9_320 (by omega) (by omega)
  exact inBlock check_9_340 (by omega) (by omega)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_0 : block 10 0 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_20 : block 10 20 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_40 : block 10 40 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_60 : block 10 60 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_80 : block 10 80 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_100 : block 10 100 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_120 : block 10 120 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_140 : block 10 140 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_160 : block 10 160 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_180 : block 10 180 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_200 : block 10 200 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_220 : block 10 220 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_240 : block 10 240 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_260 : block 10 260 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_280 : block 10 280 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_300 : block 10 300 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_320 : block 10 320 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_340 : block 10 340 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_360 : block 10 360 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_380 : block 10 380 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_400 : block 10 400 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_420 : block 10 420 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_10_440 : block 10 440 5 = true := by decide +kernel
lemma layer10 (i : ℕ) (h : i<depthSize 10) : checkedRow 10 i = true := by
  change i < 445 at h
  by_cases h0 : i < 20
  · exact inBlock check_10_0 (by omega) (by omega)
  by_cases h1 : i < 40
  · exact inBlock check_10_20 (by omega) (by omega)
  by_cases h2 : i < 60
  · exact inBlock check_10_40 (by omega) (by omega)
  by_cases h3 : i < 80
  · exact inBlock check_10_60 (by omega) (by omega)
  by_cases h4 : i < 100
  · exact inBlock check_10_80 (by omega) (by omega)
  by_cases h5 : i < 120
  · exact inBlock check_10_100 (by omega) (by omega)
  by_cases h6 : i < 140
  · exact inBlock check_10_120 (by omega) (by omega)
  by_cases h7 : i < 160
  · exact inBlock check_10_140 (by omega) (by omega)
  by_cases h8 : i < 180
  · exact inBlock check_10_160 (by omega) (by omega)
  by_cases h9 : i < 200
  · exact inBlock check_10_180 (by omega) (by omega)
  by_cases h10 : i < 220
  · exact inBlock check_10_200 (by omega) (by omega)
  by_cases h11 : i < 240
  · exact inBlock check_10_220 (by omega) (by omega)
  by_cases h12 : i < 260
  · exact inBlock check_10_240 (by omega) (by omega)
  by_cases h13 : i < 280
  · exact inBlock check_10_260 (by omega) (by omega)
  by_cases h14 : i < 300
  · exact inBlock check_10_280 (by omega) (by omega)
  by_cases h15 : i < 320
  · exact inBlock check_10_300 (by omega) (by omega)
  by_cases h16 : i < 340
  · exact inBlock check_10_320 (by omega) (by omega)
  by_cases h17 : i < 360
  · exact inBlock check_10_340 (by omega) (by omega)
  by_cases h18 : i < 380
  · exact inBlock check_10_360 (by omega) (by omega)
  by_cases h19 : i < 400
  · exact inBlock check_10_380 (by omega) (by omega)
  by_cases h20 : i < 420
  · exact inBlock check_10_400 (by omega) (by omega)
  by_cases h21 : i < 440
  · exact inBlock check_10_420 (by omega) (by omega)
  exact inBlock check_10_440 (by omega) (by omega)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_0 : block 11 0 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_20 : block 11 20 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_40 : block 11 40 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_60 : block 11 60 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_80 : block 11 80 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_100 : block 11 100 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_120 : block 11 120 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_140 : block 11 140 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_160 : block 11 160 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_180 : block 11 180 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_200 : block 11 200 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_220 : block 11 220 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_240 : block 11 240 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_260 : block 11 260 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_280 : block 11 280 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_300 : block 11 300 20 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_11_320 : block 11 320 5 = true := by decide +kernel
lemma layer11 (i : ℕ) (h : i<depthSize 11) : checkedRow 11 i = true := by
  change i < 325 at h
  by_cases h0 : i < 20
  · exact inBlock check_11_0 (by omega) (by omega)
  by_cases h1 : i < 40
  · exact inBlock check_11_20 (by omega) (by omega)
  by_cases h2 : i < 60
  · exact inBlock check_11_40 (by omega) (by omega)
  by_cases h3 : i < 80
  · exact inBlock check_11_60 (by omega) (by omega)
  by_cases h4 : i < 100
  · exact inBlock check_11_80 (by omega) (by omega)
  by_cases h5 : i < 120
  · exact inBlock check_11_100 (by omega) (by omega)
  by_cases h6 : i < 140
  · exact inBlock check_11_120 (by omega) (by omega)
  by_cases h7 : i < 160
  · exact inBlock check_11_140 (by omega) (by omega)
  by_cases h8 : i < 180
  · exact inBlock check_11_160 (by omega) (by omega)
  by_cases h9 : i < 200
  · exact inBlock check_11_180 (by omega) (by omega)
  by_cases h10 : i < 220
  · exact inBlock check_11_200 (by omega) (by omega)
  by_cases h11 : i < 240
  · exact inBlock check_11_220 (by omega) (by omega)
  by_cases h12 : i < 260
  · exact inBlock check_11_240 (by omega) (by omega)
  by_cases h13 : i < 280
  · exact inBlock check_11_260 (by omega) (by omega)
  by_cases h14 : i < 300
  · exact inBlock check_11_280 (by omega) (by omega)
  by_cases h15 : i < 320
  · exact inBlock check_11_300 (by omega) (by omega)
  exact inBlock check_11_320 (by omega) (by omega)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_0 : block 12 0 12 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_12 : block 12 12 12 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_24 : block 12 24 12 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_36 : block 12 36 12 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_48 : block 12 48 12 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_60 : block 12 60 12 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_72 : block 12 72 12 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_84 : block 12 84 12 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_96 : block 12 96 12 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_108 : block 12 108 12 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_120 : block 12 120 12 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_12_132 : block 12 132 9 = true := by decide +kernel
lemma layer12 (i : ℕ) (h : i<depthSize 12) : checkedRow 12 i = true := by
  change i < 141 at h
  by_cases h0 : i < 12
  · exact inBlock check_12_0 (by omega) (by omega)
  by_cases h1 : i < 24
  · exact inBlock check_12_12 (by omega) (by omega)
  by_cases h2 : i < 36
  · exact inBlock check_12_24 (by omega) (by omega)
  by_cases h3 : i < 48
  · exact inBlock check_12_36 (by omega) (by omega)
  by_cases h4 : i < 60
  · exact inBlock check_12_48 (by omega) (by omega)
  by_cases h5 : i < 72
  · exact inBlock check_12_60 (by omega) (by omega)
  by_cases h6 : i < 84
  · exact inBlock check_12_72 (by omega) (by omega)
  by_cases h7 : i < 96
  · exact inBlock check_12_84 (by omega) (by omega)
  by_cases h8 : i < 108
  · exact inBlock check_12_96 (by omega) (by omega)
  by_cases h9 : i < 120
  · exact inBlock check_12_108 (by omega) (by omega)
  by_cases h10 : i < 132
  · exact inBlock check_12_120 (by omega) (by omega)
  exact inBlock check_12_132 (by omega) (by omega)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_13_0 : block 13 0 4 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_13_4 : block 13 4 4 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_13_8 : block 13 8 4 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_13_12 : block 13 12 4 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_13_16 : block 13 16 4 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_13_20 : block 13 20 4 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma check_13_24 : block 13 24 4 = true := by decide +kernel
lemma layer13 (i : ℕ) (h : i<depthSize 13) : checkedRow 13 i = true := by
  change i < 28 at h
  by_cases h0 : i < 4
  · exact inBlock check_13_0 (by omega) (by omega)
  by_cases h1 : i < 8
  · exact inBlock check_13_4 (by omega) (by omega)
  by_cases h2 : i < 12
  · exact inBlock check_13_8 (by omega) (by omega)
  by_cases h3 : i < 16
  · exact inBlock check_13_12 (by omega) (by omega)
  by_cases h4 : i < 20
  · exact inBlock check_13_16 (by omega) (by omega)
  by_cases h5 : i < 24
  · exact inBlock check_13_20 (by omega) (by omega)
  exact inBlock check_13_24 (by omega) (by omega)
lemma certificate (k : ℕ) (h : k≤13) (i : ℕ) (hi : i<depthSize k) : checkedRow k i = true := by
  interval_cases k
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · change i < 0 at hi; omega
  · exact layer5 i hi
  · exact layer6 i hi
  · exact layer7 i hi
  · exact layer8 i hi
  · exact layer9 i hi
  · exact layer10 i hi
  · exact layer11 i hi
  · exact layer12 i hi
  · exact layer13 i hi
def startOK (i : ℕ) := let rt := startRoute >>> (16*i); let j := (rt >>> 6) &&& 1023; decide (j < depthSize 13) && (stored 13 j == moved (rt &&& 63) (roots[i]?.getD []))
def startBlock (off n : ℕ) := (List.range n).all fun i => startOK (off+i)
lemma startIn {off n i : ℕ} (h : startBlock off n = true) (lo : off ≤ i) (hi : i < off + n) : startOK i = true := by
  have p := List.all_eq_true.mp h (i-off) (List.mem_range.mpr (show i-off<n by omega));simpa [Nat.add_sub_of_le lo] using p
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_0 : startBlock 0 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_6 : startBlock 6 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_12 : startBlock 12 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_18 : startBlock 18 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_24 : startBlock 24 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_30 : startBlock 30 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_36 : startBlock 36 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_42 : startBlock 42 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_48 : startBlock 48 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_54 : startBlock 54 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_60 : startBlock 60 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_66 : startBlock 66 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_72 : startBlock 72 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_78 : startBlock 78 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_84 : startBlock 84 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_90 : startBlock 90 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_96 : startBlock 96 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_102 : startBlock 102 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_108 : startBlock 108 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_114 : startBlock 114 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_120 : startBlock 120 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_126 : startBlock 126 6 = true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma start_132 : startBlock 132 5 = true := by decide +kernel
lemma startsPass (i : ℕ) (hi : i<roots.length) : startOK i = true := by
  have n : roots.length=137 := by decide +kernel
  rw [n] at hi
  by_cases b0 : i<6
  · exact startIn start_0 (by omega) (by omega)
  by_cases b1 : i<12
  · exact startIn start_6 (by omega) (by omega)
  by_cases b2 : i<18
  · exact startIn start_12 (by omega) (by omega)
  by_cases b3 : i<24
  · exact startIn start_18 (by omega) (by omega)
  by_cases b4 : i<30
  · exact startIn start_24 (by omega) (by omega)
  by_cases b5 : i<36
  · exact startIn start_30 (by omega) (by omega)
  by_cases b6 : i<42
  · exact startIn start_36 (by omega) (by omega)
  by_cases b7 : i<48
  · exact startIn start_42 (by omega) (by omega)
  by_cases b8 : i<54
  · exact startIn start_48 (by omega) (by omega)
  by_cases b9 : i<60
  · exact startIn start_54 (by omega) (by omega)
  by_cases b10 : i<66
  · exact startIn start_60 (by omega) (by omega)
  by_cases b11 : i<72
  · exact startIn start_66 (by omega) (by omega)
  by_cases b12 : i<78
  · exact startIn start_72 (by omega) (by omega)
  by_cases b13 : i<84
  · exact startIn start_78 (by omega) (by omega)
  by_cases b14 : i<90
  · exact startIn start_84 (by omega) (by omega)
  by_cases b15 : i<96
  · exact startIn start_90 (by omega) (by omega)
  by_cases b16 : i<102
  · exact startIn start_96 (by omega) (by omega)
  by_cases b17 : i<108
  · exact startIn start_102 (by omega) (by omega)
  by_cases b18 : i<114
  · exact startIn start_108 (by omega) (by omega)
  by_cases b19 : i<120
  · exact startIn start_114 (by omega) (by omega)
  by_cases b20 : i<126
  · exact startIn start_120 (by omega) (by omega)
  by_cases b21 : i<132
  · exact startIn start_126 (by omega) (by omega)
  exact startIn start_132 (by omega) (by omega)
lemma startChecked {w} (hw : w∈roots) : ∃ n < depthSize 13, ∃ q, stored 13 n = moved q w := by
  obtain ⟨i,hi,e⟩ := List.getElem_of_mem hw
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp (startsPass i hi)
  refine ⟨_,of_decide_eq_true a,(startRoute >>> (16*i)) &&& 63,?_⟩
  have t := eq_of_beq b
  simpa [List.getElem?_eq_getElem hi,e] using t
end PEqualNP.Outside.L_meta_2427

open PEqualNP.Outside.L_meta_2427 in
theorem PEqualNP.Outside.L_meta_2427 : ¬ (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (List ℕ) := [[(0 : ℕ)], [(1 : ℕ)], [(2 : ℕ)], [(13 : ℕ)], [(14 : ℕ)], [(15 : ℕ)], [(17 : ℕ)], [(18 : ℕ)], [(19 : ℕ)], [(23 : ℕ)], [(24 : ℕ)], [(25 : ℕ)], [(13 : ℕ), (15 : ℕ)], [(14 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ), (18 : ℕ)], [(19 : ℕ), (23 : ℕ)], [(18 : ℕ), (19 : ℕ), (23 : ℕ)], [(17 : ℕ), (24 : ℕ)], [(17 : ℕ), (19 : ℕ), (24 : ℕ)], [(18 : ℕ), (25 : ℕ)], [(13 : ℕ), (19 : ℕ)], [(14 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ), (24 : ℕ)], [(24 : ℕ), (25 : ℕ)]]; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ (13 : ℕ) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x3 fun (x5 : Fin (26 : ℕ)) => (x2.getD ↑x5 []).any fun (x6 : ℕ) => x4 (Fin.ofNat (26 : ℕ) x6)) = Decidable.decide (∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), ↑x5 < (3 : ℕ) ∧ (∃ x7 ∈ x1, x5 = x6 + x7) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true)) := by
  intro existence
  obtain ⟨C,mono,size,computes⟩ := existence
  obtain ⟨k,S,le,live,sub⟩ := extract C.gates raw (get_goal C mono computes)
  have cap : k≤13 := le.trans size
  obtain ⟨w,hw,_,eq⟩ := root_mem cap live sub
  obtain ⟨j,bound,q,relabel⟩ := startChecked hw
  have act : Live k (stored 13 j).toFinset := relabel.symm ▸ movedLive q (eq.symm ▸ live)
  have nd : (stored 13 j).Nodup := by rw [relabel];exact List.nodup_dedup _
  exact checkedSafe 13 certificate k j cap bound nd act
