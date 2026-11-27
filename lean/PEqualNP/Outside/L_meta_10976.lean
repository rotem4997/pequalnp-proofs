import PEqualNP.Defs

-- The two-mode live-state and cofactor checker is adapted from PEqualNP/Outside/L_meta_8459.lean (Apache-2.0),
-- which follows L_meta_1674, L_meta_670 and L_meta_1667 (Apache-2.0).
-- The graph, restrictions and all search certificates below are for this row.

namespace PEqualNP.Outside.L_meta_10976
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffefffcfffefffcfffffefefffffefeffffeeeeffffeeeefefefcfcfafaf0f0eeeeccccaaaa0000
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8) || (x 7 && x 8)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 4 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 6 &&& x 8) ||| (x 7 &&& x 8)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 4 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 6 &&& x 8) ||| (x 7 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)

theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def kwLeaf (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem kwTight {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := kwWidth tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨kwFork d01 ha hb fresh H⟩

def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v

theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw

theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible false T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)

def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def kwWord (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := kwProbe pos (field 2)
  let n := kwProbe neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a p (kwProbe neg (field 4)) && kwWireB ws T b p (kwProbe neg (field 5)) &&
    kwWireB ws T a (kwProbe pos (field 6)) n && kwWireB ws T b (kwProbe pos (field 7)) n
theorem kwWord_sound {pos neg T ws k v} (h : kwWord pos neg T ws k v=true) : Impossible false T k ws.toFinset := by
  simp only [kwWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)

def CutRow (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible g.mode (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : CutRow g k a 0 := by
  intro j lo hi
  omega
theorem checkedRow {g k a n} (h : block g k a n=true) : CutRow g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem joinRow {g k a x y} (first : CutRow g k a x) (last : CutRow g k (a+x) y) :
    CutRow g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def kwTest (pos neg : Nat) (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all (fun j => kwWord pos neg (targetOf g) (stateSet g k (a+j)) k (packedAt data (32*j) 32))
theorem mixedCut {pos neg g k a n data} (mode : g.mode=false) (h : kwTest pos neg g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord pos neg _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact kwWord_sound hh

def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, CutRow g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1

def nineInputs : List Sig := vars 511
def sampleNine (r : Row) (i : Fin 9) : Bool := bit r (nineInputs.getD i.val zero)
def nineEdge (x : Fin 9 → Bool) := (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8) || (x 7 && x 8)

theorem nineTable : ∀ r : Row, bit r graph = nineEdge (sampleNine r) := by decide +kernel
theorem nineList : List.ofFn (fun i : Fin 9 => nineInputs.getD i.val zero) = nineInputs := rfl
theorem nineSampled (r : Row) : List.ofFn (sampleNine r) = nineInputs.map (bit r) := by
  rw [← nineList, List.map_ofFn]
  rfl

theorem nineEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates nineInputs).getD i zero) =
      (C.wires (List.ofFn (sampleNine r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),nineSampled]
  rfl
def neighborRow (i : Fin 9) : Nat := [4,5,6,8,0,1,2,0,1].getD i.val 0
def absentRowRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighborRow i)
def presentRowRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighborRow i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRowRow i) graph ≠ bit (presentRowRow i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRowRow i) (nineInputs.getD j.val zero) =
      bit (presentRowRow i) (nineInputs.getD j.val zero)) := by decide +kernel

theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = nineEdge) (small : C.size ≤ 14) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 13 else 14) ∧ Live u graph k nineInputs.toFinset := by
  have goalEq : (execute C.gates nineInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (nineEval C legal C.output r).trans ((congrFun computes (sampleNine r)).trans (nineTable r).symm)
  have len : C.gates.length ≤ 14 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 13 else 14) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := get_rep (u:=u) (execute C.gates nineInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates nineInputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : nineInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ nineInputs) : ∃ i : Fin 9, nineInputs.getD i.val zero = a := by
    rw [←nineList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = nineInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run nineInputs (nineInputs.getD i.val zero) sub (absentRowRow i) (presentRowRow i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 14 → ¬Live false graph k nineInputs.toFinset)
    (s : ∀ k, k ≤ 13 → ¬Live true graph k nineInputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 nineEdge 14 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run

def g145Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffdd,0xffffffffffffffffffffffffffffffffffffd1),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffe7,0x24),(0x0,0x0),(0x0,0x0),(0x3a,0xa),(0x0,0x0)]
def g145C : List ColumnInfo := []
def g145A : List (List Nat) := [[]]
def g145D3 (j : Nat) : Nat := 0x7
def g145L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g145D3)
  | _ => emptyPacking
def g145I (_ _ : Nat) : Option (Nat × Nat) := none
def g145 : Forest := ⟨145,3,fun i => g145Y[i]?.getD (0,0),g145C,g145A,g145L,g145I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g145P3_0 : block g145 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g145B3 : block g145 3 0 1=true := g145P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g145T : checkedTables g145 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g145 0 0 0 = true)
  · exact (rfl : block g145 1 0 0 = true)
  · exact (rfl : block g145 2 0 0 = true)
  · exact g145B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g145G : graphValid g145 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low145 : Lower true (varsX 145) (graphGoal 145) 4 := lower_forest (g:=g145) (i:=0) (hints:=4) (before_sound [] baseKnown) g145G g145T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K145 := extendKnown [] 4 [(145,[]),(324,[135,100,32]),(386,[116,132,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V145 : Known true K145 := extend_ok (m:=145) baseKnown low145 (by decide +kernel)
def g163Y : Array (Bits × Bits) := #[(0x1cccc,0xd4e4),(0xfffffffffffffffffffffffffffffffffe7773,0xfffffffffffffffffffffffffffffffffc5051),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffff8663,0x3aea2),(0x0,0x0),(0x3f99c,0x32b08),(0x0,0x0)]
def g163C : List ColumnInfo := []
def g163A : List (List Nat) := [[]]
def g163D3 (j : Nat) : Nat := 0xf
def g163L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g163D3)
  | _ => emptyPacking
def g163I (_ _ : Nat) : Option (Nat × Nat) := none
def g163 : Forest := ⟨163,3,fun i => g163Y[i]?.getD (0,0),g163C,g163A,g163L,g163I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163P3_0 : block g163 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g163B3 : block g163 3 0 1=true := g163P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163T : checkedTables g163 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g163 0 0 0 = true)
  · exact (rfl : block g163 1 0 0 = true)
  · exact (rfl : block g163 2 0 0 = true)
  · exact g163B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163G : graphValid g163 (boundsBefore K145) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low163 : Lower true (varsX 163) (graphGoal 163) 4 := lower_forest (g:=g163) (i:=0) (hints:=1048663) (before_sound K145 V145) g163G g163T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K163 := extendKnown K145 4 [(163,[]),(178,[64]),(294,[135,32]),(298,[135,48]),(354,[135,96]),(389,[129,81,33]),(404,[113,129,81,65,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V163 : Known true K163 := extend_ok (m:=163) V145 low163 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[(0x82f1d4e9c,0x8212b0e0c),(0xfffffffffffffffffffffffffffff430e2fe43,0xffffffffffffffffffffffffffffe420027a01),(0x0,0x0),(0x0,0x0),(0x7c31ce934,0x4c254e110),(0xfffffffffffffffffffffffffffff803e4a7a3,0x1a9bfd85a2),(0x0,0x0),(0x1ffc0711e8,0x131c8000e0),(0x0,0x0)]
def g179C : List ColumnInfo := [(16,0,163,0,4),(2,32,145,0,4),(34,0,145,0,4),(1,0,178,0,4)]
def g179A : List (List Nat) := [[],[64]]
def g179D4 (j : Nat) : Nat := 0x5bd4940
def g179D5 (j : Nat) : Nat := 0x88401900ff40fd40fd20
def g179H5 (j : Nat) : Nat := 0x700000000
def g179D6 (j : Nat) : Nat := 0x5889f
def g179H6 (j : Nat) : Nat := 0x7a009001c00000c200800
def g179L : Nat → Packing
  | 4 => (1,2,2,0,0,0,0,g179D4)
  | 5 => (3,1,2,0,0,4,0,g179D5)
  | 6 => (1,0,2,0,0,0,0,g179D6)
  | _ => emptyPacking
def g179I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 6 1 1 g179H5
  | 6 => lookupWord 1 12 0 7 2 1 g179H6
  | _ => fun _ => none
def g179 : Forest := ⟨179,6,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P4_0 : block g179 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B4 : block g179 4 0 1=true := g179P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P5_0 : block g179 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B5 : block g179 5 0 3=true := g179P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P6_0 : block g179 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B6 : block g179 6 0 1=true := g179P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact g179B4
  · exact g179B5
  · exact g179B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K163) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 7 := lower_forest (g:=g179) (i:=0) (hints:=1048660) (before_sound K163 V163) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K163 7 [(179,[]),(358,[135,100,32]),(405,[129,81,33]),(453,[113,129,100,16,33,80]),(465,[81,133,97]),(468,[113,65,132,84,97,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V163 low179 (by decide +kernel)
def g403Y : Array (Bits × Bits) := #[(0x2421facb91e,0x41a9e380e),(0xfffffffffffffffffffffffffffc7c60152e95,0xfffffffffffffffffffffffffff00c68c52a11),(0x0,0x0),(0x0,0x0),(0x84387e1f652,0xf6bc561c610),(0x0,0x0),(0x0,0x0),(0xf83f86e43e8,0x1e0),(0xfffffffffffffffffffffffffffffc003bdc25,0xff3163ad404)]
def g403C : List ColumnInfo := [(17,0,386,0,4),(258,0,145,0,4)]
def g403A : List (List Nat) := [[],[129],[64],[16,132],[64,129],[128,16,65]]
def g403D4 (j : Nat) : Nat := 0x23f64547309bd89534426d6214d10
def g403D5 (j : Nat) : Nat := 0x208048080dc812000c6302faa3987bd4930bfa8a61fb304c2fea6885f94d10bea9a217c53443f260885bd4930
def g403H5 (j : Nat) : Nat := 0x8070800ac007840000000340000
def g403D6 (j : Nat) : Nat := 0x102ff30fd30fd10
def g403H6 (j : Nat) : Nat := 0x728002c0800000000000000000034c800000000000000000000000000000000000c0800198f0800000000000000000000000000000000000000000000000a14000000000000031700000000083000000000000000000000000000081313000000000000000034300000000000000001c000000000000000000000000000005220000000000000143f090000020
def g403D7 (j : Nat) : Nat := 0x105f
def g403H7 (j : Nat) : Nat := 0xb000052f5004c0007610800004e0000000000000000e200000000000000000056800000095003c800640000000
def g403L : Nat → Packing
  | 4 => (3,3,1,0,0,0,0,g403D4)
  | 5 => (10,2,1,0,0,5,0,g403D5)
  | 6 => (3,1,1,0,0,0,0,g403D6)
  | 7 => (1,0,1,0,0,0,0,g403D7)
  | _ => emptyPacking
def g403I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 12 0 9 2 3 g403H5
  | 6 => lookupWord 3 103 2 11 4 3 g403H6
  | 7 => lookupWord 2 43 0 9 2 3 g403H7
  | _ => fun _ => none
def g403 : Forest := ⟨403,7,fun i => g403Y[i]?.getD (0,0),g403C,g403A,g403L,g403I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403P4_0 : block g403 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g403B4 : block g403 4 0 3=true := g403P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403P5_0 : block g403 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403P5_1 : block g403 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g403B5 : block g403 5 0 10=true := (@block_merge g403 5 0 1 9 g403P5_0 g403P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403P6_0 : block g403 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g403B6 : block g403 6 0 3=true := g403P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403P7_0 : block g403 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g403B7 : block g403 7 0 1=true := g403P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403T : checkedTables g403 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g403 0 0 0 = true)
  · exact (rfl : block g403 1 0 0 = true)
  · exact (rfl : block g403 2 0 0 = true)
  · exact (rfl : block g403 3 0 0 = true)
  · exact g403B4
  · exact g403B5
  · exact g403B6
  · exact g403B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403G : graphValid g403 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low403 : Lower true (varsX 403) (graphGoal 403) 8 := lower_forest (g:=g403) (i:=0) (hints:=4294967412) (before_sound K179 V179) g403G g403T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K403 := extendKnown K179 8 [(403,[]),(454,[116,132,100,16,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V403 : Known true K403 := extend_ok (m:=403) V179 low403 (by decide +kernel)
def g423Y : Array (Bits × Bits) := #[(0x104210e305f3c7f8c046eb8,0x18733affc175c47af64eca8),(0xfffffffffffffffc0001f03fa1c780ffebe529,0xfffffffffffffff80000301101548234624409),(0x6183e3fc0c1f800f01acd96,0x638a63240edfe36f15ac594),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffe03fc000fe0000fff9cae1,0x7f6bfc968fea264cb998ae0),(0x0,0x0),(0x7ffc00000ffffff000713d8,0x638c40000e8a33800090350),(0x7ffffffff00000000143c46,0x1c719cdae1000400a043802)]
def g423C : List ColumnInfo := [(128,1,294,0,4),(37,0,386,0,4),(2,32,389,0,4),(256,4,163,0,4)]
def g423A : List (List Nat) := [[],[129,82],[32,135],[80,113],[32,113,80,129],[80,129,32,113]]
def g423D4 (j : Nat) : Nat := 0x4d9768c740
def g423D5 (j : Nat) : Nat := 0xbe58740f68c740bed9510fad4910
def g423H5 (j : Nat) : Nat := 0xf00000000000
def g423D6 (j : Nat) : Nat := 0x34088404500f6f07f507f681f910
def g423H6 (j : Nat) : Nat := 0x6008527735d0000091fa00000208000000
def g423D7 (j : Nat) : Nat := 0xe113f
def g423H7 (j : Nat) : Nat := 0x75330000000000000044801e1440023400000000144007000000000000068000000000000000000000041a5061
def g423L : Nat → Packing
  | 4 => (1,3,2,0,0,0,0,g423D4)
  | 5 => (4,2,2,0,0,0,0,g423D5)
  | 6 => (3,1,2,0,0,5,0,g423D6)
  | 7 => (1,0,2,0,0,0,0,g423D7)
  | _ => emptyPacking
def g423I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 8 1 3 g423H5
  | 6 => lookupWord 1 15 0 9 2 3 g423H6
  | 7 => lookupWord 2 43 0 9 2 3 g423H7
  | _ => fun _ => none
def g423 : Forest := ⟨423,7,fun i => g423Y[i]?.getD (0,0),g423C,g423A,g423L,g423I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g423P4_0 : block g423 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g423B4 : block g423 4 0 1=true := g423P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g423P5_0 : block g423 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g423B5 : block g423 5 0 4=true := g423P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g423P6_0 : block g423 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g423P6_2 : block g423 6 2 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g423B6 : block g423 6 0 3=true := (@block_merge g423 6 0 2 1 g423P6_0 g423P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g423P7_0 : block g423 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g423B7 : block g423 7 0 1=true := g423P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g423T : checkedTables g423 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g423 0 0 0 = true)
  · exact (rfl : block g423 1 0 0 = true)
  · exact (rfl : block g423 2 0 0 = true)
  · exact (rfl : block g423 3 0 0 = true)
  · exact g423B4
  · exact g423B5
  · exact g423B6
  · exact g423B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g423G : graphValid g423 (boundsBefore K403) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low423 : Lower true (varsX 423) (graphGoal 423) 8 := lower_forest (g:=g423) (i:=0) (hints:=4296018007) (before_sound K403 V403) g423G g423T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K423 := extendKnown K403 8 [(423,[]),(438,[135,32,64]),(442,[135,66,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V423 : Known true K423 := extend_ok (m:=423) V403 low423 (by decide +kernel)
def g469Y : Array (Bits × Bits) := #[(0xe1ac8cbc4e8be,0x41002110acb04a0ae),(0x0,0x0),(0xffffffffffffffffffffc07f01e11c38659075,0xffffffffffffffffffffc04f48a00910658031),(0x0,0x0),(0x43f19cc0448e6352,0x2965918cc0048a4250),(0x0,0x0),(0xffffffffffffffffffffcf8001e70c638b1f85,0x118001470463821f04),(0x3003fe0663a5719f08,0x100a6c622120611d00),(0x3ffc0006733e3a64e8,0x2e308010d28c1860c8)]
def g469C : List ColumnInfo := [(144,1,324,0,4),(320,4,145,0,4),(16,0,453,0,7),(64,0,405,0,7),(145,0,324,0,4),(4,0,465,0,7),(260,64,145,0,4),(1,0,468,0,7),(129,16,324,0,4)]
def g469A : List (List Nat) := [[],[98],[64],[64,98],[32,100,135],[96,32,66,135]]
def g469D5 (j : Nat) : Nat := 0x333dcf6254540
def g469D6 (j : Nat) : Nat := 0x2983881d69a09faeda8e81bbd8b5150377b12a2a05df7354520
def g469H6 (j : Nat) : Nat := 0xe0000000
def g469D7 (j : Nat) : Nat := 0x11080069c420020c080182005ae600663042c10a1185460c00ffd4740ffd4540ff54540ffd4520ff54520ff4c520bf59654bf59740be58054bb58b50bbd8940
def g469H7 (j : Nat) : Nat := 0x18000987880143d30008200000000000e880000000000000c5
def g469D8 (j : Nat) : Nat := 0x608034182010e5188201841006430402183598051566400a10057742fad09c5e202001fe54feaa7f153fea1fd50ffa07f503fa41fd10
def g469H8 (j : Nat) : Nat := 0x2180000000026800000000002c0800000000007c60000020b000000000000000000000000000000000000000001c408700171c000000000000018300000000600e30000005d202e72400000000000000000000000000000000000000712002ac8000000000000000000000782f440018c9c2a0a2100018a00000000000015
def g469D9 (j : Nat) : Nat := 0x753213f
def g469H9 (j : Nat) : Nat := 0x34a14a6ae86000622510003a80000000090b7140000038488c0000000130c004485822c2c0f2480e003418c40000000000000000000000905640e9a0000000000000000c125000000000000000000000000880
def g469L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g469D5)
  | 6 => (4,3,4,0,0,5,0,g469D6)
  | 7 => (11,2,4,0,0,7,0,g469D7)
  | 8 => (9,1,4,0,0,8,0,g469D8)
  | 9 => (1,0,4,0,0,0,0,g469D9)
  | _ => emptyPacking
def g469I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 8 0 8 1 3 g469H6
  | 7 => lookupWord 1 31 0 9 2 3 g469H7
  | 8 => lookupWord 4 99 3 11 4 3 g469H8
  | 9 => lookupWord 5 59 3 11 4 3 g469H9
  | _ => fun _ => none
def g469 : Forest := ⟨469,9,fun i => g469Y[i]?.getD (0,0),g469C,g469A,g469L,g469I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P5_0 : block g469 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g469B5 : block g469 5 0 1=true := g469P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P6_0 : block g469 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g469B6 : block g469 6 0 4=true := g469P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P7_0 : block g469 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P7_3 : block g469 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P7_5 : block g469 7 5 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g469B7 : block g469 7 0 11=true := (@block_merge g469 7 0 3 8 g469P7_0 (@block_merge g469 7 3 2 6 g469P7_3 g469P7_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P8_0 : block g469 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g469B8 : block g469 8 0 9=true := g469P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P9_0 : block g469 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g469B9 : block g469 9 0 1=true := g469P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469T : checkedTables g469 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g469 0 0 0 = true)
  · exact (rfl : block g469 1 0 0 = true)
  · exact (rfl : block g469 2 0 0 = true)
  · exact (rfl : block g469 3 0 0 = true)
  · exact (rfl : block g469 4 0 0 = true)
  · exact g469B5
  · exact g469B6
  · exact g469B7
  · exact g469B8
  · exact g469B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469G : graphValid g469 (boundsBefore K423) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low469 : Lower true (varsX 469) (graphGoal 469) 10 := lower_forest (g:=g469) (i:=0) (hints:=8623490564) (before_sound K423 V423) g469G g469T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K469 := extendKnown K423 10 [(469,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V469 : Known true K469 := extend_ok (m:=469) V423 low469 (by decide +kernel)
def g439Y : Array (Bits × Bits) := #[(0x80f7043027801e1dc38e3ff3170a6d0517c273,0x807745002180061442aeaad247085541174063),(0xe31807e0784023e23c7fe60cecdfd09958387b,0x1180080004002220472260406db000908105b),(0x1c1ff840407c3c03c070380882110f96a160fd,0x2d1b08854d7dbf8fd47a7e08c2910f968120f9),(0x0,0x0),(0x1fe0007f807fc003ff803ff512a62e10aa1e9a,0x1f80a2f9904ec002bd41552530962a10a81e18),(0xe000007fff800003ffffc009e500f3dcc71fa5,0xfac6c77fffabb11dfb8dd989e100f3d4c70fa4),(0x0,0x0),(0x7ffffffffc0000000201b92166cca5c0,0x200000064e3139c9000000080020008640a180),(0xffffff80000000000000000c38443263374f0c,0xd2e4f77830020010220181c139047060364e04)]
def g439C : List ColumnInfo := [(258,36,145,0,4),(36,0,403,0,8),(16,0,423,0,8),(144,1,294,0,4),(2,32,405,0,7),(1,0,438,0,8),(256,4,179,0,7),(53,0,386,0,4),(129,16,294,0,4),(3,32,404,0,4),(262,32,145,0,4),(290,4,145,0,4),(257,4,178,0,4),(294,0,145,0,4),(145,0,294,0,4),(35,0,404,0,4)]
def g439A : List (List Nat) := [[],[64],[129,82],[64,129,82]]
def g439D5 (j : Nat) : Nat := 0x30cc96e0d725c151a2b2999261e41d421ada961f6290750a666a3701ce4154318d98dcf6290550
def g439D6 (j : Nat) : Nat := 0x34a440030a0704002b1000b441e205081e5b1000c001000170025800000221c81818000018197000013800000000180000000000000100000000010100010000c8c800000000000050001818031eeedc0acaa8db925972d4551a764b2e5b82a34ec965c97054739f06b92e0a8d67e4d805d6419cfc9b0132c838bf9661d6590697f2cbaacb20f0fe597559641a5ecbccab2c83c3d759956590637b2fc02cb20e6b66175d8a41cd6c2aebb14834ec9660971d42bcf22c12e3a8579e45525c7508dfcb30f20ea19ad9261e41d4237b30bb483a862f6197690750cd6c3ae520ea13ad98d8a41d4335b0fb1483a866b61d5290750aecc8ee039aa19cf73e055254333b0db9c82a86676177390550ecdb80e720aa13ad98d8a41543b1ee7b1482a8763dcd5290550ce7c2ee690aa1dcb701cd215427733120ea0a846f6627590530addc82eb20a613ad98d8a414c2bd720baa42987c654e4154130fa4a9a42a82618ef92618754423db313aec488573e4d75d89108f6cc0ebb12214ed961d762442b9b263aec4885b92598254510bb2caec4a8a214ac966097590635b30baec520e4b61575d8a41
def g439H6 (j : Nat) : Nat := 0x8080000000000000a01240c0002
def g439D7 (j : Nat) : Nat := 0xb041f10018300131002830e0e4e2152220034200212d59064810f960801003108a00084e5820040f94007528800c641001a564156a9443ad46a079710595104881c404007881c43400708101c42c803887480800c080080070838009902c80800c00308565620048a0020290348005c41e40faf2a2004a2002100f880105000b080080030400597914a22710615107583a3502a352b060f8840c3840f2710f8e4061f5e4003a4446a7990da0f3ce79cd89969da5bc9c23446a4446d23446a3011a2344348696487d0a96042a49c9da0b1641f29d9fa24171e9d886bd977ce8d20b8f68a9d9ba3595f89d9a29d664875998b245f8d157e1d664875998b245f8bf17e3095f8bf17e3093acbf17e2fc5c27596a2d44ec9d9602a55143e53b2764c493920a2621a848f81dc392758e49b53345e0b21422344b88d11a2344688d10d1f235c618a81281e43285106c06c0d800df7815d951bf78159551f778159551ef77658551ef56558551bf586d4551f7565d4551fe572d4551ded72dc1519fd86dc151bdf835c151ded725c151dbf865d641dbd865d641dbf805d641dbd805d641dbd8799641dbd7599641bbd8099641dbd8759641dbd7559641ebe6559641bbf8059641bef815cb50bef8154b50ded725c7509ff865c750ded825c750ded525c7509fd8758750df57158750bbd8790750bbd8690750dbd7690750bbd8590750dbd7390750f3f5390750fad7290750faf6290750fad5290750bef8748750bef8548750ded7348750f6f5348750bef81549509fd86dc550ddf7358550ddf7354550bbd8690550dbf7690550bbd8590550dbf7390550f9f7390550f9c7390550f3f5390550f3d5390550faf6290550fad5290550bef8548550def7348550fcf7348550fcc7348550f6f5348550f6d5348550bf981d4150fba41d4150fe921d41509fd819d530bef8154930bbd8690530bbd8590530dbe7590530dbd7590530faf6290530fad5290530bef8548530dee7548530ded7548530fba4154130fe921541309fd85dd9109fd869d5109ff865d5109fd861d5109ff865cd10bed85d8910def75d8910dee75d8910ded75d8910dec75d8910def73d8910ded73d8910df77654510f756554510fe58254510fe76254510fe7624c510bfb8654110dfb7654110feb62541109df835c351aec865c951be78154951e7565585519bf865d641dad825d6419bd8799641d3d75996419bd8759641cbd7659641d3d7559641dad75d8a41dad7554a419bd8790750ddb701cd50dcf7354950d9f7390550dcf73485509fb805d530f5953541309df835d5108fd861d5109dd831d5109ad87d8a41
def g439H7 (j : Nat) : Nat := 0x61000000000048c000000000000000000000000000000003000000000000000dc3000000000000000000000000307000000000f2b909519712629a2171f916e1a000000f8d00000000000000000000000000035e000000000000000000a97a14b34000000000000000000000000000000000000f3200000000070c0000000000000000000000000000006720000000000008afe00000e28000000000000d2600060a000000a0d000000000000000000902000000d4d000000000c2f000000000000000000000000000d17d8f000c1d00000000000000039b00000010500000032e000000000000656000000000000000624308b2d50e000000b25a04000000000000000000000000000873e27520000e13000000000522000b35000000000000f11000000000000230000000000000000000000e3331e00000000078b00000000f00070100000000000000000034f000000000d31000000144215000000000000000000000000000000c83000000123000000d2a00000000091800000000000000000000000000000000032c31b19d51c000000000d9200000000020b00000000000000090650112100018011
def g439D8 (j : Nat) : Nat := 0x3c400c0564c431492034959311d60d4c440d65310052569430315078885941c31885a58831d41e25940c71568941c31713c00c42520081c3188c430040c00910c00ca0430040b12240c5203c401310022b5c910052110c0108103c401711030c0c640c48470034b12031121c30c04560c41e50115831a5c88003c541f202545414ac919545860c81c30b12031081c30e51c30c80c70e58912160c6014c481008919541518a5516162c430e20310c43b10c38875831220141c48945871070c223228b2450400c30310c91009310c4942024c43187c400c91484b12431520241c3165472004944c431084841c31400c24b19031010c00e1d72004135ca1005d72003075c80121035c8a176d080f1161621617ba1617ba0d2011f99f09e49da1ce1c51bc1b49aa0301a299e19819098798018018017b97296b16215c15494e94e94714113992f12311a10f9099020fc0f60f00e58de0d50cc0c60be8b88b10a98a209d89488e88707f87506c06305a05283004b04203d83603002882881f8198120090003febb6a3ffdd951ffaeca8ffe65547feb2aa3ffdc151ffae0a8ffd71d43feb0ea1ff54750ffac2a87fd51543feb0a61ff54530ffaca887fd63442ffbb6a37f5db51efccba8fed72d47f6a96a37f5c351bfeeca8dfd76547bf32aa3df59551fdae4a8fed52547fab0aa3fdd4551bfee0a8fbe65907deb2c837f5cf50efea7a87ed72d43f6a96a17f5c750f7c83a87ed21d42ffb9aa1f7dcd50fb8e6a877f53543bea9aa1fb54950bfee2a87be41543f690aa1fed4150bfcea985fd754c3f6a9261ef90530fda42987f9504c2ffbb2217f5d910bfeea885fe75442febaa217f1d510bfee6885fd73443f7b1221fb54910feaa2887f531443fcb0221fe54110f5aa8a95ef7154adebb4836f5d641f5ec520fad52906f7baa4377dcd50
def g439H8 (j : Nat) : Nat := (if j<1 then 0x1f3c00000000000000004b57a70000fa880004520000000000001a77000000000000000000000006110000000000000000000000060e000748c00000000000000000000000000001a6700014f8000000000000134c000baebc9ac3c0000000000000000000000000000050500034ac0000006a1400000000000018ae000000000000193f000068c000000000000000005000000000000000000c19a760000005850000000000000000000000000000012086618002cec000000000000071a000000000106800000000000000005834000000e1d7898000000000000000000000000020720000003870000000000000283400000000000000000000000000000000000000000000000004d62654168000de6000d2e80014cc000000000385800000c80000000000000000d8be434ad0000001e5b00000000000000006af4000000000000000000062cbd5c0000000000000000000000383000000000000000000000000000000a3600000000000000000003ca80000000000846000c1a800000000000000000000000000000000000c1100000006dbf9d000000000000000000900000005364000000000389146344000000000000000000000000000000000000000000000000000000000000da8000000000165b012d0af8159e000000000000000000000000000000000000000186200000000000000000000000000000000000074a022800000000000000028c600000050f40006340000000001071000000345e00000000000000000000000000000000000000000000000000000cb0000000000000000000006fc160003b24001c18d1d8000000000000000000000000000000000000000000690000000738c0000000000000000000000030a2f225200052b400000000029b44c203300000000000000000001158000000000349c000a1700000000000000000001e25d2219e4000000d1c492dc600000004c21c7800000069600000490000000000345ebd39444e80000005471f3800049a00015a4673f3700000000000000000001c5f92169e3006000000000008c0000004d400000000000001a98000a1f000000000000000000000000005b3d1da20b0000003aea000c4e80000000000000000000000600d11c000000000000084e00000035a4a4883f0000000001e0700000006720000000000000000903000001e0001998000000000000000000000000000000000000000003a88000000000000000050480008000000000001e584c10000003ab084f000000000000000000000000000000000000000000000000000000000000000000000000001a72000000000000000019a80000001a37dec0000000000000001a5a000000000000000000000000000000000000000402780240003001041081a010c32c0 else 0x35d2000000000000000093d8000000000000551d8b80000005104000000000000000066400000000000000007c1c000000000150000000003a800000000000000000000000000000000000b37800000161d00000000000000000000000000008000182e000376080905000071000000000000000000000000000000000000000000000000003d2000385569e000000000000000018ac00053d0005c80000000000297800000008671a565e000000000000000000021b000000000000000000000006598000000c098000000000000759400000000000030f4000000000000000092631c00000000005b9604200052a800000000090ffe7800051e0000002c360000000000000000000694c000000b25013400000000000000002040000002c640002970000001f180000000000000d300000000)
def g439D9 (j : Nat) : Nat := 0x312b19006320e020e239ab204483188895a851c4915a8828e238876a1c54c80588c83d6400985ac80120a1ac886169d2580b394a862e8f83e00ff587ff51ff547ff50ff543fd30ff443ed52ef907ed21
def g439H9 (j : Nat) : Nat := (if j<1 then 0x6138000000000000000000000000000000012b80000000000000000000000000000000000000000000003c0a000b088003805a8b0000002416000000000000000000000000000000000000000000000692000000000000000000000048000000000c4b0000000000302000000000060b00000002150000000000000000000000003f0000000000918000000000000000000000000000000000000000000000385e00000000034440000000000000000000000000000000000000000000004900000000000000000000000000000000005073efc000000000000102ea340000000000000f18000308243b0000000000000615800000000000060640000000000000000346000000000000000000000000000000000000000000000000000000000000000000000000001720000000061cd4a000000000000000000000000000000000000000794000000000000000000000000000000000000000000000000000000015840000000000000000000000000000000024a4000000000000000009d000000000160600000000010c300000000014380000000001f0d00000000000008500000000000c03d0b4000000000380414e20a0000000000000000000000000000000000000000000002e3c00000000000000000000000000000025000000000000000000000000000000000000000000000000000000000000000003070084000000000000132d0000000000000000000124f23d0000002c3a00000000000000000000000c8600000000000000000000000000000000000000000000028f00006200000000000000922000000163e000000000000000a00000000000000000000000000000104c0000000000000000000000308a0008a000000000001190000000000c14b2480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000012300000000000000000000000000000000000000000000003110000001c540000000000042a9400000000000000000003e6a0000000000000000000000000000000038a0000000000000000191700000000000000000000000000000000000000000064c4000000000104c00000095100000000000000000000000000000000000000000000000000000000000e1800000000000000004093c100000005894000b8d000000000001b0000003866000000000341bec800000000000000000001424000f84000000000000000034960000000000000000000000000123500000000000000000003e840000000000000b1f00000000000000000000001231057d31c0000000000000000000000000000000029f8000000000000000386c00000000410405082050090a1 else 0x18004c4c24c230000000406000000000024f3d1000004c0000000000000000188c001a4df956a9800000000000000014910002b14000000000000000052e0000000000000000000000000055480000000000000000001a1f00060e8000000000000000000011b80000000000001474000000000000000000000000000000000000000000000000000345c0000000000000000000000000000000000000000000000000000000000000343c0001080000000000a1c8002e4cc0300000000000000000000000000000000000000000000000000000000000000000000000183544748c80038580000000000224000000083c00000000)
def g439D10 (j : Nat) : Nat := 0xca8422ff
def g439H10 (j : Nat) : Nat := 0x34900084f9e0100000e1c009080000000000000015600015fa000003c5a20000000000000bcc00000000000000000682e1600000020338a6351a93244
def g439L : Nat → Packing
  | 5 => (5,5,4,0,0,0,0,g439D5)
  | 6 => (54,4,4,0,0,8,0,g439D6)
  | 7 => (124,3,4,0,0,11,0,g439D7)
  | 8 => (78,2,4,0,0,12,0,g439D8)
  | 9 => (10,1,4,0,0,9,0,g439D9)
  | 10 => (1,0,4,0,0,0,0,g439D10)
  | _ => emptyPacking
def g439I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 12 0 9 3 2 g439H6
  | 7 => lookupWord 14 295 4 12 6 2 g439H7
  | 8 => lookupWord 40 811 3 13 7 2 g439H8
  | 9 => lookupWord 25 775 3 13 7 2 g439H9
  | 10 => lookupWord 4 47 3 10 4 2 g439H10
  | _ => fun _ => none
def g439 : Forest := ⟨439,10,fun i => g439Y[i]?.getD (0,0),g439C,g439A,g439L,g439I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P5_0 : block g439 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B5 : block g439 5 0 5=true := g439P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P6_0 : block g439 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P6_3 : block g439 6 3 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P6_51 : block g439 6 51 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B6 : block g439 6 0 54=true := (@block_merge g439 6 0 3 51 g439P6_0 (@block_merge g439 6 3 48 3 g439P6_3 g439P6_51))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P7_0 : block g439 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P7_1 : block g439 7 1 23=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P7_24 : block g439 7 24 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P7_72 : block g439 7 72 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P7_120 : block g439 7 120 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B7 : block g439 7 0 124=true := (@block_merge g439 7 0 24 100 (@block_merge g439 7 0 1 23 g439P7_0 g439P7_1) (@block_merge g439 7 24 48 52 g439P7_24 (@block_merge g439 7 72 48 4 g439P7_72 g439P7_120)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P8_0 : block g439 8 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P8_8 : block g439 8 8 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P8_56 : block g439 8 56 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P8_62 : block g439 8 62 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B8 : block g439 8 0 78=true := (@block_merge g439 8 0 56 22 (@block_merge g439 8 0 8 48 g439P8_0 g439P8_8) (@block_merge g439 8 56 6 16 g439P8_56 g439P8_62))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P9_0 : block g439 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P9_3 : block g439 9 3 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B9 : block g439 9 0 10=true := (@block_merge g439 9 0 3 7 g439P9_0 g439P9_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P10_0 : block g439 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B10 : block g439 10 0 1=true := g439P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439T : checkedTables g439 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g439 0 0 0 = true)
  · exact (rfl : block g439 1 0 0 = true)
  · exact (rfl : block g439 2 0 0 = true)
  · exact (rfl : block g439 3 0 0 = true)
  · exact (rfl : block g439 4 0 0 = true)
  · exact g439B5
  · exact g439B6
  · exact g439B7
  · exact g439B8
  · exact g439B9
  · exact g439B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439G : graphValid g439 (boundsBefore K469) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low439 : Lower true (varsX 439) (graphGoal 439) 11 := lower_forest (g:=g439) (i:=0) (hints:=4296018004) (before_sound K469 V469) g439G g439T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K439 := extendKnown K469 11 [(439,[]),(443,[50]),(487,[135,100,32]),(499,[98]),(502,[135,66,32,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V439 : Known true K439 := extend_ok (m:=439) V469 low439 (by decide +kernel)
def g471Y : Array (Bits × Bits) := #[(0x10040101920630fc40ffcd90d1956838ff0,0x503018006109c482525a8f38428307b0),(0x1879f21c0bc087801c2aa3bb14469e2aa,0x1c6937140e0ad78a9c2083bb14409e222),(0x5e00600c0f07ffe01544a138f046e2e,0x1004800204c030593e00755b030f042a2a),(0x0,0x0),(0xfffe060601c7ff00ff800ffd847441243ae063,0x872749c7e110f6102dad8430412438e042),(0x0,0x0),(0xffff07f801f80000fffff00218203470cdd017,0xffff23c801790808cfa6c10208203070c9d005),(0xfffff80001ffffff0000000421e9e97a55390d,0xffff380000000e0e000300002140001944180d),(0x1fffffe00000000000007ceb206c9ba17d0,0xc4316c84b0100000003582804c803205d0)]
def g471C : List ColumnInfo := [(146,1,324,0,4),(322,4,145,0,4),(68,0,403,0,8),(17,0,454,0,8),(131,16,324,0,4),(262,64,145,0,4),(2,0,469,0,10),(85,0,386,0,4),(18,0,453,0,7),(66,0,405,0,7)]
def g471A : List (List Nat) := [[],[98],[64],[64,98],[32,100,135],[96,32,66,135]]
def g471D5 (j : Nat) : Nat := 0x1865e939360980dc565
def g471D6 (j : Nat) : Nat := 0x81c306af7bdef7bdef7bdef7bdef7bde0cd5e1793603715971d793e0980dc565c75e4d826037159719f94e0d725c165a6de9172e0570597477646447559560d1d591911d565582576a91d78159560a6de9182e0576d429b7a464b815db50a3d684865d972d421f7a166287d8b5087de8597a1952d428f5a12197654b50967e9192d97735421f7a166376d8950a75e8585dcf6254299fa461b7354950a75e8586dcd5254299da421b7354950a7568486dcd525423f3a166362d4150
def g471H6 (j : Nat) : Nat := 0xc0000000
def g471D7 (j : Nat) : Nat := (if j<1 then 0x481e3056410407000d481c3010b0c1000508140004301040004200078f482030c0021973864561915b8032194a02d281905b54320b65064402b61880402b100ac560b158ac56b80c9ecf6190c82c562b158ac162b0c82c561905ab4321905a9816190582c3219058ac569b058ad042b0c82c560b158ad360b3da50320b0ca09048905a09047b0c82cbc7b3d9ecf60b059d0ca5e29930984c158ac560b058804019058ac56201006482191906456200c82c320e0582c00dbbc8b0fb2ccbe7786e1771597cef0b32ee2b2f9ddd665dc565dbbc2f01b8acb77795603715976ef0ac06e2b2df5e4d80dc565afacb701b8acb9f782e03715973ef04c06e2b2e7d60980dc565dafb2f06b82cb9df83dc9705973bf06b92e0b2eddd97815c165cfbb9702b82cb9f572e05705977af07b8ae0b2e7de478759465cfbc3f02b28cb9f797e0565197aef23c3aca32f5de5f8159465ebbc3f02b28cb9f79859571197be722b2ae032f75e45655cf60abf4c0eab2ac1c7f641d5655838fac83aacab075ddd78159560eba3af02b2ac19f497e0565582d7f28c12cab05bde458259560e7a4bf02b2ac1e7795e0565583cef0bc0acab067de4585dc960cfac890ea92c1e7791595525833ef22c3ceda84efe51829db50cfbc8b0b3b6a19f797e0576d433ecedc0aeda856fe51825db50afbc8b04bb6a19f782e0576d433eb05c0aeda867de57815db50cfacaf02bb6a19f792e0576d433eb25c0aeda857de4587d9750cfbc8b0fb2ea15f7915db65d4277f28c16cba867de1f8159750cfbcbf02b2ea13bd9421972d427eb22432e5a863fe19765cb50c7e432ecb96a15f7915d972d423fb3143ec5a857de4587d8b50cfbc8b0fb16a11ff9761762d427ef22c2ec5a847f65e8654b509deca10ca96a13f59121952d431ff0cbb2a5a863f2197654b50afbc8aeca96a13bf9460b65542bbb25b2ee6a8757d9565dcd50aefc92cbb9aa1dd79159773542bbf26c3ec4a857de4587d89508fecc6edb12a11ff985db62542bbf26bb6c4a857de4576d89509fbc8b0bb12a19dd85dcf625433bf0bb9ac4a8767e1373589509dfca30ca92a13f7916195254277b28432a4a84fd6448654950cefc36e6a92a19de86dcd525433bb0db9aa4a867721b7354950eaeb2ee6a92a17bb94589605437e722c36a0a84fe66362d4150bddca2c5a82a15f591a1d654833ed0fc0aca9067d21f8159520cfb4bf02b2a419f497e05654826ef22c3ecb32e9de1b85dc565aebc9b01b8acb9d783dc5705972ef23c3aca32e5de1f81594658fbcc2cab88cb9779859571196be722b2ae032f3ce45655c065aebc8acab9ec1cd79159573d82aeb223aacab047de4585dc9608fac890ea92c11f79161e76d423ef22c2ceda847de4587d97508fbc8b0fb16a15d7915977354333f09b9ac4a84fce4586d4150 else 0xd604101b20009c8142b60414042057209c81040008c8100040b)
def g471H7 (j : Nat) : Nat := 0x2ccc000000001038000000000000000000000000000000003400002415c19c1182000305000304680c000003042c2400000000001d04c00083da00830000000000000000008001454000000000000000a4c000000000000000000c040000000000010340038d0000000000003048000003e4400000000000000000000342c00000202a15
def g471D8 (j : Nat) : Nat := (if j<1 then 0x54d8f100022a6098c08014284020040b8c08010205038c00b8c0010f1800b1d2000446dc8006db900c6226c61408014001ed8e90b8c2000d9000bb0401484a4002860026c1420002284000430214006140800db00e58c4e400202002000420000008157f362f7d17bd7a278776574a0007215802027066e46a162f6a162f6d06b50140146a101462f6a162f68d66b65753d63c62f61460e5ec5d15bd5a25655805650ec54a53d5294d84ec50e4d84ec1364d84bd49b47945743c42140d0000000000af0000003f93e53c33a137f3563340283192f00002c709400000000029e27c00025a05e2312162020000001e005e0001c51a305e05e17a1511361221221001000ec0d80000000af00002809400009400000001400001400000000007900005e02800002803c014000014000028028014000000ff785dc565ff665dc565ff780dc565ff580dc565f7f65dc165dff72dc165ff771dc165f7f655c165dff725c165dfd725c165ff7715c165dff8759465ff78159465ff78159760ff78159560eff8259560efd8259560bfd829db50dfe765db50bff825db50ff7815db50dff825db50dfd825db50dfd87d9750dfd76d9750bfd82d9750dff8759750f7f6559750bff8259750ff78159750bff865cb50bfc865cb50dfd765cb50dfe87d8b50dfd87d8b50bfd85d8b50bff8654b50bfe8654b50bfc8654b50dfd7654b50f7d6554b50bfd82d9550f7f6559550bff8259550ff78159550dfe87d8950dfd87d8950dff76d8950dfd76d8950bfd85d8950fdf73d8950ff980d8950bff8558950fdf7358950bff8654950bfe8654950bfd8654950bfc8654950f7d6554950ffb6258150ff96258150ffb62d4150ff962d4150dfe8759520dfc8759520ff78159520df7815da65b7d87d9665e7f7599565f7785dc565ef665dc565df785dc565df665dc565df780dc565df580dc565df771dc165bdf835c165bf7815c165df7715c1659ff8759465bf78159465d7f8759465f778159465df5655c465df9655c065bf78159760ef78159760ddd655cf60d7f7559560d7c7559560bf78159560e7f8559560ef781595609fd85dc9609fc8754960e7d65549609fd879db509fd859db50bf7815db50df7815db509fd87d97509ff8759750bf781597509fd87d8b50bf78159550ddf65dcd50ddd65dcd50ddf73d8950ddf7358950ddf7354950bf986d41509fd861d520bf781595209f7815da659f5819d6659df835c26597f8759465d76655c465d75655c465dea729c065df1719c065dda735c065dd9735c065dea725c065de9725c065df1715c065cfb655c065cf9655c065cdf655cf60cdd655cf609dd831d5609ed821d5609f5811d5609f7815db509dd831db509ed821db509f5811db509dd839d9509df835d9509f7815d9509f887581509bd849d5209df835d520 else 0x8cc00610033ac21300059094c004100d30c3d3021d30005908029840d300c78808b8d9010c2b2c60046404200059060590548084100920021202152000430008700043002010e004001c086480058c0070c26300044c600206129280e90349405491810d1d208004018c224031878c9040026324002081e1b2022436414386019070d904580845800458200022160a0400815981002040acc08014281a6004a7c8006169810800)
def g471H8 (j : Nat) : Nat := (if j<1 then 0x626a000000030210000000000000000000000000000000000000000000000001b1a40000000000000000000000000000000000000000000000000000000000000000000000000000004040607a00000000000c0380001c0a800000000000000000080d2000000000000000a1440000000000000000000000a874000388fb8340000000000000000001e5e0000000000000002a2480000000000000000000000000000000000000000000000005a760000427000000000000000483f000000000000000504a0002c3500000000000283b0042000000000000000000000000000000d05e00000000000804e0002837000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002e14000010a570ac0000000604c00000000000702e00000005922000000000007c3b000000000000000408e401c000000000000003d06984c709e0000000000000000000000000000000000000000062ea000000000000000000000060310000000000000000000a1f0000000000000000000000000000000000000000f400000000000000000000000000000000000000000c0e60000000000000000000000000000000000000000082f4000000000000000000000000000000415c0000000a0400002c368000000000000007830784e0000000703e0000000000000000000000000000000000000000000000001416c000000000000000000000000000000000000000000001a0df8390000000000000000000000000000001a1800000000000000000000000000e0be0001c030000000000000000000000000000004172000001500000000000000000000000000000032067152000000000000000000185354998000000060d6a3c8000000000000000000000154f40000000e0e200000000000000181700005865000000000000000000000000000000000000000000000000000000002a5e70c4000000000000000000303c80000000000000050140000000261300000000000000000000000000303d8000000000000000000000000010bc8000000041ac000000000000000000381f00000000000500e60040000000000000000000000195a000181774228000000000000000000487a000000000000000000263a80000000000102c00000000c4b400000000000000000000000000000000000000000000000000000000000000000000000000201480000000000000000007a4820d8000000000000001e39000000000000000000000000001e9b000000000001420800000000000000000070d00001833800000000000000000060f0000000000007076000000000000000000000000000000000104000000700002c000c else (if j<2 then 0xb088000000000000000000000000000000000000000000000000100680000000000000000000000000000000000000000000060720000000043f80000000000041600000000000000000000000000000000000000000000000000000000000000005044000000000000001e1bc000000000000003c0e800000000000000380f0000c1f80006055000000000000000000000000000000000000000000000000000012b068611048000343a000000000000000000000000000000000000000000000000000000001c150000000000000000000000000000000000000000014198000000000000000000000000000005860000000009348000000000000000000000000000002137d09400000000000800200000000000c4fa00000000000f839616800000000000000000000000000000240f000000000000000000040560000000000000000000000000000000000409800000000000000000000000000000285e000000000000000000000000000000d0fa000000000000000000000078090000000000000000000000000000001242000000000000000208c0000000202c00038028000a03214ac00038110000000000000000000000000000000000000180c000000000000000000092ec0000000000020860000000383800000000000000000000000000000000000000824800000000000000000000002120000000072a2000000060040000012c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004d00000000000000000000002e2e80000000000000000000001718400000000000000000000000001404800000000001949c00000001848000000000000000000000000000000000000000000000a20461b00000000000000000000001f078000000000000000000000000000003041000000000000000000000000000000483200000002cb9a86300000000000000000000003808000000002020000486400000000000606c0000000000000000000000000000000000000000000000001402b800683c40cc000000000000000000000000000000000000000000000000000000000000a0b800000000001020c0000000000000000000000000000000000000000000000000000000000000003425000000036300000000000000001d7900000003a9300000001600c00000000000000000000000000000000000000000602c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006837000000000000000000000000000000307400000000000000000000000000000000000000000000000000000000000014e8000405900000000000000000000001c2815690000000000005490000 else 0x141d400000000001e0b6038000000000000000601b000000000000000000000000000000000000008a7000000000000000000000000000000501a00000000000000000000000000000000000000000000000000000000000000016030000392cea1a5576c400000000000000000000ba4a00000001561b0ee00000000000000000000000000528400000000000000161580000000000000000004c0d00000000000000000000000000205354ff811b014000000000000000))
def g471D9 (j : Nat) : Nat := 0x5c81004141c930055850444f20079a38800458c4001105ca3040141c800c58c1c801414800f60018d21411d20048d2004104d810128c6144001da34878c04841070010f61440011460c2001140042084001112c800c5053c801450400c40010c60010c40400f60c00440c50401231410041050401058c10c6142043c801c48c10048f20030c1003141c801008c10c5040cb68c62020011128c10c5001c841451012320060c4c801011021430720050f20030070820010c30010c30401c40810035b3c831440011361320047c828b1e618bd1712d335ab04151f21fead47faa352ea153b2674ce9491d22b43e834fd9f23c6234eb81e38a6e4289ad342618ca9862ee5a08715921c5343913524c4687990e1fe3cc6f0cf1862c42289c108234420720cc1742884506c0a80f00f01e03c003ffb2ccbff5ca65ffccab2fff70597feb82cbff59465ffacbb07ff65583feb2ac1ffdc960ffaa4b07fe76d43febb6a1ffd9750ffacba87fd72d43ffb16a1ff54b50ffecaa87fd65543ffb12a1ff58950ffaa4a87fd65482febb4cb7f9d665efecb32dfd72996feb84cbbf99565feee2b2dff70596ff3a8cbdf99465efaca32ff571197fd380cb7f5c065ff2e032dfe75d82febaec1bfd9760dfacbb07dd73d82feb96c17fdd560bf8eab06ff655837eb2ac17fdc960ff6c0b05ff76d42ff3b6a17f5db50bf8eda85fd72d42ffbb2a17f9d950bfaeca85fc76543efb9aa17fdc950ff2c0a87fb50542ffbaa417f9d520bfaea905fc75483fcb02417ddc565beae232df970196eeb9ec177dcd50
def g471H9 (j : Nat) : Nat := (if j<1 then 0x3175000000400000000000095ce69c00000000a109c22000000000000000058c308d15a00000000000060976458000000000000000000d11200000000000000000000005458000000000000000000000000000000000000000000000000000000000000aafc00000007475000000000000000000030600000000f8d834e8000000000000000000000000000000000000000000000000198500000000000000000000000000000000000000000000000ae00000000000000000038267029000074a0000000000016844000000000001510000003700000000000000000000002a31c96700000000000317900000000000745d0000e0b4000505a0a200002c058000000000000000000000000020b1946900000000410cc1100000000000000000000001c398000000130580000000000000000000000d06a0000000388600000001c0f00000000000000014590000d590d4080000000000000000000000000000000000001555400052450000000000020600000000000040410001d4e40000000991a0002243000000000000000000092b800020145d0f000000000000000000000000000000311c0000000703350f8c0e8000181f00000000000000000000000000000000000000000602a60140000000000000000001c00800020700000000000048ac00000000000000000000007d6a0000000000000000000000000000000000614969300000000000000028660000000041180000000000000000000000000000000000000000000020270000000000000000000c16c00000000000000000000000000000000000000000222000000000000000142400000000000000000000000000000028550000f2004bf800000000000a2d0000000000020aa000028cdea00000000000000003eb9108500018536818800000008010e243877c05e75ac00000000001f514000000000002558000607000000000000000000000003424e444000000000000000000000000000000b2b20000000000000000000000182c21040000000000000000000000000000000000000000000000000000000000000000281203600000003c8b800000000000000000000000000000000000014a10e898000000000000000000b91c00000000d58000000000002015000000000003c650000000340e8000309c00000007d606b10a18d028d8840000000000000000000000000000000000f1c40000000000000000000000347400000000000000000000000c32000000000000000000000024af00000000000000000000000000000000000001644c0000a710001a18400041530000cd3400000000001e448945800000000002e0c8c3a000000006b18000000000000000000000048e400000000000b57400800010943014084c8211010280013604240008400228f90 else (if j<2 then 0x1311c000000050d0000000000000000000000000000000000000041660001019400025439081a162803b87600000000000000000000003c0cac28000000000000000000001b40000a02000101f86af0000000000000000000347000000000000000000000000000442a00000000000000181400000000ab01d16f6b28000f451c0ac00000000000000118f0000f8c4091000000000001f00800000000000d1f80000000000000000002965f25e00000007262909e000180794130000000000000000000000000000000000000080bd0180000606c00020050001c48e4120000607e00000000000000000000000000a2f000014390000000000000000000b0b901bc00000140001a000000000000000000000758700000000440800050ce00006ab8000000000000000000e08a0000000000088da00000006c840000000390b0000000049340000000000000000000000facdc04800000000000000000000000001c04e21cf03418d400000000000000000000002288000000000007a32000000000000000000000020458000000000012990000a2f6114d046800000000000000000020f2000000000000000000000000000000b458000148a0001f5b400000000001b5000000000000134458320000000000000000000000000000000000000000000000189000050f3cbe80000000000000000000000000000d000000000000000000018e4000000000000000000000000000000000163580000000000000000000244000000009510000000000000000001e1d12b8dc49f0d60001c13781c000011780000d8b0000000000000000000000000000000000000000000000001f19080b00000000310c0006c450000000000000000000715400000000000000000000000000000000000000000000000000001aa800000000000000000002288000000000024b4800000000000000000000000000000205400000002026800000000002c8380000000000000000000000000000000000000c1e2d460000000000000000000000000000000000000000000000000fb03461800000000001c04669a00000001b21c000585e90e20000000000000000003a13000000000000000000000000000000500ea0a600035130000000000000000000000000000000000000000000000000000000000000000000160200000000000015fc000253332a000000000000000000000000000000000000000000000121d5ab100000001c1a800000000000000000000000000000000000009b0c0000000000090be00c800000000000000001c8000000000000000000000000000000000000000000000000000191000000000c0fa0000000000000002878000000000000000000000000000000000205900000000000000000000000000000000000000d2180060000 else 0x2a2b80000000000340630030001f148000583c00000000000307b604001a40003c46000125f9c41800000000000000000000000000000315f000000000000000108e0000000000000000000000000040040000000490b000165b80007c10000000000000000000000000000000f118000000000000000000000041720001c228000000000004128000000000000000000000000000000000000000000000000487a00000001825800070120002640f880e0ba000241800000001e15800000000000000000000000001a1fc0000000000000000000000000000000000000000000000000000000000000005556f08781b1090800000000002a07800000000000000482200000002ebaac3492a5d61000000000001a8d3e280000000000020ab800000000000000000000000000000511e000000016c50000000000030170000107a0000000000000000000000000000000002a3034730000000000000000000000000000000000000323fd468000010cea2a000000000002043c55a00000000000003e80c400ec0000000000000000000422000000000000000000000000000000000000000000000001a0003eb4800000000000a4400000001d230000000084800000c37000038700000000))
def g471D10 (j : Nat) : Nat := 0x24ed200b39583288961c80120b6900611ad200c4b486010969006282c21845d9c49672583e1f00ff997fd65ff197ff60ff583ff50ff543fd20
def g471H10 (j : Nat) : Nat := 0x1833121ac4a00000008046070000000000000000000001c1f8577c0d0001e060001e00343200000000000000c91e254904081e092000061800000000000c10800000000000000000000082c000000000000011123054b528000000301a00000000000000000000000000000000001903610e0000000c01446c0000000000000000000000000000123800060aec8c0000000000000000000000001d2000000000000000000784c000000000000016a2800000022260005d497228000000426c55e0001813800110d000000000000000000000000000000000005420000000000000002128c7705a800000000006a080000000000000107c0000001941000000058200003062000000000000009439064000388e05cd46e50ff45560f0c52000000055c000000000000000000000493a424800000000014590001887e86c08b006800000019078000000000000000014168000000402e000406e000000000000018d900004110001c1400000000000a1d800111a8000000000080dd466e208000000520400000780001c7800000000000000000700e00010840000000000000000000015163827014800121a80000007d8200000000000000000000000024400000001f13e587044000140fb27700e800000000012088000000023e0005451709a84021c80000000000c0480001119c700000000000000170480006018000000000000000000000000e0e00000000001363305c0000000000000000000000000000000000000038900000000000000000000000000000000000000000000000000a5700018178001c0a000000000000000000000319036100000000000000000000000000000000000000000000000002002a9900000000000e5980000007857f5b00000000000809000000000000000000000000000000000002c0a00000000006c8355500000000000000000084c79709441847a1edd26000680a25f80000000000000000134c80000000000000000156280000000000d4f90300000000c050000a42a01c0004016046000000000000001875a96800000000000000000000000000000000000232000000144900080000000000024a000000000000000000000000780c0000d6e00029800000000816088a0000000000628c0004d4600000006227c85c218001f17a404e5a00000002286000000062000000000001747b08c000000000000000007048000286774d2c0e0000000000000000049740007d6b15000000000000359800000000000000000088812d90180802408d00040488d1009
def g471D11 (j : Nat) : Nat := 0xc641ff
def g471H11 (j : Nat) : Nat := 0x3c300000000000b00000000000020000000000000000000000000c622b000000000000000000000000084c000000000000001e2ca8000000000000000000000000000d1b23b1c0000000000000000000000000000000000000b9c0000000000000200000000000000000000000000000000000000000000000000000000000000000085600000000048400000000000000000000000000000000000000000000000950000000000000000000000000111a040000000000000000000000001a900000710000005054800000000000000000000000000000000003240000000000000000000000000000000000000000
def g471L : Nat → Packing
  | 5 => (1,6,4,0,0,0,0,g471D5)
  | 6 => (22,5,4,0,0,5,0,g471D6)
  | 7 => (132,4,4,0,0,9,0,g471D7)
  | 8 => (143,3,4,0,0,12,0,g471D8)
  | 9 => (74,2,4,0,0,11,0,g471D9)
  | 10 => (8,1,4,0,0,8,0,g471D10)
  | 11 => (1,0,4,0,0,0,0,g471D11)
  | _ => emptyPacking
def g471I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 8 0 8 1 3 g471H6
  | 7 => lookupWord 5 88 2 12 5 3 g471H7
  | 8 => lookupWord 39 1195 2 15 8 3 g471H8
  | 9 => lookupWord 66 1327 3 15 8 3 g471H9
  | 10 => lookupWord 43 523 3 14 7 3 g471H10
  | 11 => lookupWord 6 199 0 10 3 3 g471H11
  | _ => fun _ => none
def g471 : Forest := ⟨471,11,fun i => g471Y[i]?.getD (0,0),g471C,g471A,g471L,g471I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P5_0 : block g471 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B5 : block g471 5 0 1=true := g471P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P6_0 : block g471 6 0 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B6 : block g471 6 0 22=true := g471P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_0 : block g471 7 0 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_22 : block g471 7 22 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_70 : block g471 7 70 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_118 : block g471 7 118 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B7 : block g471 7 0 132=true := (@block_merge g471 7 0 70 62 (@block_merge g471 7 0 22 48 g471P7_0 g471P7_22) (@block_merge g471 7 70 48 14 g471P7_70 g471P7_118))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_0 : block g471 8 0 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_30 : block g471 8 30 47=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_77 : block g471 8 77 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_125 : block g471 8 125 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B8 : block g471 8 0 143=true := (@block_merge g471 8 0 77 66 (@block_merge g471 8 0 30 47 g471P8_0 g471P8_30) (@block_merge g471 8 77 48 18 g471P8_77 g471P8_125))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P9_0 : block g471 9 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P9_5 : block g471 9 5 45=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P9_50 : block g471 9 50 24=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B9 : block g471 9 0 74=true := (@block_merge g471 9 0 5 69 g471P9_0 (@block_merge g471 9 5 45 24 g471P9_5 g471P9_50))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P10_0 : block g471 10 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B10 : block g471 10 0 8=true := g471P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P11_0 : block g471 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B11 : block g471 11 0 1=true := g471P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471T : checkedTables g471 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g471 0 0 0 = true)
  · exact (rfl : block g471 1 0 0 = true)
  · exact (rfl : block g471 2 0 0 = true)
  · exact (rfl : block g471 3 0 0 = true)
  · exact (rfl : block g471 4 0 0 = true)
  · exact g471B5
  · exact g471B6
  · exact g471B7
  · exact g471B8
  · exact g471B9
  · exact g471B10
  · exact g471B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471G : graphValid g471 (boundsBefore K439) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low471 : Lower true (varsX 471) (graphGoal 471) 12 := lower_forest (g:=g471) (i:=0) (hints:=4328523380) (before_sound K439 V439) g471G g471T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K471 := extendKnown K439 12 [(471,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V471 : Known true K471 := extend_ok (m:=471) V439 low471 (by decide +kernel)
def g511Y : Array (Bits × Bits) := #[(0x739c863c3190f0f3333331f333fffcc4bb2c43,0x318c021c31905073331110b3335554449b2441),(0x9ce718403e1ccc3c3cccce1fffcccc03b6c28c,0x94a508001214cc3c3c44420555cccc01368284),(0xe0f8618fc1e30f3ffff0f01c3cf0f03007de30,0xe0f8208540a1051555f0f01c3cf0f01002de10),(0xff007e0ffe03f03fc0ff001fc0ff010406df00,0xff007e0ffe03f03fc0ff001fc0ff000006de00),(0x7ff00003ffc000ffffe000fffdc3749203,0x7de00003af8000eeef4000aaa983648202),(0x7ffffffc000000ffffffff0000058b3c0c,0x77ffede8000000bbbdfaaa000004893c08),(0x7fffffffffffff00000000000031fca030,0x5f7abf5efaeaaa00000000000021fc0020),(0xffff8000000000000000000000000238085a40,0x4a528003080000000000000000000038005800),(0x3ce412580,0x980000003c6012100)]
def g511C : List ColumnInfo := [(40,0,471,0,12)]
def g511A : List (List Nat) := [[]]
def g511D13 (j : Nat) : Nat := 0x3ff
def g511L : Nat → Packing
  | 13 => (1,0,1,0,0,0,0,g511D13)
  | _ => emptyPacking
def g511I (_ _ : Nat) : Option (Nat × Nat) := none
def g511 : Forest := ⟨511,13,fun i => g511Y[i]?.getD (0,0),g511C,g511A,g511L,g511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P13_0 : block g511 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B13 : block g511 13 0 1=true := g511P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511T : checkedTables g511 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g511 0 0 0 = true)
  · exact (rfl : block g511 1 0 0 = true)
  · exact (rfl : block g511 2 0 0 = true)
  · exact (rfl : block g511 3 0 0 = true)
  · exact (rfl : block g511 4 0 0 = true)
  · exact (rfl : block g511 5 0 0 = true)
  · exact (rfl : block g511 6 0 0 = true)
  · exact (rfl : block g511 7 0 0 = true)
  · exact (rfl : block g511 8 0 0 = true)
  · exact (rfl : block g511 9 0 0 = true)
  · exact (rfl : block g511 10 0 0 = true)
  · exact (rfl : block g511 11 0 0 = true)
  · exact (rfl : block g511 12 0 0 = true)
  · exact g511B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511G : graphValid g511 (boundsBefore K471) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511R : Impossible true graph 13 nineInputs.toFinset := by
  rw [show graph = targetOf g511 by decide +kernel]
  exact root_index (g:=g511) (top:=13) (i:=0) (before_sound K471 V471) g511G g511T (by decide) (by decide +kernel)
def mo511Y : Array (Bits × Bits) := #[(0xfffff000000000000000000000fff000000fff,0xfffff455455455455455455455455455455455),(0xfff000fff000000fff000,0xfffff033033033033033033033033033033033),(0xfff000000000000fff000000,0xfffff10f10f10f10f10f10f10f10f10f10f10f),(0xfff000000000000000000000000,0xfffff3ff3ff3ff3ff3ff3ff3ff3ff3ff3ff3ff),(0xfffff000000000000000fff000000000000fff,0x8aa8aa8aa8aa8aa8aa8aa8aa8aa8aa8aa),(0xfff000,0xfccfccfccfccfccfccfccfccfccfccfcc),(0xfff000000000000000000fff000000,0x2f02f02f02f02f02f02f02f02f02f02f0),(0xfff000000000000fffffffff000000000,0x300300300300300300300300300300300),(0xfffffffffffffff000000000000000000,0xc00c00c00c00c00c00c00c00c00c00c00)]
def mo511C : List ColumnInfo := [(260,72,179,0,7),(139,48,324,0,4),(10,32,469,0,10),(40,0,471,0,12),(24,0,487,0,11),(322,44,145,0,4),(68,0,443,0,11),(137,16,358,0,7),(9,0,502,0,11),(152,1,358,0,7),(154,33,324,0,4),(320,12,179,0,7),(57,0,454,0,8),(12,0,499,0,11),(186,1,324,0,4),(366,0,145,0,4),(11,32,468,0,7),(14,32,465,0,7),(42,0,469,0,10),(156,1,354,0,4),(187,0,324,0,4),(268,64,179,0,7),(321,12,178,0,4),(358,8,145,0,4),(362,4,145,0,4),(324,8,179,0,7),(153,0,358,0,7),(262,104,145,0,4),(108,0,403,0,8),(72,0,439,0,11),(69,0,442,0,8),(328,4,179,0,7),(270,96,145,0,4),(302,64,145,0,4),(330,36,145,0,4),(354,12,145,0,4),(155,32,324,0,4),(197,16,298,0,4),(294,72,145,0,4),(334,32,145,0,4),(26,32,453,0,7),(141,16,354,0,4),(212,1,298,0,4),(125,0,386,0,4)]
def mo511A : List (List Nat) := [[],[98],[64],[64,98]]
def mo511D7 (j : Nat) : Nat := 0x322cd90758c86a5824c971cab1441d6321a9609325c72d91a2750c76c1814c570
def mo511D8 (j : Nat) : Nat := 0xc000042f48f44646f43005140140042f0874d00a00511c13d0c0043dededededededededededededededededededededededededededededededededec0c07e60602a00eaaad032e58b4ac3a659f45b0305b561d824cb768b0060b6ac3b049961b7641c62e1a94c971c76a8838c5c352992e3a3cd90321a9609325c7578a2064352c1264b8d675371b961d3260571d8eae130ec9b02c82e3979592710b7681814c7a3a996cbb0ed030298f167351c06dca864d21c2eee2380db950c9a43ad55a2305b561d735c31b7344e216ed0302b867664c9c42dda060570ced890b885bb40c0ae1add1a231db0605315c30bbb28e3970d1a42b86367251c72e1a348570c6eca038e5c34690ae18e9c94718b868d215c319bae8e3170d1a42b86b55688c16d5875cd40d2ead118edcb0298a8185ddd971cb868d215031bb3a0e3970d1a42a061b765dc62e1a348540c76cb838c5c34690a81fd09855d1824c9705033b3190ba36690ae0a07762609746cd215c140eec8c0ae8d9a42b82811755dc260b1695875ceae8ba44c162d2b0eb9cab3758c86a5824c971ace2e9170c3b26c0ae359c5d22e1875cd815c752ab4e60b6ac3a64c04f64750c76c1814c570
def mo511H8 (j : Nat) : Nat := 0x9900000020000000000000000000000000a1000000000000000000000000ba00001200000000000000000000000000000084000000
def mo511D9 (j : Nat) : Nat := (if j<1 then 0xc7dd976cca848540cfd9706cca8485408fddc72e1a348540c7dcb865da348540e7cd9768d8248540e7d5b968d8148540e7d59768d8148540ebd58768d8148540fd39855d1825c140ff4985609325c140fd99325d1815c140fd99825d1315c140ddb9b85d1215c140ddb8b85d1215c140fd99b35d1215c140fda9825d1215c140fdb1815d1215c1409fd8c86cd215c140dfc9826cd215c140dfd1816cd215c140d774a92c5a561d20f1f4c961d815c520d7cdc26e0974c910e5dcb969d874c910b7cdc825d824c9109fd4c86e9325c510cfd5a86e9325c510ddd5ba61d325c510dfc5ba609325c510fdc587609325c510b754c16d58764c87b764c16d58764887a774ca6d58764487b770c16d58764087d5d5c76c49861d73b74dc2261a561d73b755c1261a561d73d754982c5a561d73bd54c1695a061d73c7d5c76c4a865d32c7d5c06c4a865d32d755972c5a561d32af54c1695a061d32bf44c16d58760932abcdc22a1875cd81a7cdc22a19864d71adcdc22a18764d71a7cdc22a1985cd71adcdc22a1875cd718eddc62e1a94c9718eddc62e1a74c971abccc86a5824c971b9d5c329d8760571b9e5c229d8760571b9f1c029d8760571b9d5c32618760571b9e5c22618760571b9f1c02618760571b9d5c32a58760571d9d5876cc8760571d9e5876c88760571d9f1876c087605719fc5c22e19360571cdd4ba61d9360571d9d4b861d9360571d9d4ba61d93605719fc5c22e17360571d9d4b861d7360571d9d4ba61d73605718fd4ca6e53260571d9d5b761d3260571d9d5b961d3260571f9c5876093260571f1d58764d8164171c7d4ba69d9760531bbd1c029d8760531b3d4ca65d8760531f1d5976c187605319f95c42dda060531f1d59761da060531c5ddc06dca864d21c7d5b86cda125d80bd54c16d5875cd80b974c16d5875c98087ddc12e5a74c980c7d5ca6c4974c980e95da76d5874c980bb54c16d5874c980b71dc425d854c980b755c125d854c980b78dc425d824c980b7c5c125d824c98097d5c12e57360580b795c425d814c580a79dc425da348580a7d5c125da348580bd54c16d5875cd708eddc62e1a74c9708fd5c12e1a74c9709db9c42dda060570e9d5a761d814c570bdd0c76c1814c5708dddc72e1a3485708eddc62e1a348570bd54c16d5875cd408eddc62e1a74c9408fd5c12e1a74c940b5d4c76e5814c540e9d5a761d814c5408dddc72e1a3485408eddc62e1a348540fd19855d1325c140fd8974609325c140fd9174605315c140dd99746cd215c140c774a92c5a561d208eddc62e1a74c9108fd5c12e1a74c910d3cdc26e0974c910b3cdc825d824c910b78dc425d824c910c754b96cda121d75c754ca6c49861573c754ca6c4985d573d555972c5a561d32965dc62e1975d5329755c12e1975d532b954c16d5875cd80 else (if j<2 then 0xcaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaac880880880880a85a69a690cea42a101759c899695988093d83d93d83d90b8d989c88088088088088088088088088088085983d7fa7fa8217fa7fa7c878b7436fb6c96ad69c08066a64e6275f55ce5a757554e43251c4ea4ce4ce49c49c47544e43243240b3ce3ce39c36a3433113112b82df2df2b82862542542221f01d41ad1911751591270f50f50ce0a708004e032032000d775922c59564187d7cda16c89861d73d7d5ca6c49861d73cf75a02c5a561d82dd75a02c5a561d72df55a02c5a561d32f55da565da061d32df4db06d58760932e9ddb069d874c981c7bd926d0a764181cf9d326d0a764181cfb5216d0a764181e9dcca61d7364181c6fd906d8a864971cef5106d8a864971c7dd906cca864971cfd5106cca864971addccb6a5874c971d9f4cb61d9260571dbd5b961d3260571dbd5b761d3260571f9d5c061d3260571fbc5876093260571d9f4cb61da060571e9f5a261da060571f9d53261da06057197dcc86e53264171d5dd876e53264171d7cd826e53264171f1f59261d8164171f9d53261d8164171f5d58764d8164171b7d5c264d8164171dbd4cb61da060531e5bcc46c1a726121c5fdb46c1a726121c7ddc06dca864d21c7ddb02e98764d21f3d5c061d9360521d7d4b764da060521e7d5a764da060521f3d58764da060521e7d5a464da060521db75822c5a561d80df55322c5a561d80db75a22c5a561d80c7ddc12e5a74c980d7d5c86c4974c980e9ddb169d874c980b7cdc125d824c980fb4dc561d824c980f9cd7161d824c980d79d326d09760580d7d5326c49760580f9d53261d815c580cbdccb61da348580cf75a22c5a561d70dd75722c5a561d70df55322c5a561d708fddc12e1a74c970ed5db569d874c970ff0d85251824c970fd4d855d1824c970d9ddb261d7360570cdf9a22dda060570ddd9322dda060570ddf1212dda060570f9d53261d815c570c5fd946dca848570cdbc946dca848570cdf9406dca848570cebc946d8a848570ccfd746d8a848570cf9c946cca848570cddd746cca8485708fddc72e1a348570cf9cb8251a348570cddcb85d1a348570ef8c9468d8248570edcd7468d8248570e7d5b968d8148570ebd58768d8148570ef949468d8148570edd57468d8148570efd1b068d8148570cf75a22c5a561d40dd75722c5a561d40df55322c5a561d408fddc12e1a74c940ed5db569d874c940f74d97615824c940c5fda22dda960540d5dd322dda960540d5f5212dda960540d9ddb261d7360540f9d53261d815c540c5fdc96dca848540cdf9c06dca848540c6fd976d8a848540cef9706d8a848540 else 0x10500000864000085a136300a0fc1b0960e0144f11e11c680a0020146d09e1bc680a13c4784e0dc34028a1000705d23a274300a2743c1381c0289d23a2646e8601450020142d86014008610000840140084808008050c14813d86014459bb0c0500100a2ec8d8802800ec300a34cd98c82503ec300a3544a86038008880007040141b08c490000a13c18010b4180501c1b48689002088970cc00010f8400a00a1f88e8c0280c09d0c070050f8434d0140144e11d37a300a13000010ba1e4620e0584c180140087d0f000010c008160b8200a0021f04e8781c2001315c27c3f8c0044e081000700113827430021e88d081002889c102070c0262704a180043e08103860011342642081a304d9a033630011266a0c98c81c44180042219b180086028028403c09858240784d3603b46820264d20f9188808208008050c8140000219020020143f10e37c200513038050b84005c000284aacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaacaa))
def mo511H9 (j : Nat) : Nat := 0xc7400000000000000000000229d07000226900281000000000000000353e99c000002e8c000000000002824000000000000003c94002448000000000000001294000000000000000000000000001c68000000000000000003c5c00000000148c000000000000000000a98003429940001d64000000000000000000003488001e88000000000000000000000002004000000001060000000000000000000003604000018000000000000000000000000000000c7f67c00000287800000000000000000000000285400004c00000000000000000000000000000381ec9fe2c00000197a43400000000000000000357c000002284000000000000000000000000000000001c6e91c000000000003d5ed0c000000000000000002c81444000000000000000000000000001c40000001d68000886022560000001498000001108003514000002e3742dc30002e90490000000000003450000000000000000000000002c58002c14808000438000000000000000002104000000000000000000000000000000000000464000001d5883f40c000000000140099
def mo511D10 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x61d32503baecc30a99281bd769d854c940eebb2ec2a64a077cd98609325037e6d3b0499281df365d824c940fe9b0ac1264a07f4d7560932502afe5bb52c0a81e7761d7360540f3eb0ec0ae2a06ddda761d31503beadcb0298a81df5661814c540dfab4ec0a62a077d59760531503deac3b0298a8137f6dca8485409dfb6c54242a04fddb32a1215027ee5c34690a819f7661a348540cfbb2ed1a42a04fddba5cd215037e6d1b0490a81bf568d8148540fb72e8c12e0a07f59854c970503fe4c1264b8281f6e5d1815c140ffa30298ae0a07db97448570502fecd9a42b82819df6d5a726120cefb6ad412e90677ca969587482fba58b4ac3a411ff6e89760520a7fb704bb029057f5b125d814823fedd130b8a4157f6dc985c520afeb624c2e29079f587605714831fed93504ba21d772e5875cd10a7fb704bb048857bdb425d8244277edb150b92213f76cca85c9109feb62542e48867dca968d724427fad8950a12219f72e5a74c9109fb970d3a648857ddb825d324436eed3b0e99221df3661824c910df9b4ec12648877cd9760932443be64bb0499221df3651824c910dfab50d1ae2887dd58768d71442feadd264b8a21f7561d325c510ff8b04992e2887fc5824c941443fe4c1264c0221ff2609325c110aee962cab24c3d774b16559061f3ba5cb4243b0bbd36cda221d75cee972d090ebaef55b3684875d73e6d13424c2e79f56dda126173cfb342d0130b9d7cdb2261875cebead8930c3ae77d52c5a561d73aebb644c2eab9dd74b1695875cab3edb130baae55d76cc985d572aeeb624c2eab947ddb12a1974cbaaecbb4ac3a657d52c5a561d32aeb970cbaea99755d9761d754cabaedc90ebaa657976d8875d532be9b6443aea995f55b121d754cafacd810ebaa65dd365d75609329f9b64542e6c0c7dcb969d32606becd812e99303a7769d874c9819f9b6454326b8cfcdb22a1735c67ea5d326c0ae3e7561d9360571f3ab0eb9b02b8f9d5874c9815c6fe8d814ec0a635f52e99760531e7ab2ec3b0298c7ddb72a1934879eac3b26c0a439f56cda125d80b6e962d2b0ec0573db425d85602bbad892ec2b011f76c4a95cd80f2bb6ac3ae6c0675ca961573603caec3b0ab9b011f72e5a74c980af3b684ba64c057d5b125d326034eed3b0e993011f72e5a74c580af3b684ba62c057d5b125d316034eed3b0e98b01f4e615745c140fb32e8992e0a07d99744c5705029eedc12e992215e76d0974c910cd9b4cd1130b9e74da5688985cf3aad2b424c2e79f1689a126173cf3348d0130b9e7c9a2680985cf3e8d0b404c2e77552c5a561d73ae9b644c30ab9d755b1261855ceba6d9130baae75d56c4985d5738dbb6c5432e9947d5b12a1974ca3e65d32ec12651f36c8a865d318fa974cbb0298f1d59761d814c62eedb950c9a431b76d8a864d21 else (if j<2 then 0xe37f66c0984c9719fb970d3a64b8e7dd9869d325c76eed3b0e992e3b776a5874c9719fbb7443a64b8deddb621d325c6fe6d910e992e37f66c0874c971df9b52c1264b8f7cd98609325c77e6d3b04992e3f7361d824c971bfab6654b02b8dfd5b3261815c6ff2d9130c0ae37fc6c09860571cfe952d3b02b8dfd5b329d815c6ff2d914ec0ae37fc6c0a760571e7e952c3b02b8f9f4a761d815c76fa54b0ec0ae3e7d2618760571f3e952c3b02b8f9f5b261d815c7cfad830ec0ae3e7d61c8760571bfab6643b02b8dfe5b221d815c6ff8d810ec0ae37f52e99360571bfa970c9b02b8fbd58764d815c7eeac3b26c0ae37f52e97360571bfa970b9b02b8fbd5875cd815c7eeac3ae6c0ae3e7d61da2605719fe974c9302b8f9f587649815c7cfac3b04c0ae3e7d61d7260571bfab7299302b8efd4a94c9815c6feadba64c0ae3ef561d3260571fbab0e99302b8ffc5824c9815c7cfac3b40c0ae3d7761d9364171afbb7299320b8f9f587605905c7beac9b02c82e3d7765da061d31bfab6053b0298f7d5a765d814c7dea53b0ec0a63ef56c18760531bfa96ed030298efd5a7681814c7beacbb40c0a63ef561da060531dfab48d030298e5fdb069c984873ee5d30ec9a43df569d9360521efab26d030290e7f5b8684976033fad93424bb017dd2c5a561d80fabb6ac3ae6c079ddb161d73602bdeda12ec13015fd6c497609808ffb6254ae4c0797db561d72602beed892e99301ed76d5874c980eeb92ec2a64c07b5d8761532603daec2b0899301df325d824c980f79b0ec1264c07f4d7560932603de6c2304993015ef6d09760580afeb624bb02c057dcb95cd81603ceec3ae6c0b019f72a5325c580f3bb0e992e2c079f58760571603bea4bb0298b01ef561d814c580f7ab08c0a62c057bdb425d21602bfad892e90b013f72e5a348580cfb92ed1a42c06bdd8768d216035eec234690b017dd2c5a561d70fabb6ac3ae6b87d5d87615735c277edb150b92e13f76cca85c9709feb62542e4b84fdcb869d325c36eed3b0e992e1dd7661854c970debb4ec2a64b87f1d85251325c3eaec2ae8992e1df3661824c970df9b4ec1264b87f4d85609325c3fa6bab04992e1fe3251824c970fb9ae8c1264b879dd875cd815c2efc5bb40c0ae1e7d61d815c570dbbb4ec3a62b877d5b9605315c3beacc30298ae1bf569d814c570f7ab0ec0a62b87f9494605315c3eeaba30298ae1ff46c1814c5709bfb6e54242b84efdb62a1215c27eed995090ae13f72e1a348570cfbb30d1a42b86f9c9468d215c36eeba34690ae13f76e97348570df9b46c1242b86fd5a3605215c3facc2a64c02e1ff26093260170ffa30298b00b85fd9b3485805c2fba58b4ac3a81f576d5875cd40fabb0ec2ae6a04efdb62a1725027eed9950b92813fd6c4a85c9409fb970d3a64a06ddda7 else 0x6e54242b86fbda8251215c37de5412890ae1b7f6a17448570dbf950ba242b87f9c9468d215c3eeeba34690ae1bf761da348570ff5928c1242b87ded74609215c3bfadcb0290ae1efd61d8148570ff6928c0a42b87df574605215c3ff8d830290ae1ff64c98160170defb44d2b0ea07dddb161d73503bbecbb0ac12813ff6c4a85c940fafb6ac3ae4a07f5db561d32503faec3b0a992819ff689a960540f3fae4c3b02a07ddd875cd81503beed4a64c0a81df76613260540bfbb6e99302a077dd974c981503deec3a64c0a81bf76a1325c540fbbb0e992e2a07df58760571503fea99302b8a81df765d824c540ffab6ec0a62a07fd587605315027fedb95090a819ff6a19748540cff950cba42a077dd9768d215037eec3b4690a81dfb65d8248540efeb72c0a42a077f59760521503dfac3b0290a81fde615825c140ffb264c0ae0a07fd9824c570502ffcdc242b82817fe2e1215c140ffb36690ae0a07fe98248570503ff8c0a42b82819ff6c5a726120cffb62d412e9057fdb12a5874833fed0952c3a41ddf2a5a561d20e7f972c3b029067fcb96a171483afe5cb0eb8a419ff6c9a825d10cffb4454b0e8857fdb825d82443afe5cb0eb9221df72e5874c910ff9b0ec1264887df5b261d71442ffa5c344b8a21bfd6a1a25c510fbeb0ed12e2887fd5b368971442ffadd304b8a21f7d61d825c510ffab46c12e2887fe5a260971443fead4264b8a21ff361d824c970ff9b0499302b87fcd824c9715c3fe6c3b0499281ff36093260540ff9b04992e2a07fcd8460932442fba58b2ac930f7dd2c59564187bee962d2b0e43f75db561d9321fbb6dab0ec910fddd6d58764487eef36ac3b2043d7ddb1261875cfbae4c34ac3ae7f57695a061d73fabb60c3b0ab9df74b16958760b3fadbb424c2e59fd6c1a126172bee962d2b0eb9775d97695874cbaeecbb42c3a65d7765da061d32debb4ad030e99775d9761d754cbfa6dab0ec1265fd361d7560932cfbb2ed192ec0e7ed97688976073fccbb404bb036f76cc9761d81b7db644bb0ec0dbf9b025d876075eec3b4643b03afb61da221d81d7f30ed010ec0e7dca965d736075ee5430eb9b03af72a5875cd81f3bb60c3ae6c0ebdda761d32607de6c3b04993033ef6d0a7641819fb974b9b20c0f9dd875cd906073eecc3464c2e39fb661a226171df9b66d1130b8e7f998680985c6eeed9930c3ae377b6c89861d71bbf3604c30eb8e7dd9868c875c76eec3b4643ae39fb661a221d71dbdb0ed110eb8efcdb3688875c73fccc34043ae3b7e61da021d719fbb6454326b8e7dca8661935c76ee5430ec9ae33f76c8a85cd71cfb950cc2e6b8eddca861d735c677edb150c92e33f76cca8649719dfb6c542e4b8cfddb32a1725c67ee5c352992e39f76a5984c9719fbb744c264b8deddb6261325c6fe6d9130992)) else (if j<5 then (if j<4 then 0x5a3d80f463d18f463c88ef43b40ed03a70eb63a7075a3a0875a3950e1c37b8dca3698d643460cd632c8c8e3158c142f48b902db0b342bf0ad82ad075a2ad075a2960a7c2960a16275098825b8940243092624308d4229885a20b07fe1d6875a1d6875a1d687d01e607741d6870e1b5869e1998610173855a14b04f41278000114843810502dc0b703e60ee02f60a5038a0d483520c402f60b702b80a502380970238082820a02e01e607080b802e00b802e018a0250166050811e03980e602e0094019802e0000000eefb24cab20c3f7ddb161d9321fbf6d8b0ec910fdfd6e98764487eff362c3b2043f7dc98685875cfeeed8342c3ae7f77685a061d73defb40d2b0ec17d7da5681875cbbeecbb42c3a65fd7695a061d32dfbb42d030e997f5db061d854cbfe6d8b0ec1265ff36c18760932fbbb60c3ae6c0f9fdb061d72607deed830e99303aff2e98764181cff94ec9320c0f3fd87649906077ee53a64c8303df765d3264181f7bb0e99320c0f7dd944c9906073fed1340cc2e3b7f2e98764971dfbb52cc264b8f7ddb0661325c77eecc34e992e3bf76a5874c971dfbb4ec3a64b8fdddb061d325c7fe6cc304992e3ff361d824c971f7eb64c3b02b8fdf5b061d815c7fead3b26c0ae3ff561d9360571ffab4eb9b02b8ffd5875cd815c7dfac3b44c0ae3efd61d9260571f7eb0ec1302b8fbf5875c9815c7fead3a64c0ae3ff561d3260571fbeb0ed0302b8eff5a2681815c7fea99340c0ae3df76099364171affb70c9320b8d7fcb8649905c7afec3b24c82e3df76cd9264171efdb04c9320b8f7dd984c9905c7eeec3a64c82e3ff36093264171fbeb0ec0b20b8f7f592605905c7fea99302c82e3ff56c1a760531ffab60c3b0298ffd5a7681814c7feac3b40c0a63ff5691a060531cffb60d393090e7fda02a587487beed830ec9a43efd6c18760521bfe96ed030290eff5a768181487dfac3b40c0a43bfd691a060521f6fb4ad130ec07dddb161d73602bfed892ec1301edf6d58760980cffb6254ae4c079fdb161d72603faedab0e99301ef76c5874c980efb92e99302c07bdd874c981603deec2264c0b01e7f609875c580f3fb64c3ae2c06fdda84c971603eeec3a64b8b01ff3609325c580fbeb0ec0ae2c07fd53260571603feadbb0298b01ff56d1814c580d7f974c3a42c06f7da2695875c3eeed8b0eb9ae1fcf6149460970fafb0aba304b84ffdb12a1725c3ebedab0eb92e1fd76d5874c970febb0ec2a64b867fda26a5815c3cfeb930ec0ae1f7761d7360570efbb5299302b877dd984c9815c2feedba64c0ae1ef761d3260570ff392899302b87ddd744c9815c37fcd1340c0ae1ff64c9a060570dfbb50992e2b87ddd874c9715c3efac3b02b8ae1ff54c9815c570ff3928c1262b87ddd74609315c3feadbb0298ae1ff561d814c5709ffb else 0x148b0c0110202038051ac602407002c8b0ecdb1202084052f83c08010144e0c0a808010145e2384e0c050280140800228db0c05b22c4808001d800042e23c60283d0c058000113080160002840174302400134dd1b43c0007170853405d0c000246000010b000042043000043c20000283006cd032c601c5033c60043d374601c101182004000d83004000f88e1300208051502004000f0201c050d0201c050f88e1005e0c00178301c010004c08010003e0e02004001383e2384408001748d10000444df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df537d4df53788dcf36fadae366cd8ab5ded670ad81d6875a1d6875a1d6b56e2ad354ad49b4eed3034a6d193422cfab3a8cdeb356cc7b2e6b612d84b6132c23de875acb0b2c2cb0ad84b3aaceaca2b23ec7f31d8ad4b1b4b612d84b67ad84c5db176c5dad84c5dad84c5db190b613176bff3152b43aed0c54ad0ec4930f6c32309ac163020bff2ffcbff2ffcbeeaf78bd02ef4bb42ed0bb42ed0ba3ae56b852de6b70ad9eb58075ab61075a1d6ad60b4caceab43aceab31ac84b10ac1e1d6875a1d6ab52afeabc2addab52acbaaf6aafaa90a98aa20a7a29b0a592940a42289ea17281a9f8a7be9e1a7589caa6fc9b626a099a262697ba5ca969a56e952a51c93ba4b691d24467c8a40e8faa3b28dea37a8d5a3288b9a2b88a2a25c88ba1e2868217c84ea10c83520b0820a0548049fd07e61f6a7cf1f227c89f087b41eac79f9e5078b1a7476f1df476f1d7a74e1d145481ce672b9c6c70a9bf26ec1b786d01b086b69aa269d1a4668619ea66c999865d194664398e062c9870610981e5fc11385ee176c5d217105b896be5a4166c58f95e258415e25681568551152053c94b051e144050213c64e613604ca129e4be92cc4a79284493121e48791f046b9180457113844010c8426906c40f8fd24090ff63f48f463ee0f463d18f9e3de87) else (if j<6 then 0x10014011688e0c0a0f8305c0a0c1001500e0c0a1584230010dc8713828004d234400020128d800cc8080f158d70d027100503c6f0d8b600011005c0388f180a1708028050f4301400c200a17c3d1b0021c1617c3028230f88d180a088404000d0f4dd18011b08d374602840300580001134dc20000284910000280113434324600107014161e4dd0e46c200042469190908035124643109001071bc3c2f000044003c3c2f000045830050043a2000038051007000010584a22cd02400b180a1b88203c3000050286d0c05042000045d0f080000a1144000010384038160800028223000014010585a20000283310000040e1384f180a0044c100a0043611c341c4004c5e13c3c1c4004c513704d0e07100131b04d0d4d01c091006030550283d37460040a134d0300ad180117434324603d091006c134391907424401b0891b0450840164dc11079194242469350c9190742459350c4264641c5a104b100140285e13c3f1801138412c400500a1704028400044d0d0c03c0a110c948400284c10141000a130412c4003801141402824300e0043c1005d0c0a138800784d08401788e134210046218450840128813401a1040144603c8c1000a13460500a0c0a23346004462246611421005621c30154d610421007a10400283a12c3318408245a12c31000a11841000a0f84f1a8c0044c110c0043c120c1000111846304004c4e138c10013104dc1001c304004c6c114d01f0c1005c10550043c104000430034dd180113044324603c4041c6c1246c310710059350c03e4641c5c12464314210059370443246509071b84a33c60044a104b1028c0045e104b1038c0045c1186430011304430400044c130c1000110140042c104b1030c0045e1342e304011845098c1004136840068c10051180fa10400044d18140043a10400043612466314210056114d1098c10050050cb190712cd032c600443360c31a07120c004243001b180e12c6430010c05004200418080b004050c0a05c2028050a0771a100c0001c05004421f462403424170b0905c201413084d0040f04c40174601f4d04050154d0241712464240f0e46424170e4d4330203e4642469350c0010791805440793544c080f919071a020040e0e888480a0e02a22c3b180a1688b0ec6b36020246336c3a220231a0918cd80a4431a0981c631805824333644a08c68245f2346d23c40145d13c6028320801014360c0520a000045e0c000043e0c07c080e004001b8301d02038010006e238402b0020801014701c050bc8f1386060441c050b07014204788e0f840145e218de10051386e238de1082c54051c072360701446340901c05130601c870144c0f02028010145054130143004050b485340901c00d10051f43c0805100011703c08051000116c3808051000116c8b1202004408480e0 else 0x137049190950840c207a10c601440172099087a10c682440832421b04919421002b41c61368431a0790840a307a10c690840832071910135449190941d0c1fc8f1346930c20146e0c82004051284b180a0d848000a0fc8f139d03c0517c3625870144624170bc8f138d028010146e23846340a004051b830240763405168401783635000246a1386e340a118d01c050f88e1306c34051706c348921c051400004050d4482e00c480a17485374402801000051e46425070024d0146f0fc60043b0c0a05c360c0101431000109020040f0fc8f13c30144721c470c0513c3c2707014470d0941c051348d1001d0c11014653743028010145d0c0101430074382607134051b43028019350c01465374302407014504748d100a007430147c0c010143d234491801d0c051a5d425070140f16460074342507014693646d0c0511c3014010dc3004050c0103c2f0c01014340800004051102100010d02004050d12004050dc6826077331201467120b803c303c0a1a02004050e12014010e02014408480116c8b120202801848051ec3014010c02014010ec3014408080116c3028018080516c6b0c0f0144f0c2504c0513c8f100a007c3014642507b740f0145b1bc3028010145b22c48080a006c30147b0c010143b0e02028010145b22c402801002c3b36c6808052ac302407b36020146b0cc682607808051805403c3f180a164405c0a0e4490ec60500a1744d0c0e004451143038011284209000284e0c0500438080a00612014502d020040001456138382e0003c0a1b83)))
def mo511H10 (j : Nat) : Nat := (if j<1 then 0xbe000000000021bdc0c9991d549d8dfaf8000250c682000380086f22b823240008994c8f71838b6d1d400042100000003aa8d8cb05c60fc0000001c8d60940003b4c00000000000003cc4000044100000000000000f204000a320000ca028a212224de000220b98a324242dc000b7434ae101c00000000000000000d307c71000048500000000000000b362ade0000000000096400000000000090a05c000000140656200000001c9c0000000000293da9180654776938a1484b900005aa000290d0000ac700000000002928d35c00000000000002cd30000000e28000b000000000015100000000b7284aa31bb47e0000000000000000022c5000200e712b84d0001c0800035ba10c0000187880c00035d954980004988d5000029c3016fe1ba158ce2a48000000000001b18000b293c01000294a00000000000000b0a40000002c930000000506800091e800037600000001ab0ab2400091e000066300007a4d01f421dc0f4382403c2b0000000258e0001ec4598c000caa4000e294e300000000533400000000000000ac800000000000000000000046d000000000005b8000031fcc2e000000000000007093062c1ab47d7119a6e000247c09fb40900000000000000515400000010370000000000000000000000002e1872280000000000000000000000000000000695583d0002c9a125c00071785e0c048000a5a1ce15054000735b66600000000003463d10cc92d09c00006a4000a071c4700008b336ad88e46bc000a5440000000000277c000000000032c8000f2fe18f59900000000057000000000004cbf338405f05000000028ad000000000008df72600000000a2c616800000000000000abf6250000000000000000000b3800033694667ac782f122c000f140edf129d5cb41b00000000000000000012ec0000000000c36c00000018192344c6f6340000f07780202ac00018bc0000000872776800066e55905800ecb133c00046176db0000000d1900000001c5151640000000000000002d5ad88b85184000000000071380008715438000000000000000284000696400000008740000ebbd1ded53b2a0039e0d8823d2d40000000000c12c00000000000000000000000050840000000000badcc28fb58000000014fa1e400000000000002c3b295fc04064d89b00010cae5e15750000000c610000e04000079b14c32a80876e5ebdb830d755600010bc00016aa0003d74204d0bd00039a463650162688000e4a4000000089117791e30000000a5df1b756b8000b5bc00000000000000000e0981c80002cd25af40000000000c40c0000000000fa90000000000000035600001aca00000000002067000388c0041200082080c00000128e0a180281808401b2128265088032000050800004e000041004c20880ab9440506121002478423 else 0x1da100008dc0000000000000000000001b540000000000820a0d40000000787f042c2d00000000c831374edc000062992195655680000697800000000000000000d0780007648000f2c00002ab00002b7658ab06dc89000000000012760003147000246d0001636000000000000e30000000000003146cc000d0440005034000b0f0000000260a000000000000000000000000015cf29b12a0001853d1200001b8c000b13d09d50824d582ea0a900030afe1a484c81c0458f258000b61f2c300024990001a9200000000002e4900000000000000a3318c085b15bb000287300000000000000000000000030c200000000002c5d00000000000000a1136340000000369c00000005860000000d718000c5579db8acea980000000728c0000000000e5ceaba00005b60002d2c0001c180000c2a373c40af0e800030ac00000012a7000000000002adc9b42d4a31c000f1edc3e9200000b0b2da345040009864000000252128740b100000000001c6800000000000000a0cc000a27c9390000000031586be17c00000011273aadc950003049000000000039790000000f100000e151c226738000000044500005ade0d0000227a4c60001a2d00038)
def mo511D11 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x7fd5a760531ff529d814c7fd58760531ff5681814c67fda7261219ff6a0974877dd8764d21efd61d814867fda125d80edf6958760377c9761580edf61d85603b7d8561180f7761d73603f5d855cd809ff2a5726039fd875c980bf769d326037dc974c980ef761d32603f5d854c980fd75d532603bdd844c980ff3609326027fca95c580e7f61d71602fdda74c580df725d31603bdd874c580ef761131603fd5814c580bf768d216027fda126170ddf661855c3f3d8525170f5f615745c3ddd875cd70fd7615735c37dd984c970bf769d325c3f5d854c970fd75d5325c3f9c944c970f775d1325c3fcd824c970df7661315c2fdda74c570fe7251315c3ddd744c570ff5605315c2fdda348570fde615805c3fd93260170ff64c5805c377d9861540ddf65d85503ddd875cd40fd7615735037dd984c940bf769d325037dd974c940fd761532503f5d754c940ff3609325037dd984c540bf769d315037dd974c540ff560531502fdda348540fde61570503fd9325c140ff64c5705027fda7261209ff684984827fda825d209ff6849748377c9761520ddf261754837dc974c5209ff69c984427fda825d10f7761d734437dd984c910bf769d324437dd974c910df725d324437dd944c910ff360932443df5875c510ff568d71443fd5325c510ff54c941443fd93260110ff64c970442f74a165587dd76559321f6ed9664887ddb6559221f7cd9364887df368d9221f7759564487df564d9121f7e59264487df568d9121f7799564087dee6519021f7d99364087dfa6499021f7f19164087bd768c87616f6da221d85bdd68487616f79a021d85bd768c875d6f6da221d75bdd684875d6f79a021d75bf3688985cefd5a126173bf6680985cf75da5261739f7688985cf7cda2261739f7684985cf7d5a126173df6680985cfd5da561d73bf3688875cefd5a121d73bf6680875cf75c9861573f5761d855cf75c985d573f5761d755ce7dda325d829f72a57360a6fda6261729f768c985ca7f5a1261729fe680985ca7eca9609729f72a1974cb5dd9761d329f76a4874caedda621d32bf3688874cafd5a121d32bf6680874cb75d9761532dd765d754cb7cd9760932fd3615824cbf4d75609329f768c976067eda225d819fe680976067dca95cd81e7761d736067dda3261719fb688985c67f9a0261719fd2a5815c79f587605719f72a1974c75dd9761d319f76a4874c6fcda221d31bf5684874c6fd9a021d31df565d814c7bd5876053197f69c984866fda6261219f768c984867f9a0261219f768c974867dca864d219f76a5734877cd9360921df564d814867bda425d809f768c976027eda225d809fd684976027dca95cd80e7761d736027f8a960170f6e5d1705027dda325d208ff6a0974427bda425d109f768c974427eda225d109f3688985ce7d5a126173 else (if j<2 then 0xdff661825c3f7d8560970fdf5d5825c3fbc9460970f7f5d1825c3fdd7360970bff6a1725c2ffca85c970f7f61d725c3f7d855c970ff768d725c3fed825c970ff761d325c37fda960570dff661815c3bfd8760570fef251815c3dfd7460570ff75cd815c3fdd3260570ffe681815c2ffda85c570f7f61d715c3fdd325c570ffd605715c3fdd874c570ff7609315c3fdd724c570bff6a1215c2ffca848570dff661215c2ffda748570fef251215c3dfd7448570ff768d215c3fdd7348570ffb609215c3fed7248570ffd605215c3ff98260170ffe605805c3ff92160170fdf69587503f7d8761540dff661825037fd9760940fdf61582503f7d7560940ff75cd82502ffda85c940bff2a172503dfd875c940fdf61572503fdda35c940ffb60972503fdd874c940dff6a5815037fd9860540dff65d81503bfd8760540ff75cd81503fdd3260540bff6a171503dfd875c540ff74c971503ff5815c540ff761d31503fdd824c540ff75c931502ffda848540bff2a1215037fd9848540bff69d215037fd9748540ff768d21503fdd7348540ffb60921503fed7248540ffd60521503ff9825c140ffe60570503ff9215c140dff2a587483f7da561d20dff25d81483bfd8760520bff6a1714837fc985c520f7f61d71483ff5815c520dff2a5874437fd9860910dff65d824437fc9760910dff65182443fdd7360910dff2a572442ffda85c910bff2a172443dfd875c910ff768d72443fed825c910bff2a142443fdd874c910ff761132443ff5a85c510ffd68971443ff5825c510ffd60941443ff98260110ffe6097044377d9564987ddf6559061f7dd8764c87dfb61d9221f7dd9364487dfb6499121f7dda364487dfd61d9121f7f99164087dfe61d9021ef7da021d85bdf688875d6fdda126173df7684985cf7dc9861d73fd7695875cfddda161d73f77681875cefdda121d73fd761d855cff5d985d573fd761d755cff5d75649739ff6849760bf5d755cd829ff684985cbd7da561d72ddf661755cb77c985d572f5f61d755cbf5d7564d72fd75d5735cbf6d7560972df765d874cbf5da561d32bf7684874cafdda021d32fd761d854cbf5d875d532fd721d754cbfcd8760932bf768c97606feda225d81bfe68097606fdda321d81bfb68887606ff9a021d81bf72a573606fdca85cd81ef761d73607ddd875cd819ff2a5726079fd875c981bf769d326077dc974c981ef761d32607fcd824c981bf768c985c6feda226171bfe680985c6fdda321d71bfb688875c6ff9a021d71bf72a1935c77dd9864d71f7761d935c6fdca85cd71df7661735c7ddd875cd71bf76a5325c77dd984c971bf769d325c7ddd874c971ff3609325c6ff4a960571dfd2a5815c7bf58760571f7d61d815c7fd59360571ff55cd815c7fd53260571df764d905c77dd9761d31bf7680874c else 0xc0f9002a039907740e641ae832105ee0bdc16682ac00a809c01230213039c05e804b01a402f4054008a00ea0180025803a807500a800cc0000000fff6899161fffd9264587fff6819161fffd9264187fff6459061fffda161c87fff6858760bffda061d82fff685875cbffda065d81fff68187607ffd9764181fff61d90607ffd9464181fff689985c7ffda261d71fff661925c7ffd8764971fff661825c7ffd8760971fff661725c7ffd875c971fff609905c7ffda061d21fff68587603ffda760580fff61d81603ffda460580fff61181603ffd825c580fff689875c3ffda161d70fff69d815c3ffd8760570fff689815c3ffd7260570fff61d215c3ffda261d40fff68587503ffda760540fff61d81503ffda260540fff5c981503ffd8748540fff68587483ffda261d10fff61d82443ffd8760970fff609815c3ffd825c570fff61d82503ffd8260540fff60971503ffd8460910fdf6559261f7fd9264587fdf6559061f7fd9264187dff6459061ff7da561c87dff61d9121ff7da061d85fdf689875d7fdda161d73fdf6958760bf7d875d582fdf695875cbdfda161d72f7f681875cbf7d875d572ff7685874cbfdda061d32dff65c97606ffda025d81eff25d87607bfda261d81eff68187607bfd8721d81bff68087607fdd975cd81ff761d736077fd9764981eff61d92607bfd8760981eff61d72607fdd974c981ff761d32606ffca764181dff65d90607bfd8764181dff65190607fdd7364181dff64990607fdd3264181dff689985c77fda066171dff660985c6ffda226171f7f261875c7dfda261d71f7f681875c77fd9821d71f7f61c875c6ffda221d71ff76a1935c7fdd9864d71ff761d935c7fdda264d71ff76a1735c7fdd985cd71ff761d735c7fdda25cd71bff2a1925c77fd9864971f7f61d925c7fdda364971ff764d925c7fdd7364971bff6a5825c77fd9860971f7f61d825c7fdd9360971ff75cd825c7fed9260971bff6a1725c6ffca85c971dff661725c7dfd875c971ff768d725c7fdd935c971ff75cd725c7fed825c971ff7661325c7fdc984c971ff761d325c7fdc874c971ffd2a5815c7ff49860571ffd69d815c7ff4a760571ffd61d815c7ff48760571ffd689815c7ff59260571ffd609815c7ff57260571ffd681815c77fd9864171f7f61d905c77fd9264171ff74c9905c7ff58164171ff7681874c77fca961d21ffd69d81487ff5a060521fdf69587603bfda261d80eff68587603f7d8761580fdf615846037fc9760980eff61d82603f7d7560980eff61182603fdd874c980ff7611326037fc9760580eff61d81603bfd8460580ff75cd81603fdd3260580bff6a171603dfd875c580ff74c971603ff5815c580ff761d31603fdd844c580bff2a5216037fc9748580eff61d21603bfd8448580fdf695875c3f7d876157)) else (if j<5 then (if j<4 then 0x905e0c0e0016eef5ddebbbd777aeef5ddebbbd777aeef5ddebbbd777aeef5ddebbbd777aeef5ddebbbd777aeef5ddebbbd777aeef5ddebbbd777aeef5ddebbbd777aeef5ddebbbd777aeef5ddebbbd777aeef5ddebbbd777aeef5ddebbbd768aeaa5d0fb99571f2e1bdbf2b76d6dc5663db35b5f2bebed635a9cb4d3686ecf459b5b2f3651ac80d8e0b125615a9465835b0295f3ebd2d77baea35c7ab63d694acc35872aebd59baa9b5446a6ad499a8cd5116a0953d6a7234d7a99ecc44a6394bca956d28ca4d7492a8e1d217a3c9470e89e5190a2bb44f287bd0b2a0db410e81150229fcd3ece7c94f569e353b7a755ce669c5537de6e6cdac58e735c268cccef991f31966224bde98112f7a5bf4b5d96552b96554ca769475281e4eec9aa92cb24ca47fc8b190fd210a407c7d38f411dfe3aac7108da91ace33746208ba516362ad452789fb1306242c44988090f221cf436b86950c5e176c2c38533099a110c1e5836505fe0a64107818501f6020c0207fdafec5fb63f427e0cfb95f623e9a7ccef841eeebdaa7adcf481e723cb178eaf151e0c3bd37752ee21db3bb3d7614eb81d56b29174d0e8b1cf839cf734ae5c9c96b8fa717ce22dc2338016f78de25bafb7356e04db19b4e36696c90d89dafa35b86b0ad525a8234c8692ad165a17b3f3675cce119ad3339661ecb95959329164bcc8d1909b1e9635ac3c18c1b1626282c48188430f06168c24d83030245fe2bf1d7d7af855eb6bcc578caef85daeba497222e115baab6656b32d455a36b3a1663ac9457c6b1cd60b2c735880b0595f19c714dbeaee55c7ab5c562eab255422a5a543c9b7d4fa26df5394a6814a92928520ea351455289250e2a11d3f827ab4ede19b139e26f74dbe9a4532aa6194bcc96a92b7256e4a769421258a46348608fad1cea36a46148b15149225f44be88b10fca1f9438c84250bc21454212831103b20163fa27de8f919ef03d687974efe9da63ac273e0e629c8938e270d4dfc9bbd37026d14d921af1355869c0d279a1c33e46720cca96fb32d66498c7e18a530d260d8c0197c72f045d3cb8996fb2d905a78b3a16382c0a576cadd131425d455b099a952729c45250a2c141327ae4ddc9ab133526284ba8949923c242447348d191821eae45187bc1101218a420082210081f863e647bc0f571e363b7c7458eac1d1639607128df21b9036186d38d861aca34c867b0cba190e312c5fe8bb816d42cb857d8ab614f4291c50a09ea139203a84ae8096133e25f804b00ea12fc2574075009601d403a802a039900a80e6449e053a127814e843c887910380150480089a1176226843c88461038207040e040e0c841fec3e400960f3c1ce03b587380e1c03a836906960cd819b0336066c0cd8190830785d30b40156c02a00330a74141c258005407320e64243042f081 else 0x210814aa181c1346810040a3d0e8c00a45368855810149268028748a211a04210293c305c08800117860a0040802051b91c405803860ae30060448240e00e1f1b91c42001604532188000530c04260081490030c1440010040a3b1812076430c00cd6200842052c884300718142e23080a00a080030000216230784804080a360c1600810040a360c0b88c24080036120500c18280a302803c8e26080030080e1b0c2348a2408002f0f0c05e4712040b1c2005e18038c011b11c60506000602e000117100b000284a20001401121005a18240028178609058988a302c0bc30487c702d0c0009101602a68300146a1c000e482a1143a6d181230028842050545a35348427048a44a68301346038c4626d100b438480070281c0016008b880580013c6050c000504000802e000116100b0002842200014011289438610814001822c421028002830000102880c2c828382004964003d0cb20922860ca350a9b5c048f040081e8d432c824784002080aa310a9a01220900a6d188409181807a6d0a8d5c048e0104d341946038d0802c109a4b2342687072014282c8283821641418078c0a0c180ae300448450c0b0425828844000920f4430d080a2010a8c01270800200284420019ac661900123a1000400509842c8043820049607204306820328d42a6d700e3c10034603902183030014da151ab8071e094da3100840c1a0900a6d1884071a09422692c8c40860f0401164022410b2010c01c6008704009089640860c8400d188440460c01668318c071419c6008602e18241400141801000280a280803c30581c5060030c011004090286020580430100002181401c60384058181481020b82460651a9b0207824681d1a0417048a00065368d02048c0c05808014da301c2041101800a6d1a04071c9b44a1918ab02848148c470c03c68102464430c05c6050ac300a219a026302472233404096301c666b190405048a4466b1904091791c4e310842100400182586070008c300800361004001a080a070c12070060c340b180f830482c0082008f830001c3c181c001e230900410145c181c02001204050386800481e04051686070082c4643100ac3000bc8e20178600178609050004c40370805c18006c42370805c1800604e0c0e0013118481000404e1a0407028b88836100b83000d8883611040017110dc241a2a82028f820281c3058020405038b430482c0f48a200204052787020080040482c0e00e1f2389c6811302008003c46110400130682008004c1004001e2307840280800360f11840580204372389820008c86220800260814000e900d0151000111a9144810004644198882000ac861a358805010007e181c020b1003c6e181c405d0c000712100a0580286091b860700800400f181807118607008004e301c201a0802000f04010586) else (if j<6 then 0x6010d08c30392c542e13864683c249634128642a301e9a091d19c3e302844670c9640078286c2050141d18280a0d19460700444212c8014050a884230c0a076302484cd270805e1f18142e109640050505c212e04400480464203012cd213180e0a23084b21100280a1a084b20028022c218d042050896341096010f1046c2052844b1b1046c20041542200e0f4617c1c261096140c034607068c00d181c222186842892c542004960e131046c2508962e238605c2518844b1f09c36310097091b0800e192c800a1b084b070784e3230022612184b200045c25180a4b461010e3805180fa321c5c2518808c6112c6c24028cc2438a84a321c808c4d12c7c211a0e01c6468963e108c0ac600480131f094603e30962e10184b0088844612c4a26108d8c8392c58210a8d0ca681c6c22338c0113084b20230022d1828010f098c008684259011801150807631099a8c1b084b200901c2e1096072063002321084cd03a318c011f084b2110318011a090c25900022c118c40a1430963410184b00898423006858c258d84230280342c6100707e10be0e13080c258384125181c1a10a28c2588840612c1c26108d8ca112c5c2004961e128c42c612c500c318d07118d0c008601863181c22790405e1824163430160102880b0501430f028301c3014050c0a0a0814050904050071812011a8c8907868c07e0a8c8915180002a1e8c9019880fc15190e2d18008911880102844600c2446211803090b8805a302430202430111a12230c140f008610818028d4d810247081100f460653412012310c6810041c2e23870200b181c370c03888131a12351205096341c5634240a1d118d828489c8a352388051689c605064200d0c0e0015860102864200f0c0e00178600008144610078607000b830001c0a220b060000890200e0c0e00171184054010401028e0903e0f1184802080a421217828060e32091f0600008144c46101401810006404080a071018000086c4c301cb4051023c80500789c3000148e47130c2210391a028607430260e05170c090388840d01422101c0a1c180e87028988c24091a0504e0c0e00270d88c6e110515028e02c18240007028d8dc46120400170d8d04a560407028e0702850641437118402e0c00430c1400410040a370c160ac10040a370c1582008145418280082008146c18280182008146a182a0401028b03054080205169144a182c140000c080a4d22060903802890202900a0380026051791460481f880b110f48818240f02005100a402c0400038145a1d181207a45129a1581014aa4118001ca24080a3b0c0a82200045e1e081640008a8302a08800117078205900022d0c0b02200045a4512860a20006040522060581100022d0c0240810380a350c0e050480481021e91440550e0546008148a30240f43a4536890 else 0xc2225854625a1c6c24318c4b8481481422308c686424024ba10f844651896c22021c7c24318c4b8381481422308c6a1103184b838e90625190e40462247e47128c4c61014663015990983d08303d118dc2e1c251635111680e33081c370c01120081456242e000a118d8284c1c0a2e230983050040b004111c8e26762a05173a4923a540a2f23898d050040a30240e05c306056242c0bc3c30263e3e180e050f1184c18240f864163484260b0786c68246e18280a1a0802050d8d0983b301782028ec463648142408000102888c000280a24081401890145a45120607000280302029346a1b303618168c0ba183c0a2d19120b43e0800051f91c4a6828020b028f4da18149902078d030481c004ca6c080a470f8c00080140230150148e1f1814306c2005e1f1814331015c62600456185c141b1b884c0d860566b0d04c40283c6e47118cc366014303b118782e30385811001c1a0880010d8cccc9014462026170063208143c08020f0e0440008783008143a1c080a40070b4381014800116860e02874302902040e16060520408022c0c02050f91c4e18280211028f43050068c050a060708f23880a00f0c0a3b2188c30288c3070143e47108dc3260146aea250e05078b5d078143643128c010b8146a300512870b8146e47108c01e18146234260f92028a0ae18061307088147050068c050a0606e1d341207028a920481c0a224802050c8c01e1c260e051a9144200280302a344a9a4d0c0401028948a210286000481e8d4d811503010040a270c02050c1440e181403021b8602008144e471387c600028800500c08a010040a1b0d8d02078145e4712040a00f0c0a3b1a13078103c0a370e040a0081458101601c3e30286a250d8c01070b44a180414251286016303852220880c366b18143d1286820700454220a1700050bc8e220814010007c36461999020283c5e1e1a05c40283c602c0311c6050ac600f0f1109058dc305803100a1710000507440605402270d19464381600161f8746c402c00891a8c891006c4a3224168c0021c7a690a10050050c1215229a44000240a0c0385480070e168c80014023f0f100b0002856202c0001070a0c0001414201cb8c4001084030140188e1f181430171009007181430308400630259a0a1f8680210000a0a1a0508000284220281800008b42058283460000a0e0b0a0ac402c1c2007100b070984e30280226109640050045465180a4be1a24803e228d8420308963612014661224500a310f46448a0144a328c871508c3a31011287258f842300787098392c7c270c8d0705100263e1387460481c9636109)))
def mo511H11 (j : Nat) : Nat := (if j<6 then (if j<3 then (if j<1 then 0x1e322000163c2000000000001a98a000000012b45c333c400000042ba00000000000000000000000000000000000000000001c04a000002b80000000000012bba0000000000000000000000000000e2d60000000000000000000163da000000000000000000000000000150be0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b42a0000133c0000000000000000000000000000000000000000000000000000e9c600000001a1a600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b43000000000000000000000000030a400000001ca5e0000000000008bbe000000000000000000000000000000000000000000000000133a00000000eb060000000000000000000000000000c438000000000001207e00000001038e94846b6ac2f8000000000000000000016b5e0000a9ff6279888c31580000000000000000000000000000000000016026000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0dc000000000000000000000000403c000000000000000000000000000000000000000000000000000000000000533e0000000193ec038a0001611c0000000000000459e354000000000001522ab198424400000000000000000000000000000000000000000000000000000000a36200000000000000000001e3468c08ec5600000000000000000001413200004254000000000000000000000000000100fa000000000000000000000001a98400000001e27e000000000000000000000000000000011190000000000000000000000000000000000000000000000000000060a4000000000000000021cc0001e3a80000000000000000339e000000000000000000000001c3e600000000000000000000000021a4000000000000d3d20000000104340000000000000000c4840000000000000000000000000000000013100000210800000000000101e200000bdc84182a60000000000000000000000000000000ea00000001a31c0001433188b36ba40000000000000000000000000000000000000000000000000000000000000000420a000000000001836c00000000000142d200000000000060ec000000019435486e00000000000000000000000000000000000000004100020120000200000100800800800004800160100000228020000b20800000a00000004000004c80a2014000902502484400002002400008002000480c8201008480003040008041000018281200 else (if j<2 then 0xa60000000000000000000000000000000000000000000000000000b1d6000000000000002a00000000000000000000000000000000000121e720f600000000000194740000000141d4000000000000000000000001c140000000000000000000000001290400000000000000000000000000000000242400000000000000000001624000000001c3280001e48800000000000040e0000000000000000000000000a01400000000000000000000000000000001145c00000000ebfa000121d0000000000000000000000000000000000000000000000000000000000001605a10b480a6000000000000000000000000000000000000000000000000000000000000000142a011f60000000010cfc314000000000001f18a0000000000000000000000000000000000000000013000000000000000000000000000000000820c0000000000000000000173ba200a0000000183e200016444000000000000000000000000000000000000e158000000000000808a000000000000000000000000000000000000000000000000000000000000000000000001683a00000000000000000000000000000000000000000000000000000000000000000000000141b54c2e0000000000000000000000000000000000000001c4740000000000000ad00000000000000000000000000000000000000000688e00000001619800000000cbf00000000000000000000000014b74000000000000d1680000000000000000000000000000000000000000000103020001e94c0001616c0000000000000000000000000000000000000000000000000000000000000000c0e7e09e0000000000000000000000000001cc6b4b100001c1900001d3160001f1ae00000001411a0000000000000000000000000000e34c0000000000000000000000000000000000000000e39e0001ec86000000000000000000000000000000000000000000000000000000000000000183d20000000000000001037a0000000000000000000000000000000060500000000000000000d41a0000000000000000000000000000000000000c3e000068c400012abe00018036409a0000000000000000000000000000000149dfc0020000000000000001cb400000000000000001826a000000000000000144064b3e00004c6400000000000000000000d2480000000000000000000000000000c41c0000000000000001a3fe00000000000000002b0a00000000a296000000000000000000000000000000000000000000000000000000000000000000000000000000000c3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e41e00000000000000000000000000008234000000000000000000 else 0x8bb20000000140c80000000000000000000000000000000000000000000000000000000000000000000000000001e83c0000000000000000000000000000942c000000000000000000000000000000000000000000000000000000000000b2c200000000000000000000000000000000000100c00000000000000000000000000000000000004b6200000000000000000000000000000000a18a0000000000000000e9320000000000000000000000000000000000000001b3f400000000000000000001a42e000023bba2200000000000000000000000000000000000000000000000000000000000000000000000000000d3e80000608c0000000094620000000190c18ba9ab1e00000000000000000000000000000000000000018a98000000000001733201fe000000000000000123480001407a000000000000000000000000000000000000000000000000000000000000827400000000000188dc000091bc0001c34200000000000000000001c01a0001901c0000000000000000000163f20000c0c641c200000000000000000000000181680001a1240001f40f494400000000000000000000000000000000000000000000000000000001644a000000000001c2a20000000000000000000000000000000000000000000000000000000192f000000000000000000000000180300000ec32000000000000000173bc00000000000000004206000000000000000000000000000000000000000000000000000000000000000053de00018c040000000000000000000000000001219bc92e000000000000000000000000942600000000000000000000000000000000000000000001635c00000000000000000000895633a2c2880000830a0000000000000000e1ea0000000000000000000000000000000000000000cbe800000000000000000000000000000001d1c800000001b488000000000000000000006380000042478260000000000000000000000000000000000000000000000000e0b28372000000004067e456000000000000a1b800000000000000000000000000006a620000000000000000000000000000000171ea00000000a1ee00000000a226000000000001a47a000000000000000000000001204e0000000000000000000000000000000000000001448c00000000000000000000000000000000000000006318000000000000000000000000000000000441b15e0001c2f0000000000001cb98000000000000b0fa00000001f1be0001a3bc00000001634a000000000000000000000000000000000000002e000000000000000028120001ab)) else (if j<4 then 0x1626200000000000000000001a3240000000033c929a4000043a40000000000000000000000000000000081b0810400002204000000000000000000000000000000000000e2a600000000000000000000000000000001c21e00000000000169520000000000000b9c000000000000000000000000000000010236000000000000000063ec000000000000000000018214000000000000000000000000ab020000000000000001e2ce00000000000000000000c1480001e28c000000000000000000000000439800000000000000000000000000000000000000000000000000000000000000000000000162560000cb0800005300610c00000000000000000208000042940000d2d000000000000000010a8e00000000000000e2000000000000029188d4a339609c0001c0fca0b60000000000000000000000000000000000000000000000000000000000000000a02200000000000000000000000000000000000000000000000000000000000000000000000000019032d0f683b411a800000000000000000180000000000000000000000000000000000000000000000000000000012a6c00000000b3f8000000000000000000000001211220d20000000000000000000000000000000000000001e2f2000000000000000000000000000000000000a0f38b9000000000000071fa0000000000000000000000000001640e000000000000000000000000000000000001c87a000000000000000000000000000000000000000000000000e21a000000000000000000000000000180940000000000000000000000000000000000000000000000000000603a0000000000000000000000000000000000000000000000000000000000000000e3a2000000000000000000000000000000000000000000000000000000000000000102d00000000000000000000000000000e0fe0000000000000000000000000000000000000000000000000000000000000000000000000001b1b20000000000000000e0d600000000000000000000000000000000000000000000000193e5d17e0000000000000000000000000000000000000000c12000000001a1e000000000000000000000000000000000000000000000a3d8a2e763e0a3600000000000000000c3260000eacc0000000000000000000000000000abf80000425a00000000000000000001ab20a0ac441400000000000000000000000000000000615e000000000000e09800000000000000000000000000000000000101360000000053ac000000000000000000000000000000000000000000000000000000004ad40000000000000000000050ea000000000000a378000000000000000000018a1200000000000000006c38000000000000000000000000000184520000d414000000 else (if j<5 then 0x6816000000000001e2cc00000000000000000000000000000001e26e00000000687c00000000000000000000000000000000000000000000000000010bf3e9c200000000000000000000315c000000000000000000000000000000000000000080d800004c0608520000e43000000000000000000000000000000000000142d4000000000000000000000000000113d6000000000001c882000000000000000000000000000000000000514c0000000000000000000000000000000000010301ea060000000000000000000000000000000000001314000000000000000000000000c1ae00000000a21c000000000000000000000000d42800000000000000000000000123200000000048200000000181ce0000000000000000000000000000000000000001645400000000000000000000000000000000000000000000cb320000cc0000000000000103b2000000000000000000000000000000000000000000000000000000000000000000000000000000000b80000000000000000000000000000032fc000000000000eaea0000000000000000000000002b720000000000000000000000000000c30e0000000000000000000000000000000000000000000000000000000000008c6c0000000000000000000000000000000000000000000000000000000000000000000000000001a2b7530222f400000001c0de00000000000143b0000000000000000000000000000000000b18807400000000000000000001c3060000000000000000000020480000000000000000000000000000000000000000000000014bbc00000000000000000000000000000000000000000001a82e0000000000000000000000000000000000000000000000014aac0000000000000000000000000000000000000000000000008a6fa82a00000000000000000000000000000000000000000000000000000000a0ba00000000e1ca00007288817f71e56064000000000000000000000000000000000000000000000000000000000001cc240000000000000000000000000000000000000000000000000000000000000000000000000000000000000001b2ce00000000000000000000000000000000000000000000000000000000000000000000000000010b8a000000000000000000000000000049d2000000000000000000000000000000000000000103ac00000001499c00000000000000000000000021fc000000000000000000000000eb46000000000000613c0000918e0000000000000000000000000000000000000000000000000001ec0a2a0c0000000000000000000000000000000000012be20001abf4000000000000000000000000000000002b76000000000000000090bc0000000000012ac400000001cb5800000001d18000000001a49000 else 0xe15da057148000000000000161bc00000001d466000123f600000000000000000000c32a0000000000000000407600000001845c000000000000000000000000000000000001eab80000000000000000000003ee00002b5000000000000000000000000000000001014c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000600004986000000000000000000000000000000000000000083a600000000000000000000000000000001a3840000000123de0000000000000000000000000000000000013478000000000000000000000000000100e80000000000000001a9540000000000000000000000000001881c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e2fdac42000000000000000000000000000061dea1c800000000000000000000000000000000839c0000000000000000000000000001c3fa00002bd4ac62000000000000000110c6000000000000000060cc00000000000144800000000000000001f16a00004b6000000000000000000000000000000000eadc0000000000000001ea5c000000000001c268000094860000000000000001805c0000f1de42bfe12600000000000142520000000000000001a449a494000191ac00000000000152fe0000000000000000000000000000000000016492000000000000c3b60000000000000000000000000000041a00000000a11ec1bf8410000000000000000000000000000000000000000000000000000000000000000000000000000000000000e1460000000053384c1c0000000170fc808800000000b1c56478000181d600000000d30a0000000000000000000000012b6e00000000c1020001f16e00000000000073a000000000000000000000000000000000000000000001224a00000000000000000000000000000000000133b8000000000000e1e400000000000000000000000130b200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001237e0000000000000000000000000000000050f3919c00000000e176000052e6216a0000000000000000000000000000806e000000010a71418e000000000000000000000000000000000000c486000000000000000000000000000000000001f422000000000000000000000000e8ea0000000000013454000000000000000000000000000000000000000000000001f0460000833600000000000000000000000000000000e43e000000000000000000000000000000000000000000000000e3c800000000a13ff2960000000000000000a341e42a0000000000000000000013c000))) else (if j<9 then (if j<7 then 0x1c29f83f86144000000000000000000000000000101f8000000018416000000000000c18800000000000000000000000000000000000000000000000000000000000000000001f3904472000000000000000000010c3c08c2000000000000ebb00000000000000000000000000000000000000000000028740000000000000000000000000000000062120000000000000000000000000000682400000000f40c000000000000000173dc0000000000000000000000010462000000000000519600000000000000000001607c000101620000000122d9a1560000835a000013c43336f0b600000000000000000000000000000001e2580000000000000000701a00000000000000000000000000000000000000000000000089ca00000000534000000000000000000000000081b20000000000000000000000000000403e63820000c0820000000000000001d4200000000063e40000000000000000000000000000000000000000a3120000000070d324760000000000000000000000000001e0a00000000000000000000000000000000000009186000053be0000000000000000000000000000205e0000000000000000000002fe0000000000000000abadc426000000000000000000000000000000000000000000000000000000000000000152b6000042c00000000000000000000000000000000001a200000000000000000000000000000000604400000000000000000000000000000000000000000000000000000000000000000001240c00000000000000006286000000000000000000000000000000009240948a0000a16e00000000000123a0000000000000609600000000021600000000000000000000000000000000000000000001e3b8c33400000000e27229b000000000000000000000000000000000000000000000905a000000000000000000018c40cb4200000000000000000001046c0000000000000000000000000001c1dc000000000000000000000000000000000000c0b000000bece8da00000000000000000000000000000000000000000000000000000000000000018ace00000000000000000000000000018028000000000000000000000000000042ac0000e99e00008c96000000000000000000000000c86800000000000000008413946c000000000000000083f40000000000000001aa0800010376000000000000000000000000000000014466000000000000a304000000000001829cac4e8461a3e9227a0000000168fc00000000000000000000000000000000000000000000000000000000c3c00001a24c0000000000000000000000000000000000000001abce0000000000000001c45000011413c282000000002bb4000000000000000000 else (if j<8 then 0x1c0f40000000000000000000121d20000ec8000000001918dc068000001420000a3900000000000000000000000000001e04000000000000000000000000000016a6962bc0000000000000000000133cc00000001285c0000890000000000000000000000000000000000943600000000000000000000000003682a3400000001ebd0000000000000000000000000000000000000613a60db01966bb600000000000000006951ac1a000000000000000113fca35800000000000000000000000000014250000183520000000000000000000000004c5e0000000000000000a0ae0000e27d20040000237c0000000000000000000000000001c90600000000000000000000000000000000000000016b3c000000000000000000000001a01e00000000000000000000000000000001a1fa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a350000000000001c16000000000000000014187130e0001e3866aa000000000000000000000000000000000000000000000000000000000000060920000000000000000000000000000000000010a420000000000000001a3080000000000000000e00c00000000000000000000000000000000000000000000000000000000606a0000000000000000130660d40000000000000000000000000000000000000000000000000000000000000000000000000000000061c0e3640000000000016034000000012a185388000000000000000000000000036e000000000000493400000000000000000000000000008bc8244200000000000000000000000000000000317a000000000000000000000001cb66000000000000000000019201623000000000000000000000000000000000000000000000d1f80000000000015416000000009188000000000000000000000000000000000000000000000000000000000000000020d01472222e0000000000012223a28a00000000000000018122000000000001e22c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000627000000001f3aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000069ae00017156000000014a640001814a0000000000000000000000000000000000000000000000016be600000000000000000001c0e40000000000000001c04c000000010c540000000000000000000113c600016012000000000000a26c0000000000000000000000000000000000000001c42c000000000000000000000000000000000001217800000000000000006032eb1a000000000000e1a800000000f476000000000000000000 else 0x1e43c0000f192000000000001e3cd202c00000000000000004264000000000000000000000000000089da000000000000000004280000000000000000000162a400000000d40a00000000ac8200000000000000000000000000000000000000000001446861ac00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001044d1150000000004b0e000000000000000000000001c2c932e000000000000000000001a2b1f2a400000000000000000000000000000000000181c400000000000000000000ab1c0001d468000000000001738a0000000000000000000000018bb99258ea0e000000000000000000000000000000000000000000000000247dea9100c2000000000000000122ca00000000000080f000008a1000000000000000000000000000000000000000000000c2e200000000000028a6000172d868b000000000000000000000f15a00000000000000000000000000014164e224000000016b14000000000000000000000000619d282800000000000000000000000000000000000000000000000000000000000000000000000000000000e89a0000000000000000000000000000839600000001a1820001040a000103880000000000018280e30c0000000000000000ec66000000000000000000000000000000000000000000000000c047f41821720000000000000000e17a0000406200000000000000000000000000000001b16600000000000000000000000081b600000000000000000000000000000000000162e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000815200000000000000000000000000012c5de87800000000000000000000000000000000000000000000000042c40000000140700001abee00000000000000000000640200000000000000000000000000000000a3aa000000000000000000000001e3d600000000000000000000000000000000000000000000000000000000000000000000000000000001c0bde31e000000000000000000000000000000000000d042000000000000000000000000000000000001e000000000000000e90800000000000000000000225c0000f4020001c3c6000000000000000000000000000000000000000000000000000033f000000001810a000000015174000000000000000000010a1400000000000000000000000000000000000000000000000133ae000000000000e08000000000000000000000000049c80000000000000000000073340436f1d80000000000000000000000000000000000014bfe0000000000000000000000)) else (if j<11 then (if j<10 then 0x9c0000000000000000000000002b4a0000000000000000000000016bca0001c2b200000000000000000000000000000000000040f8000000000000000198dc000000000000000000000000000000000000086a0000c29a00000000000000006392c2ef3194000073da000000000000000000000b7bc150000000000000000000000000000000000000000000008b64000000000000000000018356000083cfa45f4c6e00000000000000000000000000000000000000000001802000000000000000000000000000000000000000000000000000000000000000008c5a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000120aa0000000000000000d16c0000000062ae00000000000000000000000000000000000000000000000000000000000000000001a15a447e00000000f31220ca0000000000000001423a0000000000016248000000000000000000000000034400000000000000000000000000000001cb3a0000000000000000000000000000000000000000000000000000000000000000000000000001011000000000000000000000000000000000000000000000000000000001a31000000000c06c000000000000000000000001294a0000000000000000000000000001e0720000000000000000ab840000000000000000000000000000000061660000000000000000000000000000000000000000000000013408000000000000000000000000000000011268612c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c2dc0001741c000000000000000000000000000000000000000000000001205200000000000000016058698800000000000000000000000000000000000110b124220000000000000000000131cdec7200000000000000000001528a42c600000000000000000000000000000001c1e8d3e600000000000000016c2a20a2000141340001941e00000000000000000000000000000000000000000000d44c0000000000000001a2180000000000000000c3660000000000000000000000000000000000000001080800000000000042980000f3040000000001740086000000000000000000000000000000002b5a000000000000000000000bc5e3af8a5851e80001c31a000000000000000000000001e238000000000001f47c000000000000000000018090000000000000000164080001600e00000000000000000001eb700000000081abe83e0001048e00014128000000000000000000000be4418c000000000000000000000000000000000000000000000000000000000000211600 else 0xa28400000000000000000000000000000000000000000000000000000001e19552f4542e0000000000000000000000000000000000000000207851d4000000000000f404000000000000000149820000000000000000000000000000000000000000000000006c34000000000000000083c4000100180000000000000000000000000000b1fe000000000001822a000000000000000000000000000000010420f0ae0000000000000000000000000000000000000000637121c6c01c8c580000000000000000000000000000000000000000000000000000420e00016211212a0000000000000000000000000000000000002894000000000000000000000000000000000000000163160001a4820000000000012a0a0000000000000000000162c200002ad2000000000000c3be0000000080ee000000000000000000000000000093e2000000000000000000000000000000000000000000000000000000000000000000000000000000000000019e00016114a36bf308000000000001a35e0000000000000000000000000000000129cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000122e80001109600000000000000016bc7cc8400000000000000000001048a000000000000000000000000224e00000000000000000000000000010038000000000000000000000000000000000000000000000000000000000000000000000000000091f000008880000000000000000000000000000000000000000000000000000000000000000000000000000000018af2000029d060600000717c00000000000000016b820000000000000000000000000000c39a00000001e18400000000000070d000000000000000000000000000000000000000000000000000000000000000000001e99a0000000000013170000000000000000000000000000000000000000000000000000000000000000000000000000000000001ab68000161f20000000000000000000000000000000000000000000000000001026600000000000000000000000000000000e0bf514e0000000000000000000043dd09a20000000000000000000000000000000000000000c1540000000000000000000000000000000000000000000000000000000000000000000000000000b3fe00000000000000000000000000000000000000000000000000000000000032ae00000000000000000000d424000000000001b3d40000000000000000000000000000147fa01600000000000000000000000000000000000000000000c1f00000000000000001a19280dd03ea0000000000000000000000000000000000000000643a000000000000000000000000000022aa00000000d2) else (if j<12 then 0xe0080000000000000000000000000000000000000000000000000000a229c32e0000000000000000000000000000000000000000423200000000000000000000000000000001e8fe12de000000018873a02451ec0000000000000000000000000000000000000000000000000000000000000000000000002243e8d60000223e000000000000000000000000000000000000cc7400000000000000000000000000000000205400000000000000000000000000000000000000000000000048660000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000150c20000000000000000a39400000000000000000000000000000000232c000000000000c8f40000c4960000000000000000000000000000cc22000000000000000000000000000000000000c3d0000000000000000000000000000000000000000000000001a470000000000000000000000000000000000001e138000113a800000000e44e0000000161ba0864000000000000000000000000000000000000000000000001845bc46fa042000000000001a2b4000000000000000000000001330c00000000000073f2c200000000000000000000000000433c0000000000000000000000000000000000000001a1da42df90738baf03f0000000000000000000018374000000000000000000000000000000000000000000000000000168f200000000000000000000000000000001217c000000000000000020b862a80000000000000000000000000000000000000001c1d8000000000000000041a0000102e40000046a000000000000000000000000000000000000000000000000000000000000433be17180840000000000000000000000000000eb8600000000000000000000000000000000000000000000000000000000000000000000000000000000000000008a86000000000000000000000001808e000000000000000000006bc20000ec69a2fa014e0000000000000000000000000000000000000000a0c46276000000000000000040100000000000000000000000000000000000000001e3fc000000000000000000000001ead6000000000000000000000000833e84644a4a0000000000000000a38c000069e000000000000000000000000142920000000129c4000063d40000000000000000000000014202304f028e0000000000000001a0b44a80000000000000000000000000000000000000000000000000000000000001cc7c0000000000000001a0ce000000000000000000000000000064040000000000000000000000000000000104460000000000000000000000000000000000008118000000000000000000000000000000000000000193ca000000000001d20200 else 0xf8ea00000000000092bd2432000000000001810e0000000000000000000000000000000000000000abea00000000000000000000000000000001703a000000000c3a0000000000000000000000000000000000000000e34e000000000000012e0000000000000000000000000000000000000001a1000000d1fd21f7e2da00000000000000000000000133d8000000000000123293c2000000000001b43200000000000000000000000000000000000000000000e9300000000000000000000000000000000000000000000001f40001ca2c0001b0ca00000000000000000000000000000001225e00000b880000000000000000000000000000000000000000a0a8000000000000000000000000000000000000e10673e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e23d82f600000000000000000000000000000000000000000000000000000000000000000000000094960000000000000000000000000000000000000000cb7e000000000000000000000001ec7e0000000043cb906a0000000000000000000000000000000122edc1ec0000000000000000000000000000000000000000000000000000e2ea00000000000000016c02000000000000000000))))
def mo511D12 (j : Nat) : Nat := (if j<1 then 0x41c30d11091b0c00043444246c3010b110904161a0d0600441c4420580010c228690890c00043c7691b3467118145a9147448110143a90bf4291081417903b4060ff93f88fb73e80f793d28f273c30eed3b28ea33a10e713938e2f3850df53728dab35f0d5d34c8d1733e0cdd32e8c9f3200c653128c273030bf12f48ba72e30b752d88b532d10b2d2bfcb0e2bfcae82b54abe1be0aab2a70a81291ca5a291ca2428149f213d49d726d099525e895324e092524388f723708c1227888721c085120a880b1f907cd1eb87871d907451c787071be06dd1b286ab1a30675198864b18c061918185e717105ad165858715c055514d851f14204f513484bb129048d11c844b10a04110fe83e30f103ad0e5837b0d703490cc83130be02dd098c2ca0acc2a00a24276098c25008f4226083c1f007541be06bc18805b4156051c1340474106041810603bc0d402f40aa023c074017403a007c01f0001ffd9261fffb22c3fff64187ffec390fffd9121fffb0ec17ff61d72ffecbb03ffc97607ffb0ec0fff21d81ffec9303ffd82607ffae4c0fff64181ffecc2e3ffc985c7ffb0eb8fff21d71ffec92e3ffd825c7ffae4b8fff64171ffec3a43ffd87603ffb08c07ff60980ffeb9301ffd81603ffae2c07ff48580ffec3ae1ffd825c3ffae4b87ff60570ffeb8ae1ffd215c3ffb0ea07ff60940ffeb9281ffd81503ffae2a07ff48540ffec3a41ffd84483ffb02907ff5c520ffec3a21ffd84443ffb04887ff5c910ffea1221f7d9561fefb2a43ff764c87bfec910ffed9221effb2243ffd64487bfec810fff99021fefb0ec2fdf21d85fbec3aebf7c875d7fbb30b9ff726173feec3ae7fdc875cffbb24b9ff764573feec82e77fc9760befb0ac17df5d582feeb9b057fd985caff930b977f61d72fbec2ae5f7d755cbfbb26b97f75cd72ff6c12e5fdd874cbfb90e995ff25d81dfec3b03fdd73607fba64c0dff66171bfe4c2e3dfd875c7fbb26b8ff75cd71fee992e3ff5815c7fbb0e98ff721d31feec1263fdd724c6ffb3090dff26121bfecba437fc97487fbb2690ff75cd21ff6c1243fed72487feb0290dff25d80dfec3b01f7d85603efaeac06ff61180feeb9b01fdd32603fba62c05ff66170bfe4c2e1f7d855c3efaeab87ef25170efeba2e1fdd735c3fba64b87f74c570ffcc02e17fd98502ffb2ea07df61540fbebaa81fdd73503fba64a07f74c540ffcb82817fd98482ff930905ff65d20bfe4ba41f7d85483efaea905ff65120feeb9a41fed72483fda84907f74c520ffcc02417fd98442ff930885ff65d10bfe4ba217fd94443fbae6885ff64910fee99221ff571443fea82887fe60110ffcb82217dd9321efdb2443dfd64487bfcc810f7dc985cfbbb0eb9fd761573faebaae77dd974cbebb0a997d75d532fe6c12657dd974c7fab0298df764d21 else (if j<2 then 0x305c1646261829191068c178904000a4418483e4416205829188998d0436140b244646241056300c90f86170480022e46205e18003e30480c11506170480022e46205c1054923008292140187901603880a808d04585e183828480a34110890403878c14308c183e46241058e85118d841786001242200e3048505800603928d880a178712003e16184858989860e1600140a8440605802104e3050e238818841c16342210083e1e3048f101708018497130e8d865420084a5e1a3038f100e010986120b8c1402845c2060483a163050f10162309869614848c025422100e303c60d08800f84968d183c200a583a3460d080e0a00038c85184422103c663008d080e0296848d1838f21616184858c3d840e18161230f46060385a10502903c1884170c1430841806341048c20880e198c120238580e2618048234144829421068d0430123080604a3008b91898c84221038006860e00184e18583800b860e12160002843e1838006178612000e2e18380800991881601042e30483c109040a0e1848381418d000d110805041217060e00481418380091108120f050634004444201860100800e09060e0026443620021058d9013880e0b010c844244322028021858e0d9189858616364048381620302e1801391890c0b861636462210588130c0e840a2a4222121858a120e04863416364036202e1858c0401110905070d1a40104c183800a16000b040e2e18483e46263410e12908616880e00040a4a421a2230126828e12160e018791898d044848380c1000b86160191898d043a42205802185630100921686000f8c12040240021a42226a3010e12160e018791898c044c4420580410b0402001c423420041058d110904162640303e20641058f900c120f8904003e4620641058a050c0e2222421a208858a90060e880416364036241058b9189041626461e2430281058e16040200198d860e405446361848b88161400842e3210486898c18120e2858100218c848c881884868c129a3a2058500210a19858d861228161838009101708018c14028444203e321048a0f84198c1228084e306038a080084878c1230400022104a6a183a312101608018c140284442056361848b09858c180e280610663038b081602018c84183c2066321038a08038c180e28203a126a3060c081602018c8418380e30603880c05861216283038102e184800f8612041814163060100e1c3038d0c840a12201060380858a04861216261860485058a0e180216206210505880d861612206634104880e04022000280066341048a181600058c0e203a206006341038c06018c04122e184858620880086189a128c044e180c46301048c898c04120e2e3410486898d041220485a183800a12160e018628485c180038b110904170600344420580010b8c120e042444241 else 0x8d918985861630485838061e46263211289858d86122c12100e183800c8586000e0a2c321646202806185919188850d8413860e164e34164620d82c90f861504020a284e1e30385e4620002c11506140104020a307a))
def mo511H12 (j : Nat) : Nat := (if j<6 then (if j<3 then (if j<1 then 0xd191000000000000000000000000c0e800000000000099a800000000000000000000000000000000955c0000000000000000000000000000000000000000007e00000000516700000000000000000000000000000000722421b3000000007111000000000000000000000000000011790000000000000000000000000000e14f000000000000000000000000f0cf20620000011500000000000000000000c20800000000000000000000d13d000000000000000000000000000000000000000000000000000000000000000071f7598000000000000000000000f0230000712d000000000000000000000000000000009497000000000000f0170000000000000000000000000000000000000000000040a600000000000000000000000000000000000000000000c02f000005b7e1f000000000000000000000000000000000000000000000000000000000000000000000d1a0000000000000e4490000000095c700000000000000000000000000000000e16f0000c59900000000500a000000000000000000000000000051250000000000000000000000000000000090530000000000000000000000000000000000000000000000005a27d002000000000000000000000000000000000000f078e164058f0000000000000000000000000000000000000000218b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003238e0f5000000000000000000000000000000000000a12a80e4000000000000b08b000000000000000092090000915df89600000000998f00000000000000000000000000000000000000004a000000000000000000000000000000c2312084000000000000000000000000000000000000000000000000105c0000e074000000000000000000000000000000000000000009de0000000000000000000000000000000000000000e0b10000d4ef000000008a23000025ac00000000000000000000000000000000000000000000000000000000000000000000000000000000000000006d2f00000000aa34000000009020000000000000000000000000000071ab000000000000b054607d00000000e0c30000355f0000000000000000117b0000000000000000000000000000000000000000000000000000000000009047e0160000908ea401f5980000000000000000000000008221398e00000000000000000000000000000000000095a300000000000000000000000012320030103200001020111100011001112500000021000200001200000000110100220010210002010101021000010000010040001101002000001102300011001010500000100141000017201b100010001000101401010011100000111010102000022200 else (if j<2 then 0x89e500000000b614000041be000000000000000000000000000081140000000000000000000000000000000045ad00000000000000000000d518000000001089410d0000b423000081a90000401cf07b60de000000002a320000000000000000000000000000e434000000000000000000000000000000000000000000000000000000000000000094f0f2250000000000000000000000000000000000000000000000000000000000000000a0af00000000402600000000000000000000000000000000651100000000000072260628000010d22822d541a04a00000000000090330000000000000000000000000000000000000000000000000000000000000000000000000000e0e7000065570000000061b80000000022050000f58000000000413100000000000094ad1619000000000000000011d500000000000000000000000000000000589a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009a2000000000000000000000000000000000000000000000000000000000000000000000000065c52156000070a9000028ad41ef00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000071c90000c52c0000000000000000000000000000000000000000000000000000000000000000e11c0000000000000000000000000000d8c50000e0e6000000000000000000000000000001b40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000317e00000000000000000000000000000000000000000000a1df00000000000000000000000000000000915e00003d300000000000000000000000000000000000000000000000000000108100000000906e000000000000000000000000d1e30000c4bb000040f22137b0a00000216e000000000000000000000000000000000000000000000000000000000000000000000000b895045c00000000000065f90000000000b500000000000000000000000000000000723071220000000000000000000000000000000081b900004a04000000002a3b000000000000000000000000000000000000121c0000000000000000049c0000512ce52d920d000051c600000000d1170000000000000000000000000000000000000000000000000000000000008e11a45400000000000000000000000000000000000021db20aad4f9000000000000200800000000000000000000000000000000000000000000d49a000000000000000020df000000000000308c0000000000000000000000ea40710000000000000000000000000000c16d0000 else 0x409300000000000000000000000000000000000000000000a4f400000000000000000000000000000000000000000000000095f809d9a03d717a0000000000000000000000000000000000000000000070b6000000000000000000000000000000000000000061660000d98600000000000000000000e8370000d46c598400000203000000008126000000000000e0ee000000000000000000000000000000000000000000000000000000000000000000000000000024e1341c000000000000c1cc000070d40000000000000000000000000000000000000212000000000000000000000000299a00000000000000000000000000000000000000000000000000000000c0820000000000000000000000000000000000000000000000000000000000000000b15b00000000000000000000e0ab0000000000000000000000000000000000000000560f00000000000000000000000000000000000000000000000000000000000000000000000000000000a5890000000000000000d22fb0be000000000000000000001977000000000000000045280000000000000000000000000000000000000000000000000000000000000000c1a70000000061a2000000000000000000000000000000000000000000000000000000000000000000000000b8140000000091290000051a0000885a18a80000000000000000000000000000000000000000220c0000206b00000000000000000000000000000000000000000000000000000000000000000000c1330000000000000000b09900000000000000000000607700000000000000000000000000000000000061080000000000000000f524822b0000000000000000000060bd00000000000000000000000000000000000000000000000090da0000000000000000000021ac00000000000000000000189c000000000000000050d8000000000000000000000000000041ed00000000201b000000000000000000000000000061a60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021ea000000000000e9690000f552c23d00000000000000000000000000000000000000000000000000000000000000000000e4fc09240000000000000000000000000000000000000000000000000000000025da0000000000004193f0c78a1b000040800000000000000000d57c0000415108a3000000000000000000000000000000000000000000000000d47ed9a5a19550ca000000000000120e0000000000000000000000000000a0b8000000000000154000000000354800000000000000000000000000000000000020dc00006a3a000000000000000000000000000000000000000025f6802d00000000000000000000000000007237)) else (if j<4 then 0xd1f1351b00000000003e00000000e0f340ae0000000000000000000000000000000000000000000000000000000035bc000000000000000000000000000090320000b9a10000258500000000000000000000000000000000000000000000000000000000000000000000c85800000000000091470000000000000228656a00000000d1410000000020888059000000000000f51d000000006428553400000000000000000000000000000000000000000000f584000000000000000030a7000000000000000032160000c22700000000000000000000a4f500000000e0210000000000000000000000000000000000000000000004ec2239000000000000000000000000000000000000000000000000000000000000000000000000000025dc0000000000000000d97f000000000000000080cb0000000000000000000000000000d1cf7046000000000000b04cb1836138000051c3000000000000000000000000000000000000000000000000000000000000000000000000a4b10000000000000000000000000000000000000000000000000000900100000000000000000000000000000000d96200000000000000000000000000001985000000000000000000000000000000000000000000002051a14b0000b5810000f92100000000000000000000900600000000000000000000e04e0000000000003a330000000000000000000000000000000000000000000000000000262a000000000000f542000000000000000000000000d4700000000000000000000000000000000000000000c545686a75ae8030000000000000000000000000e46fa0940000000000000000000000000036000000000000000000000000000000000000b15f55e175e0193200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000061f9513500d600002620a0e90000000000000000d067000000000000000000000000000011a31610f0cd00000000000000000000000000000000a08600000000000000000000000000000000000000000000000000000000000000000000000000000000000039f60000000000000000000000000000000000000000e4dcc5c1000000000000a087000036130000000000000000000000000000f9e200000000d0f900000000000018b40000000000000000000000000000787d00000000000000000000889100000000310559e40000000000000000000000000000000078b700000000000000000000603900000000000000000000000000002a1000000000000000000000000058db0000000095cb0000a19b000000000000000000000000a0310000b54e507ce4e0000090900000 else (if j<5 then 0xc97b00000000000000000000a5f70000000000000000601000003a24000000000000614a00000000000000000000000000000000000000000000000035df000000000000b1b5000000000000d132000000000000000000000000000071ce0000a565562c0000f42f11100000000000000000000000000000000090b0000000000000000000000000000000000000000000000000921900000000000000000000000000000000000000000000087b000000000000000000000000000061010000560a00000000000000000000000000000000e0fe08a60000000000000000000000004187000000000000000000000000463600000000e0fd000049720000000000000000201100000000000000000000000099a000000000b2170000e1f500000000000019230000000000000000000000000000000000000000000000000000000000000000000000000000000040c5000000000000000000000000000000000000253e00000000000000000000000000000000000000a5a01330d90000000000000000010f00000000b00eb5fc0000696c00000000000000000000000000000000e96b00000000000000000000000000000000000000009171000054840000000000000000000031d4d02900000000213bfa1f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f92f000000000000000000000000e604d119000000000000000000000000000070ed000000000000291f00000000000040bb94e2b59aa15800000000000000000000000021af00000000000000000000000000000000802a000000000000000000003a36000000000000000000000000000000000000796100000000000000000000000000000000a1750000a8b10000000000000000000000000000000000000000b05b0000c48e000020b354fb00000000000000000000000000000000000000000000000000000000e8410000857d0000f152000000000000000000000000000000008a22000000000000000000000000000000000000e0fc000000000000000000000000000000000000211300000000000000000000000000000000000000005136d109f91e0000e5fa110ae4488038d17c0000000000000000244d01a894e9000000000000649000000000000000000000000000000000b4cf00000000000000000000901f00000000000000000000a5690000c57200000000000084d00000046540f10000115c214c0000000000000000000000000000000000000000c08aa09800000000000000000000000000000000a86800000000f22da5fb000005ec0968b044a53c461bf91d00000000b597000025e8000000000000e62e00000000000000000000000000000000000000000000000059aa0000a09d else 0x50d161940000000000000000000031bc00000000000000000000ca1c000000000000000000000000000000004a0d000000000000000000000000000001550000000000000000000000002170687c7107000040050000ba2595b80000616a000000000000000000000000000000000000000000000000000068af00000000000000000000000000000000000000000000000000000000000000000000b0030000c21d00000000000000000000900d00000000b1f300000000000000000000796d0000000000000000000000000000563d0000609f0000000021890000c05000000000000000000000000000000000000000000000000000000000d60b0000000000000124000000000000000000000000000000000000000060ac00000000c5fd000000000000d0b9000000000000f1600000c979000000000000958a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038a9000000000000000000000000f527000000000000000000000000000000000000c930000000000000000000000000000055c40000000000000000000000000000000000000000a0830000000000000000053a70c00000000000000000000000000000000000000000000024d900000000000089e100000000000031da856b000000000000c46e0000000000000000000000000000000075540000000074f20000556e0000000000000000000000000000000000000000000000000000996f0000000065160000000000000000000000000000000000000000000000000000fa0f0000000000000000c0d70000000000000000000000000000000070a40000b5b900000000000000000000000000000000000000001a110000000000000000000000000000063a0000000000000000000000000000000000000000000000000000442d00000000000000000000c1c800000000000081780000a182000045320000c8b5000000000000000000000000000000006064000000000000000000000000a91afa08000000000000000000000000000000000000309b14b254dfd1d10000000032130000c61a0000000085bf000000000000000000000000000000000000000075ff000000000000000000000000c19e62010000000000000000000000000000000000000000919600000000d5eb000000000000d1e5000000001513000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000802445790000000000000000000000000000000000009991723200000000000000000000000000002159000000000000000000000000203700000000000000000149000010cc000091f8000000000000))) else (if j<9 then (if j<7 then 0xf1ee000000000000000000000000d13401b61d2d0000000000000000000000000000606a00000000000000000000000000000000000000000000d21100006199000000000000191b000000000000000000000000000000000000ca0e00000000000000000000518d00000000000000000000e60d0000000025170000a5c60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000850000000000000000000000002014000000000000000000000000421e000000000000000000000000000000000000514d00000000000000000000f5a7a8ab00000000000000000000000000000000000000000000000000000000000000000000c978000000000000000000000000000000000000000000000000a1b0000000000000000000000000b45000000000000000000000000000ce000000000000000000000000000000000000000000000000000000000000000000000000e49900000000000000000000000000000000b163000022100000000000000000000000000000000000000000000000000000000000000000160800000000200b000000000000000000000000000000000000000000000000000000000000000000006588000000000000485600000000d1c100000000000000000000000090e20000000000000000000000000000000000000000000000000000000000000000000000000000b6290000648700000000000000000000000000000000000000000000252f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0c900006102000028bfe85200000000000061dd0000000000000000000000000000817d000000000000e53d0000000000009618b0dd000000000000c1d700000000000000000000000055e900000000996760250000d00c860700000000000041e200000000000000000000000000000000000000000000000000005920e1fa81d200000000000000000000000000000000a1e400000000000000000000000000000000491500000000000000000000407a0000000000000993000000000000e97e000069350000662f000000000000d0a100000000000000000000f52a0000a04f000000000000509e00006995000000000000e6090000000000000000000000000000685700000000000061c20000a1fb000000000000000000000000000000000000000000000000d96e0000a0630000000000000000919c000000000000b12fa63500000000b106000000000100605a000000000000000000000000000000000000000065d60000000000000000000000000000000000000000000000000000d4af0000000000000000 else (if j<8 then 0xb19800000000000075ea00000000000000000000000000000000000000000000000000000000000000000000000071fe000000000000000000000000000000000000540c000000000000000000000000000000000000609500000000000000000000000000000000000000000000000001c50000b0220000000000000000000000000000000000000000c0410000000000000000c1bd0000f20400000000000000000000660e21a4000048900000000000000000a13e00000000000000000000000091f400000000000000000000000000000000000000000000f11e0000000000000000000000000000297a000000000000000000000000000000000000c6378190d19f000000000000000000000000000000000000196685bb0000000000000000000000000000e06d000000000000000000000000000060fb000000000000000000000000000000000000000000000000000000000000000000000000000000000000d04800003096000000000000000095620000104d00000000000000000000a0680000000000000000000000000000000000000000b4300000000000000000000000000000000000000000000000000000000000000000000000000000057ff5300000000000000000000000000000000000000000000000000000000000000000f092000000000000000000000000000000000000000000000000000000000000000000000000000000000000046700000000000000000000000066060000000000000000000000000000000000000000d486000000000000000000000000a058000000000000000000005869000000000000000000000000000000000000000000000000f22e91400000000000000000000000000000a01d00000000000000000000000000000000000000000000fd2c00000000000000000000000000000000000000000000000000000000755671dc000046110000da0c70273214000010b2000000000000000000000000c21a0000000081bf00000000000000000000000000000000000000006899000000000000000000000000000000000000000000000000000000000000213c00000000c1aa0000000010eb0000002cd432f50b31e7847c000000009411000000000000000000000000000081300000000000000000ba2600000000000000000000000000000000000000000000000000000000000000000000000080ba6936000000000000000000000000000000000000000000000000000000000000e00900000000699b6a05a90ee55e9173000050d300000000000000000000f121000000000000000000000000f200000000000000000000000000319285c9e0c60000f1767066603b00000000000000000000000000000000000000000000 else 0x50f8c09c000000000000000000000000000000000000f20f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e1280000000000000000909a000000000000000000005174000000000000000014f700000000090c0000000000000000000000000000118a0000e0490000000000000000000081540000000000000000000000000000589da11a000000000000000000000000000000000000711600000000f12e0000000000000000000000000000801e00000000000081a5f59b0000500f0000000000000000205e0000000000000000000000000000000000000000f07300000000000000000000f5d2000000000000813a0000000000000000123a00000000000000000000000000000000000000000000000000000000a9f90000d1e10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080350000000000000000509700000000d5260000000000000000000000000000000000000000000000000000000000000000000035f20000186f000000000000000000000000000081ffc1b700000000f49bb22900000000000000000000000000000000000061ca000000000000000000000000000000000000000000000000000000000000000000000000000000007905000000000000602e00006983000000000000c4d10000000000000000000000000000000000000000000000000000756600000000000000000000000000000000261f000000000000000000000000000000000000000000000000c18f51e900000000000000000000000000004061000000000000000000000000000000000000000000000000000081d000000000000000000000d5cc000000000000863c00000000000074f100000000000000000000000000000000000000000000000000000000d49800000000000011230000000000000000b22361b10000307f00000000e52900000000e1ad00004a03000000000000000071180000000000000000760c0000000000000000000000000000000035ce0000589400000000000000000000000000000000000020e50000000000000000000000000000695f0000000000000000000000000000000074ae000014f3000090efa235000000000000d62b000000000000487000000000000000000000000000000000000000000000618e781a000000000000000000000000000000000000000000000000000000000000000000000000000021650000000000000000000000000000815a000000000000e9e000000000548801570000000008ae000000009180000000000000)) else (if j<11 then (if j<10 then 0x55000000000000000000000000d91c00003433a536807500000000000000000000c0520000240f00000000000000000000000094ac0000503c000051ae0000f14800000000000081d60000e934000000000000000000000000000000001012000000000000000000000000000000000000e1f60000e98900000000000000000000000000000000000000000000000000005120000000000000000000000000000000005181c56700000000000000000000000000000000000000000000000000000000000098b981bb0000000000000000000000000000000011430000000000000000c22a0000000000009142000000000000000000000000000080600000000000000000000000000000000015a80000000050f00000a2184057e18800000000692200000000000000000000000000004a1900000000000000000000920700000000000000000000412b00000000000000000000000000000000000000000000000000000000000000000000000000000000b1d9000000000000000000000000f98700000000c220062d00000000b0a2000000000000000000000000000000000000000000000000000000000000000071cb0000000050ad000070bf000021390000000000000000000000000000000000000000162700000000000000000000000000000000000000000000000038710000000000000000000000000000f007d8e80000000000000000000021690000b07938a400000000000000000000000000000000000000000000000000000000000000005564000000000000000000000000000000000000000000000000803f00000000000000000583000000000000a5c3c21b908f00000000c50081ec00000000000000000000000019f1b5a00000000000000000000000000000000000000000492a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c1770000000000003461000000006a3100000000000000000000782700000000899e00000000000000000000000000000000000000000000000000000000000000000000b13f00000000000000000000000000000000d82f0000000000000000000000000000000000000000000018eb0000000000000000000000000000000000000000000000006019000000000000e0db0000000000000000000000000000000080c1f1c700000000000000006a39000019ab6222000000000000000000000000000000000000819d00000000c4b000000000000000000000000040040000000000000000e1c000000000000000000000000000000000000000000000000000000000000000000000897c0000 else 0x34854845000000000000000000000000884b000000000000000000000000000000000000089e000000000000506900002144000000000000186b0000198d000000000000000000000000000000000000000010f70000b1de00000000000000000000000000000000000051fc0000000000000000117f000000000000000000000000000000000000000000000000000000000000000034ce602b0000000000000000a0e00000714e00000000000052340000000000000000000000000000d5c80000000000000000000060f400007206000068d80000000000000000000000000000118c000000000000000000000000755911620000000000000000000000000000000000000000000000000000d970519a09a900000000000000000000000000000000196a000000000000000000000000906c000000000000000000000000000000000000000000000000000000000000000000000000000000000000e6260000c112000040767a1d000000000000000000000000000040c4000000000000000000000000810e0000f40210340000746000000000000000000000000000000000000021ba41460000000000000000000000003457000000000000000098c3000000000000000000000000000000000000000000000000000000000000000000008042000000000000000034fe0000000000000000a96000008028410c000000000000000000000000000000000000000000000000000040a8703a0000111b0000000000002202000051eb00000000000000000000000000000000000000000000000000000000000000000000000020ec0000000000000000000000000000e0400000590d000000000000000000000000000090c800000000b05f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c091000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030bc000000000000000000000000000000000000000000000000000000000000000020c200000000000000000000000025193045000000000000704b0000000070fac185000000000000000000000000000000000000f558000000000000000000009537000000000000000000000000a043000000000000715000000000000000000000e233186e000000000000000000000000000000000000118600000000605d0000000030a300000000000091840000000000000000000000000000000000000000205600000000000000000000000000000000000000000000e89b0000000000000000b0d500000000000000000000000000000000000000000000000000000000) else (if j<12 then 0x40d0000000000000817200000000f84e0000251ec06500000000000035be000000000000f9ef00000000000000000000000000000000000000000000000000000000912741f2000071d300000000000000000000497300000000f1c40000146de1e87197000000000000e1a10000000000000000000000000000000000000000000000000000a976000000000000000000000000000000000000216b71b2a16c00000000e59c00000000000000000000000000000000d46800000000000049900000d23b999f00000000000000000000000000000000000000000000242e0000321fb0f6000031cd0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000055550000923c0000b11df8f20000761200000000000000000000000000000000501a39f4000000000000000000000000000001d82000000000000000000000000000000000000000fa1e00000000892cb161000000000000000000000000000000000000000000000000000000000000000000000000000018a10000000000000000000050e350e100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000901500000000000000000000000000000000000009a20000d5a200000000000004bc000000000000696300000000000050180000322c000000000000000000000000000000000000000065e749a7000000000000000000000000000000000000000000000000000000000000d8b200000000000091530000b11f0000000000000000192979260000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004168000004a39070000000000000000041030000000000000000000000008145a92d000000000000000000000000659214c60000000000000000a4660000000000000000000000000000000000000000000000000000000000000000000031e00000652200000000397d000035b600000000000000000000a80981e600000000000095af00000000000000000000000000000000000000000000721500007d3200000000000000000000e9a6f20a00000000f99240b4e1040000000000000000000000000000208d0000000000000000000000000000000000000000e23600009443110b00000000a0b7000000000000000000ff0000000000000000f58200000000000000000000000000000000 else 0x106f00000000000000000000000000003551000000007a1a000000000000000000000000000050720000000000000000000000000000000000000000000000000000720b0000799800000000000000000000000000000000000000000000000000000000000061fd00000000))))
def mo511D13 (j : Nat) : Nat := 0x291121468630c0c0848b861c0112220b84003431e444841a18b1a1c8891810a461c8882c3021e20c85184c31840485184c30e3840f0a30c16189841860b188448632309043c88918108202028c0c5101010d061861012302129996e247d1cb72d945912d410d42747b1ec5208800ffd87ffc87ffd82ffd72ffd81ffd71ffd21ffd80ffd70ffd40ffd20ffd10f7d85f7d75fdd73fdd32fdd31
def mo511H13 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x1413f14c000000000082b0000000000000000000000000000306100000000000000000000000000001492667000181a000000000000000002810807b85d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021260000000000000000000009c8800000000000002e8f000000000000000000d3a0000000000000000000009a50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0d800000000000000000000000000000000000c06000000000000000000000000000052740000000000000000000000000000000000000000000006620000000000000000000000000000185b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003033000028c0e0c0000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000309c0000000000000000000000000000000340000000000000000000188f000000000000000000000000000000000000000000000000000000005a2800000000000000000000000000000000000000000000000000000000c71d1a4000000221400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008c00000000000000210d665043f5e0400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002c9500020480000000000000000000000002c8c00000000000000a1c00000001d7700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000301263f0000000000285200000000228000484c000000297bb0800000000000000000000000000001ca600000005c7000000000000000000000000000000000000000000000000000000000000000141b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b0c000000000000000000000000000000000000000000000000000000000000000000000004ab0000000000000000000000000000000000000000000000000000000098980000000000000000000000000000000000041001000000201000000051010001010040001028 else 0xe70270000000000000000000000000000c47c0000000000000000060840000000000000000000020a0000000079ec0000000000000000000000000002c630a40000000000015040000000000c89184f0000000000000000000000003c0eb5f400000000000000000000000000000000000000000194b00000000000000000000000000000000000000000000030110000000000000000000000000000000007e0000000000000000038020000000000000000000000002e3900000000000000d1080000000000000000000000005484000000000000000000000000d0aa1870000000000000000000000003847000000000000000000000000000000000000001064000000000000000000000000000059f40000000000000000000000000001c31000000000000000000000000000000000000003087000000000000000000000000000000000000000000000000000000000003e82c0bc0000000000000000040140000000000000000000000000000000000000000000000000000000000000000008260000000000000000000000000000000000000000000000000000000000000000000641182b00000000000000000000000000000000000000000000000000000000000000081a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000417ea60000000000000000000000000000000000000000000000000000000000000000000000100c00000004114000c5d800000008430000000864c584000343b000000000000000000000000000000000000001d9b0001854b16800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004878000c24da8b000000000000000000000000000000000000000000000000012200000000163000000000000000000000e0b4c2400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000682c000000163b00000000000000000000060f49ae000347900000000000000000085979fac1d0000000000000000000000000000000000000000000000000000000000000000003849a05800000000004a4c000000000000000550000000000000034a4000000000000000000000000000000000030770000000000000000000000000000000000095900000002f80000000000000000000000000000000000001640000000000000000000000000000000048d800000000000000000000000000000007094000e8f70760000000000000000000000000000000048b0002c82000000000000000000000000000000000000000000000000000000000000000000000000000000000000000049400000000000000000000) else (if j<3 then 0x358300000000000000000000031e0000000000000000000002403d5f000092448150000000000000000030a90000000852800032040000000000000204100000000000000000000000000000000000b18800000000000000000000000000000000000000000104000000000001a3811f0000000000000000000002846000000000000000000000c128000f0dc0000000000858319a00034090000000000000000000004e0800000000000000c01000000000000000000000000000000018260000000d848e1a000000000000000000000e5680001a478890000000000000000000000000000c1800000000000000098100000000002c7a72780000000000000000000000000000000000000000000003070000000000012880000000000000000000000000002149000000000000000001c3e00000000000000000000000000000000000000000032b40000000000000000000000000000000000000000000000000000000358e000000000000000000000000000000000000000000000000000000000000000987d55900000000000000000000000000000000000000000000000000000000a5940000000000000000000000000000d550000000f19cc86b0d000000000000000000000091c0000000000000081d00000000000000187d000000000000000003e3e000000000000000000000000044b0000000d08c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e2580008210000000000000020a7000000000000000000000000343c000000000000000000000288700b00000000000000000000000000000000000000281400000002570000b89c00000000000000000000000000000000000000000211300000000001075000000000000000000000000000016a400030a0000a9c8000000000000000000000000000000000000000000000000000061700000000000000000000000000000000000000000000000002a736a5800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000032480a30000000000000000000000000000000000000000000000000b578000001c00000000000000000000000000000001854000000341f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000034500000002090f17800000019a2115c0000000000000027c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000002e92b51000000000000000000000000000000000003231000000000000000000000000000000000000000000000000030 else (if j<4 then 0x3c1800000000000000000000098c800000000000000000000000000000000000000529000000000000000000000000031fc00000000000003c296028000000000000000000000000e1354660000000000000000000000000000a4180008a3400000000000000000000000000000000000000e664c505860000000000000000000000000a0e0000000000000000000000000000000000000000000000000000000000000000e2200000000000000000000000000000000000000000000000000000000000089900016a0e51c00000000000000a3500000000000000000000000000000000000000000091380000000000000000000000000003b1f0000000000144c0000000000000000000000000000000281900000000000000000000000029a30000000000000000000000000000000000000000000000000000000000000000000000f63400040c8000000000092000000000000000006c000000000000000000000000000000000000000000000000000000000000000000000000011690000000000315f0000408f0e80000000000000000000000003234000aa0c0000000000000000000018510000000e04800000000000000000000000000000000001f2100000000000000000368e00000000000000017c00000000000000000000000000000000000000000189b0000000000000000000000000000000000000000000000000000000091b6180a1cf43500000000000000000000000000000000072000000000000000000000000000000000000001c9a0000000000000000000000001e3a00000000000000000000000000000000000000000094820aa00000000001c220000000000000000000000000000000000000000000000da8000000081ac0000000000fa0400000000000000000000000000000000000000862800000000000000000000000000000000000000000000000000000000000000000000000000000000000000041600000001ca8000000000000000000000953e48500000000000000000000000000000000000000000000000000000000000000000000000000000000208e00000000000000000000000000000000000000000064880000000000000000000000000000000000000000000000003c6a00000000000000000000011bd4650000000000107b103f89f0000a7f0000000e20fe1c0000000000000000000008684000d15800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000029310000000000000000030a10000000000000000b80000000000000000000000000003197000000000008440000000000000000000000000000000000070b1d05000000000000000000000000206e00000 else 0x116282bb8a500000000000000703400000000000000000000000000000003ab0000000000000000000001680000000000000000000000346c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000325c00000000000000000000000000000000000000000000000000000000000000000000000000)))
def mo511D14 (j : Nat) : Nat := 0x40810c18bff
def mo511H14 (j : Nat) : Nat := 0x65a00342e0fa1c000004c500082400000a05c1c0068124d12000000000b980020000000000000000000000000000000000000000344000520000c640a98c0000000000042c0000015c4aa86d83f0c001d0f84992001fd4
def mo511L : Nat → Packing
  | 7 => (3,7,6,0,0,0,0,mo511D7)
  | 8 => (40,6,6,0,0,8,0,mo511D8)
  | 9 => (228,5,6,0,0,12,0,mo511D9)
  | 10 => (588,4,6,0,0,14,0,mo511D10)
  | 11 => (574,3,6,0,0,15,0,mo511D11)
  | 12 => (175,2,6,0,0,14,0,mo511D12)
  | 13 => (17,1,6,0,0,10,0,mo511D13)
  | 14 => (1,0,6,0,0,0,0,mo511D14)
  | _ => emptyPacking
def mo511I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 55 0 8 2 2 mo511H8
  | 9 => lookupWord 13 275 2 12 6 2 mo511H9
  | 10 => lookupWord 80 811 5 14 8 2 mo511H10
  | 11 => lookupWord 211 6349 3 16 10 2 mo511H11
  | 12 => lookupWord 204 6151 4 16 10 2 mo511H12
  | 13 => lookupWord 60 2415 3 14 8 2 mo511H13
  | 14 => lookupWord 5 61 5 11 5 2 mo511H14
  | _ => fun _ => none
def mo511 : Forest := ⟨1535,14,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P7_0 : CutRow mo511 7 0 3 := mixedCut (pos:=0x6028108824092082409104411) (neg:=0x98485d0ac3c1a4b44b1e0b43c0f) (data:=fun _ => 0x53a5802040590531825b0932) rfl (by decide +kernel)
theorem mo511B7 : CutRow mo511 7 0 3 := mo511P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_0 : CutRow mo511 8 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_7 : CutRow mo511 8 7 33 := mixedCut (pos:=0x6028108824092082409104411) (neg:=0x98485d0ac3c1a4b44b1e0b43c0f) (data:=fun _ => 0x53ab802053ab8010a0b9a53153a580304059054253a580204059054153ab802053a58020825b09539789a2413149246131492481a29b89439785a241825b0943825b0943825b094353ab803031492471314924703149244131492481a29b8943825b095453ab80303149247053ab80303149244051492470514924705149247015942487) rfl (by decide +kernel)
theorem mo511B8 : CutRow mo511 8 0 40 := (@joinRow mo511 8 0 7 33 mo511P8_0 mo511P8_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_0 : CutRow mo511 9 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_7 : CutRow mo511 9 7 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_55 : CutRow mo511 9 55 43 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_98 : CutRow mo511 9 98 96 := mixedCut (pos:=0x6028108824092082409104411) (neg:=0x98485d0ac3c1a4b44b1e0b43c0f) (data:=fun _ => 0x3149247131492491a29b897553ab803053ab8020825b096440b90552a0b9a552825b0964a0b9a553a0b9a5429789a24140b9056340b90552a059057340b90552a0b9a542a0590582049b058540b90552a0590582a0b9a5639789a241a29b8954a29b8953829b0975a29b89543149243131492481a25b09859785a251825b0954825b0954a25b098453ab8040314924813149248031492451314924913149245131492491a29b89753149245131492481314924413149249153ab8020825b09941394247431492497825b09539789a241a29b8954a29b8953829b0975a29b895453ab80209785a262825b0965825b0965a25b0985a25b098453ab80403149248053ab80403149245053ab803031492450a29b897553ab803053ab8020825b096453ab8020825b09945149248031492430825b0943514924809785a2415149248051482480514824801584249831492450314924401394249453ab803053ab8030a0b9a552a0b9a583a0b9a5524059055240590552405905824059054140590591) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_194 : CutRow mo511 9 194 34 := mixedCut (pos:=0x6028108824092082409104411) (neg:=0x98485d0ac3c1a4b44b1e0b43c0f) (data:=fun _ => 0x53ab803053ab802053ab802053ab803053ab803053ab802053ab803053ab802053ab80309785a252825b0964825b09649789a25253a580404059055353a580304059055253ab803053ab803053ab802053ab802053ab802053ab80109789a2519785a251a059058253a5803053a5803053a5802053a5803053a5802053a5802053a580209789a241) rfl (by decide +kernel)
theorem mo511B9 : CutRow mo511 9 0 228 := (@joinRow mo511 9 0 55 173 (@joinRow mo511 9 0 7 48 mo511P9_0 mo511P9_7) (@joinRow mo511 9 55 43 130 mo511P9_55 (@joinRow mo511 9 98 96 34 mo511P9_98 mo511P9_194)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_0 : CutRow mo511 10 0 20 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_20 : CutRow mo511 10 20 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_68 : CutRow mo511 10 68 16 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_84 : CutRow mo511 10 84 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_132 : CutRow mo511 10 132 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_180 : CutRow mo511 10 180 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_228 : CutRow mo511 10 228 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_276 : CutRow mo511 10 276 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_324 : CutRow mo511 10 324 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_372 : CutRow mo511 10 372 6 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_378 : CutRow mo511 10 378 7 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_385 : CutRow mo511 10 385 96 := mixedCut (pos:=0x6028108824092082409104411) (neg:=0x98485d0ac3c1a4b44b1e0b43c0f) (data:=fun _ => 0x9789a25253ab803053ab8030825b0975825b09a5825b0964825b09659785a251825b0964a649a461a29b89659789a251825b096431492451314924a19789a2419789a241829b09869785a252314924619785a2623149249131482451314824a1a29b897531482451314824a153ab8030825b09a513842495314824a9825b0964824b09649789a2529789a25253ab8040829b0986a29b8965a29b8964a29b89649785a262a25b09969789a252825b0975825b0975825b097553ab8030825b09a5a659a461a29b89659789a251825b096453ab80309789a2419789a241829b098653ab804053ab804053ab8030a29b897553ab8030825b097553ab8030825b09a531492450825b0964314924509785a251314924603148245031482450138424a553ab804053ab804053ab804053ab804053ab804053ab804053ab804053ab8040a0b9a5749789a262a0b9a574a0b9a584a0b9a563a0b9a5529789a2514059056340590563405905a3405905529789a251405905a3405905524059055240590552) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_481 : CutRow mo511 10 481 96 := mixedCut (pos:=0x6028108824092082409104411) (neg:=0x98485d0ac3c1a4b44b1e0b43c0f) (data:=fun _ => 0x53ab803053ab803053ab803053ab802053ab802053ab803053ab804053ab80309789a2629785a2629785a262825b097540b90563a0b9a563825b097553ab804053ab804053ab803053ab803053ab803053ab803053ab803053ab803053ab802053ab802053ab803053ab803053ab802053ab802053ab802053ab802053ab803053ab803053ab803053ab803053ab802053ab80209789a2519785a2514059055253a5803053a5804053a5804053a5804053a5803053a5803053a5803053a5803053a5802053a5803053a5803053a5802053ab802053ab80209789a2419789a2419789a241829b098653ab804053ab803053ab8030825b097540b90563a0b9a563825b09759789a2529789a25240b90574a0b9a56440b90574a0190594a0b9a553a0b9a56340b90563a0b9a563824b09a5a05905949789a262a659a461405905a3405905529789a251405905529789a2419789a241a0b9a5749789a2529789a2523149245131492491829b0986a29b8965a29b8964a29b896453ab8040a25b0996) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_577 : CutRow mo511 10 577 11 := mixedCut (pos:=0x6028108824092082409104411) (neg:=0x98485d0ac3c1a4b44b1e0b43c0f) (data:=fun _ => 0x53ab804053ab803053ab803053ab803035ba808353ab803053ab803053ab803053ab804053ab804053ab8030) rfl (by decide +kernel)
theorem mo511B10 : CutRow mo511 10 0 588 := (@joinRow mo511 10 0 276 312 (@joinRow mo511 10 0 84 192 (@joinRow mo511 10 0 20 64 mo511P10_0 (@joinRow mo511 10 20 48 16 mo511P10_20 mo511P10_68)) (@joinRow mo511 10 84 96 96 (@joinRow mo511 10 84 48 48 mo511P10_84 mo511P10_132) (@joinRow mo511 10 180 48 48 mo511P10_180 mo511P10_228))) (@joinRow mo511 10 276 102 210 (@joinRow mo511 10 276 48 54 mo511P10_276 (@joinRow mo511 10 324 48 6 mo511P10_324 mo511P10_372)) (@joinRow mo511 10 378 103 107 (@joinRow mo511 10 378 7 96 mo511P10_378 mo511P10_385) (@joinRow mo511 10 481 96 11 mo511P10_481 mo511P10_577))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_0 : CutRow mo511 11 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_2 : CutRow mo511 11 2 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_50 : CutRow mo511 11 50 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_98 : CutRow mo511 11 98 3 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_101 : CutRow mo511 11 101 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_149 : CutRow mo511 11 149 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_197 : CutRow mo511 11 197 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_245 : CutRow mo511 11 245 34 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_279 : CutRow mo511 11 279 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_327 : CutRow mo511 11 327 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_375 : CutRow mo511 11 375 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_423 : CutRow mo511 11 423 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_471 : CutRow mo511 11 471 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_519 : CutRow mo511 11 519 1 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_520 : CutRow mo511 11 520 7 := by
  apply checkedRow
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_527 : CutRow mo511 11 527 47 := mixedCut (pos:=0x6028108824092082409104411) (neg:=0x98485d0ac3c1a4b44b1e0b43c0f) (data:=fun _ => 0x53ab804053ab804053ab804053ab804053ab804053ab804053ab804053ab804053ab804053ab804053ab80409789a2629789a2629789a26253ab804053ab804053ab804053ab804053ab804053ab804053ab804053ab804053a5804053ab80409789a2629789a2629789a2629789a2629789a262405905749789a2629789a2629789a2629789a2629785a262825b0986a29b89869789a2629789a2629789a2629789a2629785a262825b0986a29b898653a380409789a262a0b9a574) rfl (by decide +kernel)
theorem mo511B11 : CutRow mo511 11 0 574 := (@joinRow mo511 11 0 279 295 (@joinRow mo511 11 0 101 178 (@joinRow mo511 11 0 50 51 (@joinRow mo511 11 0 2 48 mo511P11_0 mo511P11_2) (@joinRow mo511 11 50 48 3 mo511P11_50 mo511P11_98)) (@joinRow mo511 11 101 96 82 (@joinRow mo511 11 101 48 48 mo511P11_101 mo511P11_149) (@joinRow mo511 11 197 48 34 mo511P11_197 mo511P11_245))) (@joinRow mo511 11 279 192 103 (@joinRow mo511 11 279 96 96 (@joinRow mo511 11 279 48 48 mo511P11_279 mo511P11_327) (@joinRow mo511 11 375 48 48 mo511P11_375 mo511P11_423)) (@joinRow mo511 11 471 49 54 (@joinRow mo511 11 471 48 1 mo511P11_471 mo511P11_519) (@joinRow mo511 11 520 7 47 mo511P11_520 mo511P11_527))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_0 : CutRow mo511 12 0 15 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_15 : CutRow mo511 12 15 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_63 : CutRow mo511 12 63 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_111 : CutRow mo511 12 111 12 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_123 : CutRow mo511 12 123 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_171 : CutRow mo511 12 171 4 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B12 : CutRow mo511 12 0 175 := (@joinRow mo511 12 0 111 64 (@joinRow mo511 12 0 15 96 mo511P12_0 (@joinRow mo511 12 15 48 48 mo511P12_15 mo511P12_63)) (@joinRow mo511 12 111 12 52 mo511P12_111 (@joinRow mo511 12 123 48 4 mo511P12_123 mo511P12_171)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_0 : CutRow mo511 13 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_5 : CutRow mo511 13 5 12 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B13 : CutRow mo511 13 0 17 := (@joinRow mo511 13 0 5 12 mo511P13_0 mo511P13_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P14_0 : CutRow mo511 14 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B14 : CutRow mo511 14 0 1 := mo511P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511T : mixedTables mo511 14 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo511 0 0)
  · exact (mixedEmpty mo511 1 0)
  · exact (mixedEmpty mo511 2 0)
  · exact (mixedEmpty mo511 3 0)
  · exact (mixedEmpty mo511 4 0)
  · exact (mixedEmpty mo511 5 0)
  · exact (mixedEmpty mo511 6 0)
  · exact mo511B7
  · exact mo511B8
  · exact mo511B9
  · exact mo511B10
  · exact mo511B11
  · exact mo511B12
  · exact mo511B13
  · exact mo511B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511G : graphValid mo511 (boundsBefore K471) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511R : Impossible false graph 14 nineInputs.toFinset := by
  rw [show graph = targetOf mo511 by decide +kernel]
  exact mixedRoot (g:=mo511) (top:=14) (i:=0) (before_sound K471 (known_down V471)) mo511G mo511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_10976

theorem PEqualNP.Outside.L_meta_10976 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8) || (x 7 && x 8)) t → 15 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact PEqualNP.Outside.L_meta_10976.directSplit PEqualNP.Outside.L_meta_10976.mo511R PEqualNP.Outside.L_meta_10976.g511R ⟨C,hf,by omega,heq⟩
