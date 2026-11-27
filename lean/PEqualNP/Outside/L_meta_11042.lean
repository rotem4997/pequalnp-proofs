import PEqualNP.Defs

-- The two-mode live-state and cofactor checker is adapted from PEqualNP/Outside/L_meta_8459.lean (Apache-2.0),
-- which follows L_meta_1674, L_meta_670 and L_meta_1667 (Apache-2.0).
-- The graph, restrictions and all search certificates below are for this row.

namespace PEqualNP.Outside.L_meta_11042
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
def graph : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffcfffffffefffffffaffffffeeffffffaafefefcfcfafaf0f0eeeeccccaaaa0000
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8) || (x 7 && x 8)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8) ||| (x 6 &&& x 8) ||| (x 7 &&& x 8)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8) ||| (x 6 &&& x 8) ||| (x 7 &&& x 8)
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
def nineEdge (x : Fin 9 → Bool) := (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8) || (x 7 && x 8)

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
def neighborRow (i : Fin 9) : Nat := [4,5,6,7,0,1,2,0,1].getD i.val 0
def absentRowRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighborRow i)
def presentRowRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighborRow i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRowRow i) graph ≠ bit (presentRowRow i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRowRow i) (nineInputs.getD j.val zero) =
      bit (presentRowRow i) (nineInputs.getD j.val zero)) := by decide +kernel

theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = nineEdge) (small : C.size ≤ 15) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 14 else 15) ∧ Live u graph k nineInputs.toFinset := by
  have goalEq : (execute C.gates nineInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (nineEval C legal C.output r).trans ((congrFun computes (sampleNine r)).trans (nineTable r).symm)
  have len : C.gates.length ≤ 15 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 14 else 15) := by
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
    (m : ∀ k, k ≤ 15 → ¬Live false graph k nineInputs.toFinset)
    (s : ∀ k, k ≤ 14 → ¬Live true graph k nineInputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 nineEdge 15 := by
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
def K145 := extendKnown [] 4 [(145,[]),(290,[135,84,16]),(324,[135,100,32]),(392,[116,132,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V145 : Known true K145 := extend_ok (m:=145) baseKnown low145 (by decide +kernel)
def g387Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffd3663,0xfffffffffffffffffffffffffffffffffdbea1),(0x23ccc,0x254e4),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffc773,0x24052),(0x3f99c,0x1ab08)]
def g387C : List ColumnInfo := []
def g387A : List (List Nat) := [[]]
def g387D3 (j : Nat) : Nat := 0xf
def g387L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g387D3)
  | _ => emptyPacking
def g387I (_ _ : Nat) : Option (Nat × Nat) := none
def g387 : Forest := ⟨387,3,fun i => g387Y[i]?.getD (0,0),g387C,g387A,g387L,g387I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g387P3_0 : block g387 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g387B3 : block g387 3 0 1=true := g387P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g387T : checkedTables g387 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g387 0 0 0 = true)
  · exact (rfl : block g387 1 0 0 = true)
  · exact (rfl : block g387 2 0 0 = true)
  · exact g387B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g387G : graphValid g387 (boundsBefore K145) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low387 : Lower true (varsX 387) (graphGoal 387) 4 := lower_forest (g:=g387) (i:=0) (hints:=4294967431) (before_sound K145 V145) g387G g387T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K387 := extendKnown K145 4 [(387,[]),(402,[135,16,64]),(417,[81]),(432,[81,64]),(449,[97])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V387 : Known true K387 := extend_ok (m:=387) V145 low387 (by decide +kernel)
def g358Y : Array (Bits × Bits) := #[(0x0,0x0),(0x24987acb91e,0x18a9e380e),(0xfffffffffffffffffffffffffffc0e78152e95,0xfffffffffffffffffffffffffff00698c52a11),(0x0,0x0),(0x0,0x0),(0x87007e1f652,0xf745561c610),(0xffffffffffffffffffffffffffff80783bdc25,0xfe1663ad404),(0x0,0x0),(0xfff806e43e8,0x8000001e0)]
def g358C : List ColumnInfo := [(34,0,324,0,4),(68,0,290,0,4)]
def g358A : List (List Nat) := [[],[98],[81],[33,101],[81,98],[97,33,82]]
def g358D4 (j : Nat) : Nat := 0x25f63547409bd89544426d6215110
def g358D5 (j : Nat) : Nat := 0x208048080dc812000c6302faa3a07bd4940bfa8a81fb40502fea8885f95110beaa2217c54443f280885bd4940
def g358H5 (j : Nat) : Nat := 0xc000000000000008000000000000000000005a00e17b00000
def g358D6 (j : Nat) : Nat := 0x102ff40fd40fd10
def g358H6 (j : Nat) : Nat := 0x8300000000000000000000000000000000000000000000000001000000000006500000000000000000d6200000000001624000000000000000050e00000000000e44000000000008080000000000000000000002850000000000000000000000904e5c0000000000000784000000000000000000000000000000000000000001830000228c80000004c00000
def g358D7 (j : Nat) : Nat := 0x105f
def g358H7 (j : Nat) : Nat := 0x293ce000000000000000000080000000e500000000000000cd0038401e2000000000000000000000002aa4000000000000000000003800000000000000000000000000000000000000000000000000000000000eb003d000
def g358L : Nat → Packing
  | 4 => (3,3,1,0,0,0,0,g358D4)
  | 5 => (10,2,1,0,0,5,0,g358D5)
  | 6 => (3,1,1,0,0,0,0,g358D6)
  | 7 => (1,0,1,0,0,0,0,g358D7)
  | _ => emptyPacking
def g358I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 22 0 9 2 3 g358H5
  | 6 => lookupWord 3 103 0 11 4 3 g358H6
  | 7 => lookupWord 2 79 0 9 2 3 g358H7
  | _ => fun _ => none
def g358 : Forest := ⟨358,7,fun i => g358Y[i]?.getD (0,0),g358C,g358A,g358L,g358I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P4_0 : block g358 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g358B4 : block g358 4 0 3=true := g358P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P5_0 : block g358 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P5_1 : block g358 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g358B5 : block g358 5 0 10=true := (@block_merge g358 5 0 1 9 g358P5_0 g358P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P6_0 : block g358 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g358B6 : block g358 6 0 3=true := g358P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P7_0 : block g358 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g358B7 : block g358 7 0 1=true := g358P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358T : checkedTables g358 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g358 0 0 0 = true)
  · exact (rfl : block g358 1 0 0 = true)
  · exact (rfl : block g358 2 0 0 = true)
  · exact (rfl : block g358 3 0 0 = true)
  · exact g358B4
  · exact g358B5
  · exact g358B6
  · exact g358B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358G : graphValid g358 (boundsBefore K387) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low358 : Lower true (varsX 358) (graphGoal 358) 8 := lower_forest (g:=g358) (i:=0) (hints:=4329571920) (before_sound K387 V387) g358G g358T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K358 := extendKnown K387 8 [(358,[]),(409,[134,118,84,50,16]),(426,[118,50]),(460,[101,117,33,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V358 : Known true K358 := extend_ok (m:=358) V387 low358 (by decide +kernel)
def g403Y : Array (Bits × Bits) := #[(0x403fcce9c,0x4432a4e0c),(0xffffffffffffffffffffffffffffe8c26127a3,0xffffffffffffffffffffffffffffe90a6143a1),(0x0,0x0),(0x0,0x0),(0x103c7da934,0x12ac55a110),(0x0,0x0),(0x0,0x0),(0x1f3f8651e8,0x9108000e0),(0xffffffffffffffffffffffffffffffc007be43,0x16e11ebc02)]
def g403C : List ColumnInfo := [(16,0,387,0,4),(256,2,145,0,4),(258,0,145,0,4),(1,0,402,0,4)]
def g403A : List (List Nat) := [[],[64]]
def g403D4 (j : Nat) : Nat := 0x5bd4930
def g403D5 (j : Nat) : Nat := 0x88401900ff30fd30fd20
def g403H5 (j : Nat) : Nat := 0xc000000000
def g403D6 (j : Nat) : Nat := 0x5889f
def g403H6 (j : Nat) : Nat := 0x8005500a80260000079
def g403L : Nat → Packing
  | 4 => (1,2,2,0,0,0,0,g403D4)
  | 5 => (3,1,2,0,0,4,0,g403D5)
  | 6 => (1,0,2,0,0,0,0,g403D6)
  | _ => emptyPacking
def g403I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 6 1 1 g403H5
  | 6 => lookupWord 1 12 0 7 2 1 g403H6
  | _ => fun _ => none
def g403 : Forest := ⟨403,6,fun i => g403Y[i]?.getD (0,0),g403C,g403A,g403L,g403I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403P4_0 : block g403 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g403B4 : block g403 4 0 1=true := g403P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403P5_0 : block g403 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g403B5 : block g403 5 0 3=true := g403P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403P6_0 : block g403 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g403B6 : block g403 6 0 1=true := g403P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403T : checkedTables g403 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g403 0 0 0 = true)
  · exact (rfl : block g403 1 0 0 = true)
  · exact (rfl : block g403 2 0 0 = true)
  · exact (rfl : block g403 3 0 0 = true)
  · exact g403B4
  · exact g403B5
  · exact g403B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403G : graphValid g403 (boundsBefore K358) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low403 : Lower true (varsX 403) (graphGoal 403) 7 := lower_forest (g:=g403) (i:=0) (hints:=4294967428) (before_sound K358 V358) g403G g403T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K403 := extendKnown K358 7 [(403,[]),(405,[33]),(419,[135,84,16]),(433,[81]),(434,[135,65,16,80]),(453,[135,100,32,16]),(465,[97]),(468,[135,65,97,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V403 : Known true K403 := extend_ok (m:=403) V358 low403 (by decide +kernel)
def g435Y : Array (Bits × Bits) := #[(0xe1ac8cbc4e8be,0x41002110acb04a0ae),(0xffffffffffffffffffffc07f01e11c38659075,0xffffffffffffffffffffc04f48a00910658031),(0x0,0x0),(0x0,0x0),(0x43f19cc0448e6352,0x2965918cc0048a4250),(0xffffffffffffffffffffcf8001e70c638b1f85,0x118001470463821f04),(0x0,0x0),(0x3003fe0663a5719f08,0x100a6c622120611d00),(0x3ffc0006733e3a64e8,0x2e308010d28c1860c8)]
def g435C : List ColumnInfo := [(144,1,290,0,4),(288,2,145,0,4),(16,0,419,0,7),(32,0,403,0,7),(145,0,290,0,4),(2,0,433,0,7),(258,32,145,0,4),(1,0,434,0,7),(129,16,290,0,4)]
def g435A : List (List Nat) := [[],[81],[64],[64,81],[16,84,135],[80,16,65,135]]
def g435D5 (j : Nat) : Nat := 0x333dcf6254540
def g435D6 (j : Nat) : Nat := 0x2983881d69a09faeda8e81bbd8b5150377b12a2a05df7354520
def g435H6 (j : Nat) : Nat := 0x0
def g435D7 (j : Nat) : Nat := 0x11080069c420020c080182005ae600663042c10a1185460c00ffd4740ffd4540ff54540ffd4520ff54520ff4c520bf59654bf59740be58054bb58b50bbd8940
def g435H7 (j : Nat) : Nat := 0x10000850000260000068e040000086e386
def g435D8 (j : Nat) : Nat := 0x608034182010e5188201841006430402183598051566400a10057742fad09c5e202001fe54feaa7f153fea1fd50ffa07f503fa41fd10
def g435H8 (j : Nat) : Nat := 0x10b000430000006040000000000000000000000a8fc2800352c0c00304417cb30640000000000080a0300000180242000000007a2000001248020000680018570e719c4800
def g435D9 (j : Nat) : Nat := 0x753213f
def g435H9 (j : Nat) : Nat := 0x2550000000000000000000000000003100040000000000000000000787000003a2800000000000000000000002200068c003c2000002018000000000000030000000000000000000000000000000000000000000000000000001820000000010a003040007a489124000000003c0e25e600000000082000381000c8800000386001b4c00343001150000000000000000000000000000
def g435L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g435D5)
  | 6 => (4,3,4,0,0,5,0,g435D6)
  | 7 => (11,2,4,0,0,7,0,g435D7)
  | 8 => (9,1,4,0,0,8,0,g435D8)
  | 9 => (1,0,4,0,0,0,0,g435D9)
  | _ => emptyPacking
def g435I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 8 0 8 1 3 g435H6
  | 7 => lookupWord 1 15 0 9 2 3 g435H7
  | 8 => lookupWord 4 53 0 11 4 3 g435H8
  | 9 => lookupWord 5 111 0 11 4 3 g435H9
  | _ => fun _ => none
def g435 : Forest := ⟨435,9,fun i => g435Y[i]?.getD (0,0),g435C,g435A,g435L,g435I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P5_0 : block g435 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g435B5 : block g435 5 0 1=true := g435P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P6_0 : block g435 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g435B6 : block g435 6 0 4=true := g435P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P7_0 : block g435 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P7_3 : block g435 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P7_5 : block g435 7 5 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g435B7 : block g435 7 0 11=true := (@block_merge g435 7 0 3 8 g435P7_0 (@block_merge g435 7 3 2 6 g435P7_3 g435P7_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P8_0 : block g435 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g435B8 : block g435 8 0 9=true := g435P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P9_0 : block g435 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g435B9 : block g435 9 0 1=true := g435P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435T : checkedTables g435 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g435 0 0 0 = true)
  · exact (rfl : block g435 1 0 0 = true)
  · exact (rfl : block g435 2 0 0 = true)
  · exact (rfl : block g435 3 0 0 = true)
  · exact (rfl : block g435 4 0 0 = true)
  · exact g435B5
  · exact g435B6
  · exact g435B7
  · exact g435B8
  · exact g435B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435G : graphValid g435 (boundsBefore K403) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low435 : Lower true (varsX 435) (graphGoal 435) 10 := lower_forest (g:=g435) (i:=0) (hints:=4296015956) (before_sound K403 V403) g435G g435T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K435 := extendKnown K403 10 [(435,[]),(469,[101,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V435 : Known true K435 := extend_ok (m:=435) V403 low435 (by decide +kernel)
def g443Y : Array (Bits × Bits) := #[(0x1804022038211e1f043ff9a2061cb5470ff0,0x5022830011207442452aab654854607e0),(0x5c3800c211e1ffe304b9550f1e40ed0e,0x8004420004218611ae300e5570a1e40a906),(0x0,0x0),(0x20186fc44f03e001f83c034297cc909de1a4,0x201c6664eb031155f8be060a17cc900de120),(0xffe06070078ffc01fe003ffd014908507be031,0x247279168fe481f8909bad0109085039e010),(0x307f8007f00001ffffc0063a0064e18dd06a,0x313c8005fa08419ee510061a0044e18d5028),(0x0,0x0),(0xffff800007fffffe00000008446fd8eca43a0f,0xffd980000100086c000200005440002a80180f),(0x3ffffff80000000000000f87b1238b3a17d0,0x643199a04b080000000c900a831003206d0)]
def g443C : List ColumnInfo := [(152,1,290,0,4),(296,2,145,0,4),(34,0,409,0,8),(17,0,426,0,8),(137,16,290,0,4),(266,32,145,0,4),(8,0,435,0,10),(51,0,392,0,4),(24,0,419,0,7),(40,0,403,0,7)]
def g443A : List (List Nat) := [[],[81],[64],[64,81],[16,84,135],[80,16,65,135]]
def g443D5 (j : Nat) : Nat := 0x30c7d2726c0b01b92cba256916121b7354550
def g443D6 (j : Nat) : Nat := 0x1f182070c190f3cf3cf3cf3cf3cf3cf3cf3cf3d53cf3cf3c0cd3e1793603725971cf93e0580dc965c73e4d816037259719f94e0d715c165c6be53825c57059746f646487559560d1b591921d56558256ea91d78259560a6be9191e0976d431af94e09815db50cad6516121971d428eda2219765c75087be8998a1f61d421efa265e8654750cad6516121951d428eda22197654750967e9191d97735421efa266376d8550a73e8985dcf615432b5945848654550a67e9186dcd515429cfa261b7354550a6769086dcd515429cda221b7354550e3558486dcd515423eba266361d4150
def g443H6 (j : Nat) : Nat := 0xb061000000
def g443D7 (j : Nat) : Nat := (if j<1 then 0x40004200078f482030c0021973864561915b8032194a02d28190c864160b6ab28402b61880402b100ac560b158ac56b80c864320b3d9ec562b158ac162b0c82c321905ac4162b0ca9816190582c3219058ac162b4d82c560b15864162b058ac162b4d82cf6940c864168205a241682411ec320b2f1ecf67b3d9ec160b3a194bc5326130982b158ac160b10080320b158ac40200c90432320c8ac4019058641c0b05801b6f9261f65997cdf0dc2ee4b2f9be1665dc965f37baccbb92cbb6f85e0372596edf2ac06e4b2edbe1580dc965be7c9b01b92cb5ed96e03725973df03c06e4b2e7be0580dc965cf6c0b01b92cbb5f65e0d705976decbc12e0b2ef3e0f725c165cefc1ee2b82cb9ef82dc5705973bf06b8ae0b2e7be09715c165cf7c970eb28cb9ef87e09651973df2fc12ca32f5be4b8759465eb7cbf04b28cbd6f87e09651973df30b2ae432f7ae49655c065ee7c92cab9ec157e981d5655838fec83aacab071f5907559560eb7baf04b2ac1d6c75e09655833d92fc12cab073b25f8259560f37caf04b2ac1e6f85e0965582d7f28c0acab05bbe498159560cf7c930bb8ac19ed9221d51583cdf24b2aa2b067be49879db509dfca3033b6a19ef9261676d433df2fc12eda867b9db825db50cf7caf04bb6a19ed95e0976d433df23c12eda867b647825db50cf7c1702bb6a15bf9460576d42bdf24c0aeda867be09815db50af7c930fb2ea19ef9261f65d42bdf24bb6cba84efe5181d9750cf7c3f04b2ea19ef97e0965d4277b28432e3a84fb648865c750d7ab090cb8ea18ff865d971d431f90cbb2e3a857be49765c7508fecc50fb0ea15ef9261f61d433df24c3ec3a847fe5d85d87509f7c930bb0ea11fd97a1951d4277b28432a3a84fb6488654750d7ab090ca8ea18ff865d951d431f90cbb2a3a857be4976547509dfca303b2aa15dd91d9773543abecab2ee6a8773e4965dcd50aefc8acbb9aa15df9361f61542bdf24c3ec2a847f66376d85508ffcc2edb0aa15df935db61542bdf24bb6c2a84fbe4985d8550ceec2ee7b0aa19df85dcd61543b3f09b9ac2a84efe5186545509f7c930ca8aa13bd94219515427db24432a2a86bd5848654550cefc36e6a8aa19de86dcd515433bb0db9aa2a867721b7354550eaeb2ee6a8aa17bb94585605437d724c36a0a84fe66361d4150bddca2c3a82a15ed92a1d654433dd0fc12ca8867b21f8259510cf74bf04b2a219ec97e09654426df24c3ecb32e9be1b85dc965ae7c9b01b92cb9cf83dc9705972df25c3aca32e5be1f82594658f7cc2cab90cb96f9859572196bd724b2ae032f3ae49655c065ae7c92cab9ec1ccf9259573d82adb243aacab047be4985dc5608f6c910ea8ac11ef9261e76d423df24c2ceda847be4987d97508f7c930fb0ea15cf925977354333f09b9ac2a84fae4986d4150 else 0xd604101b2000ac8142b60414042720416c82040008c8100040b481e3056410407000d481c3010b0c1000508140004301)
def g443H7 (j : Nat) : Nat := 0xa06000000000f14238000a97f08904000000d10000817000000b37000000601702713918000911d19f00f0f000315000000000316e07000000e0d000000580000000000000c0980c00000000069500040b50e00000000000070500000021200080a803000810750
def g443D8 (j : Nat) : Nat := (if j<1 then 0x54d8f100022a6098c08014284020040b8c08010205038c00b8c0010f1800b1d2000446dc8006db900c6226c61408014001ed8e90b8c2000d9000bb0401484a4002860026c1420002284000430214006140800db00e58c4e400202002000420000008157f362f7df7bd7a278776c74a0007215652027066e46a162f62f6a16d06b50140146a101462f62f6a168d66b65753d63c62f61460e5ec5d15bd5a25875875650ec54a53d5294d84ec50e4d84ec1364d84bd49b47945743c42140d0000000000af0000003f93e53c33a137f3563340283192f00002c709400000000029e27c00025a05e2312162020000001e005e0001c51a305e05e17a1511361221221001000ec0d80000000af00002809400009400000001400000001400000007900005e02802800003c014014000000028028014000000fef85dc965fee65dc965fef80dc965fed80dc965f7f65dc165fef72dc165dff71dc165f7f655c165fef725c165dff715c165dfd715c165dff8759465fef8259465fef8259760fef8259560eff8159560efd8159560bfd819db50dfe765db50fef825db50bff815db50dff815db50dfd815db50dfd87d9750dfd76d9750bfd81d9750dff8759750f7f6559750fef8259750bff8159750bff865c750bfc865c750dfd765c750dfe87d8750dfd87d8750bfd85d8750bff8654750bfe8654750bfc8654750dfd7654750f7d6554750bfd81d9550f7f6559550fef8259550bff8159550dfe87d8550dfd87d8550dff76d8550dfd76d8550bfd85d8550fdf73d8550ff980d8550bff8558550fdf7358550bff8654550bfe8654550bfd8654550bfc8654550f7d6554550ffb6158150ff96158150ffb61d4150ff961d4150dfe8759510dfc8759510fef8259510def825da65b7d87d9665e7f7599565f6f85dc965eee65dc965def85dc965dee65dc965def80dc965ded80dc965def72dc165bdf835c165bef825c165def725c1659ff8759465bef8259465d7f8759465f6f8259465ded655c865df9655c065bef8259760eef8259760ddd655cf60d7f7559560d7c7559560bef8259560e7f8559560eef82595609fd85dc5609fc8754560e7d65545609fd879db509fd859db50bef825db50def825db509fd87d97509ff8759750bef82597509fd87d8750bef8259550ddf65dcd50ddd65dcd50ddf73d8550ddf7358550ddf7354550bf986d41509fd861d510bef82595109ef825da659ed829d6659df835c26597f8759465d6e655c865d6d655c865de9729c065df2719c065dda735c065dd9735c065de9725c065df2715c065df1715c065cfb655c065cf9655c065cdf655cf60cdd655cf609dd831d5609ed821d5609f5811d5609ef825db509dd831db509ed821db509f5811db509dd839d9509df835d9509ef825d9509f887581509bd849d5109df835d510 else 0x8cc00610033ac253001130005908100d30c05308187a6043a6000b211300c78808b8d9010c2b2c60046404200059060590548084100920021202152000430008700043002010e004001c086480058c0070f18008184c600088129280e90349405491810d1d208004018c224031878c9040026324002081e1b2022436414386019070d904580845800458200022160a0400815981002040acc08014281a6004a7c8006169810800)
def g443H8 (j : Nat) : Nat := (if j<1 then 0x3230d121000000000000000000000000001858000000000000000000000000000000000000000000000185200000000000000000000000000000000000000000000000000000000909de040000000000000000000000000000000000000000000000000000000012198000000000000000000000000000000000000000000000000000000000000000000000000000000000022ba00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050fc0000000000185f00000000000000018068000000000000000000205c00000000000000000000000000a102000341f000000000000000100a000000000000000000000000000000000000000000000000000002b10000000000000000000000000000000000000000000000000000000000000000a2a000000000000000000000000000000000000000000000000000000000000081a400000000001403c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a00800000000000000000000007a0d000000000000000000000000aa000000001435c09586e000000000000000000145d8000000000000000000597b0000000181d8000000000000000000000000000000d4c000000000000000000000000000000f0e600000000000000000000000000000000000002085b06b616c000000000000000000000000000003c1e8000000000000000000a0700000000000000000000000000040e80000000000020d800000000000f0c80003425000030bc00000000000000000000006263000000000003d3c0000000003b0000000080900000000302e0000000000000000000000283f00000000000583a0000000000000000000000000000000000000301820208837e17c000000000000000000000000000000000682600000000000000000000000000000000000000000306d0000402c000000000d400000000000000000000000000000000000006177000000000000000000000000000000000000000000000000000000000000000000000000000b4d800000000000305800000007867f818000202ee56c30f000000000000000000000000000000000000000000b06c0000000000000000000037800000000000000000000000000000000060ea00000000000400a0000000000000000000000000000000000000000060f8000000000000000000000000000000000000000008104000083b80000000000000000000000000000000000000d18800000000000000000078610000611c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005444004100080018260 else (if j<2 then 0x7839000000000000000000000012b00000000000000000000000000000000000000000000000000d0a600024208000f2a6000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002af8e06c00000000000000000000000000000000000000000b130000000000000000000000000000000000000001000000000000020fe00000000000000000000000000000000000000000000000000000000000111d4000000000000000000581d00000000000000000000000000000000000000000484bf04600000000000000000000000000f0a8c1440000000000000000000000000170f000000000000000000000000000000000000000000000000000006ac20000000000000000000000681600000000000000000000000000000000000000000000000000000000000000000000000000000000000000784d0000000000000000000000000000000000000000029330000000000000000000000000000000000000000050070000000000000140000000000000000000000282b800000000000000000000000000000603400000001e138000000000000000000000000000000000000000000000000000000030228000000000000000000000000000004c2600000003c10800000000000000000098e8000140895270000000000000000000000000000000000000000000000000a1ec0000000000160cf43e8000005000000000000000094980000000000000000000000000000000000003000000014248000000000000000000000000000000000000000034310000000000000000000000000000000000000041480000000000000000000000000000000000000000000000000000000000000000000000151800000000c05e000000040630000000000000000000000000000006018000000000000000000261600000000000000000000000000000000000001803800000000001620d400cc28000000000000000000000000000000000120f000000000000000000000000000000389b4282000040252960000000000000000000000000000000000000000000000000610894a00000000000054300000000000000000000000000000000000000000000000000000000000000000000000084e0000082700000000000000000000000000000000000000000000010e00000016800000000000000000000000000000000000000001c12800000000000000000000000000000000000013070000143d0000000000000000000a0ac0000000000000000000 else 0x791f80e400000000000000000038ba00000001f0780000000000000000000000000000000000000e0ca00000003044005400000000000f0aa000000000000001e0c80000000d0d60000000000000000000000000010800000000000000000000000000000000000000000000000000000000000000000c0f000000000000000000000000000000000000000000000000000000000000000072aa65114230000000000000000000000000000000000c0860120000000060b2000000000000000000000000000001c1580000000000164b4000000062440000000785a000000000000000000000000003829f0c00000000000000000000811000000016a000006d3d0000000000000000000c0180000000c8f80000000000000000000000000000010130000000000000000000000000000000000000002ea00000000000000000000000000000000000000000000000000000000000000004188000000000000000000000000000000000000190340000000000000000000000000000000000000000000000000000000000000000000000000000000000d0e2000000000000000000000000000000000000000000000000340d00000000c0dc00000000000000000000000000000000000000000000000000000000000369f80000000000000000000000000000000000000000000000000001a4b8000000000000000000104f000000000000000b08400000000000000000000000000000000000000000f0f200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000601100540000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0d00000000281f00000000000000000000000000000000000000000000000000000000000000000000000681c00000000000000000000000000000000014173c3f000000000000000446c000190dc0000000000000000000000000000000000000d10c0000000000000000000000000000000000000000000014062c0c8000000000000003800000000000000000000000000003d37000000000000000000000000000000000000000000000000021e98098000000000000000000000000000000000000000000000000284a0000000000000000000000000000000000000000000000000000000032fa000000000000000000000068500000000000000000000000000000000000000000000000000000369280000000000000000000000000000000000000000000000000000000000000000000))
def g443D9 (j : Nat) : Nat := 0x5c81004141c930055850444f20079a38800458c4001105ca3040141c800c58c1c801414800f60018d21411d20048d2004104d810128c6144001da34878c04841070010f61440011460c2001140042084001112c800c5053c801450400c40010c60010c40400f60c00440c50401231410041050401058c10c6142043c801c48c10048f20030c1003141c801008c10c5040cb68c62020011128c10c5001c841451012320060c4c801011021430720050f20030070820010c30010c30401c40810035b3c831440011361320047c828b1e618bd1712d335ab04151f21fead47faa352ea153b2674ce9491d22b43e834fd9f23c6234eb81e38a6e4289ad342618ca9862ee5a08715921c5343913524c4687990e1fe3cc6f0cf1862c42289c108234420720cc1742884506c0a80f00f01e03c003ffb2ccbff5c665ffccab2fff70597feb82cbff59465ffacbb07ff65583feb2ac1ffdc560ffaa2b07fe76d43febb6a1ffd9750ffacba87fd71d43ffb0ea1ff54750ffecaa87fd65543ffb0aa1ff58550ffaa2a87fd65442febb4cb7f9d665efecb32dfd71996feb84cbbf99565fdee4b2dff70596ff3a8cbdf99465efaca32fed72197fd380cb7f5c065ff2e032dfe75d82febaec1bfd9760dfacbb07dd73d82feb8ec17fdd560bf8eab06ff655837eb2ac17fdc560ff6c0b05ff76d42ff3b6a17f5db50bf8eda85fd71d42ffbb2a17f9d950bfaeca85fc76543efb9aa17fdc550ff2c0a87fb50542ffbaa217f9d510bfaea885fc75443fcb02217bdc965bdae432df970196eeb9ec177dcd50
def g443H9 (j : Nat) : Nat := (if j<1 then 0x300012544000000000012050000000000000002ab6b079984c0003540000058c40001a328000c47384440000000c8a6a1b800000000000000000000000000000000000000000000000000000ab40000000000022e20000000000000000000000717f00000003aab000000000000000258a00000000000000000003064000000020e8000214300000000000000000000000000000000000000000000000000000e100029800000006190000000090af221000000000001f5a80000000a4c600000006d8100000000000528b00000001eab80000000000008b3011d0c60000000443c0000000182480000001001681000000000000000b80000000000000000000000000000000000000000240b5006000095ac0000000cae4a5e00000000a8b20003eaf0000d0b342000000000908e61400006532b2fc000004680008afe000122200001b0e0000000000080540000000607c00000003437e045a01e00000000000a0b00000c03948c0000206ac38800028b600000000000601bf4d0000387f0000000000000810001c0b000010230001b2280000000648a000000000000001254800000000001f19b006000000000000a468000000081e16398000000000000000000000141d800000000000000111900000000000280480000000000000000000000000262c000000000000000686600000000000000000000000000000000000000c0c0000000000000000000000000000000000000000000006d4300840002020c95f9311e08621c395e00019238000000000000000000000068c62078000000000000000000000000000000000745d603800025408000643c000008f0000000000000000000000000000000000000000000000000b87200000000000000000000000000c2d20002c91000000000000000000072cb421c4856954c0aa88a101a987d8aa8e0cc2b480000000000000000000001d5934250000c0b60002e280000000000018050000000000000002086000000014140000f42a0002a8b88320000d1b3c18800078bc4040000187e00015501c2415120000d6144358000000000000004c870001c038000000000000000000481900000000e0b800000002074000000000000000000000000000000813e85a000091a000065446886e0e3004000000000000844000000000000000207000000000e2d00001916000184744520000e1e88a9f428000031580005471204971d7c3600000000000000000000001223000071620000000000000000000000000051790001c0f40000000000000000000000c82400000006580000000000003075709c859c00044320000a85d00f9a8c48fe618000030440001e0b400000000001515ca2480000000000000000002201024030012412020080101002a10110101100201b0000001234330302300524 else 0x7e9514000000000000000000000000000000000000000000000000083c0000943ea1a00000001c5b80007a38000000000000000000000000000000000000000000000184400000000000000000000006555000088080000000000000000000000000000026c4a03e000000001218000a2acf40a98f000000000001a9319235ac0000000000000acc558b42680000000000042e0000000040eceb2b85182fa4934000614d000075f800000006ae600000000000025e0000000000060c4f20741b58520000612ec21b53300000000620000000000000405ec85e81e0000000000060040001c3980000001a1a40000000203600000000000000000000000272000000000000000842600000000000000000006010000000021c80002460000000024128000c0ef744c0000000000000000000000aa2000000003586000101500000000000000000000000000000000000000d8d511b411a00000000000043d8000000000000000000d09800000000000a224000000000000000a0b800000000000000000001508b1652240000000000086168acd013000000000000000b20dc1a8000000030240002a390000d045a0ac0000000000000000006d38000051ac000000050536902a2a0000000040c0000000000000001cab8464582600000000000000000000002410000000000000000000000000000000d44c000000000000000000029cea440000000000000000000422c0000000000000000000000000000000000000004c00000002d68d106363000000000000000082b000000000000000000000000003e942815c0ba0001e403558000000000004c1800000003c338000000175c44c26834000000032ba800000000000000000000000000c230a3a000000000000000000000000000000000080040000882000094e80000000769a0003544800000000000a240000588ba214eb18000000000038450000baba0000000000070be60e4000000000000000000106d909f65d4000285e12cc01a00000000000000024308000000100000000000000145ea0448000000000016237c51e90c21940000000000000000000000307400000000000324200000000000000000000000000f06e0003e3f000000000000000000000000000000000000000003017f469000000000000000000050cc0000000e8740003e2a800000006013e23800000000000000195c0000000000058)
def g443D10 (j : Nat) : Nat := 0x24ed200b39583288961c80120b6900611ad200c4b486010969006282c21845d9c49672583e1f00ff997fd65ff197ff60ff583ff50ff543fd10
def g443H10 (j : Nat) : Nat := 0x3ec60000000832000000000000002a33a03a81320aca2a988000000016b7da948c0090800000000000000000000000084c8000927400000000000000849000000000000000000000d2d4000000000000000000000000501e41c7a90000000183d60b4000000000000000000001e2700000000000c850000000e518000cb0400000000000000000b891427910c0006824ab5d057438c2e800000000000000000d06c000f0a80000000000e4b7c3c00000000000000000002100039250000000000340f0000000000000010800000002030000000000000000003c87000000000000005b0800000000000000000e0a0000000000094d80000003c3a00000000001e0feae000098940000000000450c000e05c0000000000000000000000000000000d43f63b0002c1922d0000d0cc0000000000b08c0000000000000000000000000003e13f0dc0000000000203492422e0000f864000f0580000002810000000000000000000000b050000000000018b0000a4efc180000000f50504748d81b2a2b800000002c368f000000000000000000000000000000000000000ea40492300800000000000000000990c000d030000912140a48a4000886b22f7002c40000000000000004047916000368f8918000000282f000000000000000002aaa3acf637000383f00008b3000043b844c000d823404000000030e5c260000000010800040480000000000307c287000000000000004a640000000000f48c00000000000000000000000000000000000000000000000016930000000f0040000003809000000070c8000000000000000000002a35000000094a800051180000000000f88c00000200000003c03000000000000008aec0000000c45da680000000000000000010d9d02e11391f00000000000c35000000000000000001088000000000000000000cbf00000002a8c000000040600000000000000d9140000000000000000068a000000000000000000c01400078080001af00000000d450000000000000000000000000000a0d201d0000000000000060c4000000382c94640000000000000000000000005818000602c00000000004840000aa08000c09629f90f8000000000000000000002c2e000000000000000000000f81400000000002105424187c000e2e4e0700012380000000dada24100000000000000f0a4000000000000000000000c1e0001c980002a47a232022000000000000000000000a0686a03b17cb20a2014c8400061011248049000000
def g443D11 (j : Nat) : Nat := 0xc641ff
def g443H11 (j : Nat) : Nat := 0xa1fc0fb1abc46d0000000006700000da7420000000000001ea001450000000000000003900000000a1000000000000000000b500000000000000000000000000000014600000b480000201000000002300121888000000000253000002200066143b002
def g443L : Nat → Packing
  | 5 => (2,6,4,0,0,0,0,g443D5)
  | 6 => (26,5,4,0,0,6,0,g443D6)
  | 7 => (135,4,4,0,0,9,0,g443D7)
  | 8 => (143,3,4,0,0,12,0,g443D8)
  | 9 => (74,2,4,0,0,11,0,g443D9)
  | 10 => (8,1,4,0,0,8,0,g443D10)
  | 11 => (1,0,4,0,0,0,0,g443D11)
  | _ => emptyPacking
def g443I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 9 0 8 1 3 g443H6
  | 7 => lookupWord 6 69 4 12 5 3 g443H7
  | 8 => lookupWord 40 1615 2 15 8 3 g443H8
  | 9 => lookupWord 66 997 4 15 8 3 g443H9
  | 10 => lookupWord 34 523 3 14 7 3 g443H10
  | 11 => lookupWord 4 79 4 10 3 3 g443H11
  | _ => fun _ => none
def g443 : Forest := ⟨443,11,fun i => g443Y[i]?.getD (0,0),g443C,g443A,g443L,g443I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P5_0 : block g443 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g443B5 : block g443 5 0 2=true := g443P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P6_0 : block g443 6 0 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g443B6 : block g443 6 0 26=true := g443P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P7_0 : block g443 7 0 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P7_22 : block g443 7 22 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P7_70 : block g443 7 70 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P7_118 : block g443 7 118 17=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g443B7 : block g443 7 0 135=true := (@block_merge g443 7 0 70 65 (@block_merge g443 7 0 22 48 g443P7_0 g443P7_22) (@block_merge g443 7 70 48 17 g443P7_70 g443P7_118))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P8_0 : block g443 8 0 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P8_30 : block g443 8 30 47=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P8_77 : block g443 8 77 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P8_125 : block g443 8 125 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g443B8 : block g443 8 0 143=true := (@block_merge g443 8 0 77 66 (@block_merge g443 8 0 30 47 g443P8_0 g443P8_30) (@block_merge g443 8 77 48 18 g443P8_77 g443P8_125))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P9_0 : block g443 9 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P9_5 : block g443 9 5 45=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P9_50 : block g443 9 50 24=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g443B9 : block g443 9 0 74=true := (@block_merge g443 9 0 5 69 g443P9_0 (@block_merge g443 9 5 45 24 g443P9_5 g443P9_50))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P10_0 : block g443 10 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g443B10 : block g443 10 0 8=true := g443P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P11_0 : block g443 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g443B11 : block g443 11 0 1=true := g443P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443T : checkedTables g443 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g443 0 0 0 = true)
  · exact (rfl : block g443 1 0 0 = true)
  · exact (rfl : block g443 2 0 0 = true)
  · exact (rfl : block g443 3 0 0 = true)
  · exact (rfl : block g443 4 0 0 = true)
  · exact g443B5
  · exact g443B6
  · exact g443B7
  · exact g443B8
  · exact g443B9
  · exact g443B10
  · exact g443B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443G : graphValid g443 (boundsBefore K435) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low443 : Lower true (varsX 443) (graphGoal 443) 12 := lower_forest (g:=g443) (i:=0) (hints:=4296044628) (before_sound K435 V435) g443G g443T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K443 := extendKnown K435 12 [(443,[]),(477,[101,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V443 : Known true K443 := extend_ok (m:=443) V435 low443 (by decide +kernel)
def g487Y : Array (Bits × Bits) := #[(0xfffffffc010228880fb0ff184d620824373d83,0xfffffffc01cb2cac04902f184d620c04173981),(0x1061c00ce0c4f041ff1f1ad7508fc78,0x1061c00ca2e45040af1316ca300f458),(0x80030f1f07019e07f8a5ec5c5a47c,0x80030d0b070994055876444c0a46c),(0x0,0x0),(0x0,0x0),(0x230603f01807fe1ff81fd8144fb40a8,0x2b0603901c03ae1f500cc8144fb0020),(0x3c07fc001ff8001fffe080b83bbd114,0x3e47e40014f8c00bfaa080b833b5010),(0xffffffffff800001fffffe00000d63eb78e643,0x3fe100001fb6fd0c6208d63eb68c442),(0x3fffffffe00000000000e751a461bc0,0x18186240000020000001010040b80)]
def g487C : List ColumnInfo := [(34,0,453,0,7),(128,1,358,0,8),(68,0,419,0,7),(129,0,358,0,8),(70,0,417,0,4),(100,0,387,0,4),(197,0,290,0,4),(38,0,449,0,4)]
def g487A : List (List Nat) := [[],[98],[81],[33,101],[81,98],[97,33,82]]
def g487D5 (j : Nat) : Nat := 0xd2600acc5a31d96258521
def g487D6 (j : Nat) : Nat := 0x39c016007ca00a9600a4c992a24c993264b550500567e5182dcd61ccfc26e6b92c399f84dcd6258676f28c16c2b0c77e4d879d921cf2c13033b24399f84e0d764873cf05c0aec90c7da607658521abaca8ecb0a435b5941d961486bab263b2c290f391d96258521
def g487H6 (j : Nat) : Nat := 0xe00000000000000056
def g487D7 (j : Nat) : Nat := 0x81681c0116a0aba42a811410000720024010c1082802e60080c828014a00bbe700fbe42c1b644107ef91041e541d4ea7b511ed387549a2908663a8f0fc75331ecea6c33174a84b210f066270f03c00bbf845cb61dbf845cb61bf581d8b61fd781dcd61ddf82dcd61ddd82dcd61ddf73dc961bbf845c961bdf835c961ddf735c961ddf73d8961ddf7358961bf78158961fd773d8561bf582d85619fd879d921bf5819d921df5819d921bdf835d921bf7815d921ddf835d921df7815d9219fe861d921df67658521df47658521fd78358521fe78258521fe562585219bf845cb619df835d92197d851d9219dd831d921
def g487H7 (j : Nat) : Nat := 0x70230e00000780108000003b300000000000001e2400000001ee00000000182c00000001a230533200180c0000000000000000a0cc15460000000000000000000000000001604c
def g487D8 (j : Nat) : Nat := 0x456f226f2a0f795404828224141914b4c0554025a48180816f59009b865426f200f70c90426e50c8bb24a19176686482ec990485de81913438cb958a9b2e8f425f2c56fb1560963b960721a007ff72d87feb96c3ffd8b61ffee4b0ffd72587ffb12c3ff58961ffcec90ffd76486feb96c3f7dcd61bfee4b0ff761586ffbb2437f9d921bfaec90dfc76487fab0a4377dcd61
def g487H8 (j : Nat) : Nat := 0x62117619000806d1d00051800000000000000000000000000011a00050a860000000000000e6763500060300000000000000000000000000000000061500000020700000000000000071100000066a90f00000000000000000000000080b00000093473a000b3b700000f01000d28c6b00026f000000a73000c0480c000d1600000000000000000000000000000072600000000000000000000000063900000000000000000000003111400000000000080991f96cf1330e000d68d12000000000000000b0d97d000000f1c000f6d000000000205108936c6e51e000000000000c1021b000e74000000000000000c020000d2c9
def g487D9 (j : Nat) : Nat := 0x2e8244ba9012d0a405c1a03ff61ff587fd21
def g487H9 (j : Nat) : Nat := 0xa20c1800000000000024800064600045fe25a0400000000121f00de1a000000000000001e60001d5aa4e00000000062200180e06200000000121c00000000125a001058000000000810a64001808000000000000001807ada616e01442e0a0122c380385200061425c001602ce
def g487D10 (j : Nat) : Nat := 0xd0227f
def g487H10 (j : Nat) : Nat := 0x9a0030802c400000000000000000000006544800000000000000000000300000000000000000000000000000000000000000000000000000000000156005a0000074db8000000000000000003600000002d400000000000
def g487L : Nat → Packing
  | 5 => (1,5,3,0,0,0,0,g487D5)
  | 6 => (13,4,3,0,0,7,0,g487D6)
  | 7 => (32,3,3,0,0,9,0,g487D7)
  | 8 => (19,2,3,0,0,9,0,g487D8)
  | 9 => (3,1,3,0,0,6,0,g487D9)
  | 10 => (1,0,3,0,0,0,0,g487D10)
  | _ => emptyPacking
def g487I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 11 0 8 1 3 g487H6
  | 7 => lookupWord 3 71 2 11 4 3 g487H7
  | 8 => lookupWord 10 169 2 12 5 3 g487H8
  | 9 => lookupWord 11 75 3 12 5 3 g487H9
  | 10 => lookupWord 2 79 0 9 2 3 g487H10
  | _ => fun _ => none
def g487 : Forest := ⟨487,10,fun i => g487Y[i]?.getD (0,0),g487C,g487A,g487L,g487I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P5_0 : block g487 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B5 : block g487 5 0 1=true := g487P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P6_0 : block g487 6 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B6 : block g487 6 0 13=true := g487P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_0 : block g487 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_4 : block g487 7 4 28=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B7 : block g487 7 0 32=true := (@block_merge g487 7 0 4 28 g487P7_0 g487P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_0 : block g487 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_1 : block g487 8 1 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_10 : block g487 8 10 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B8 : block g487 8 0 19=true := (@block_merge g487 8 0 1 18 g487P8_0 (@block_merge g487 8 1 9 9 g487P8_1 g487P8_10))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P9_0 : block g487 9 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B9 : block g487 9 0 3=true := g487P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P10_0 : block g487 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B10 : block g487 10 0 1=true := g487P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487T : checkedTables g487 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g487 0 0 0 = true)
  · exact (rfl : block g487 1 0 0 = true)
  · exact (rfl : block g487 2 0 0 = true)
  · exact (rfl : block g487 3 0 0 = true)
  · exact (rfl : block g487 4 0 0 = true)
  · exact g487B5
  · exact g487B6
  · exact g487B7
  · exact g487B8
  · exact g487B9
  · exact g487B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487G : graphValid g487 (boundsBefore K443) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low487 : Lower true (varsX 487) (graphGoal 487) 11 := lower_forest (g:=g487) (i:=0) (hints:=4329571927) (before_sound K443 V443) g487G g487T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K487 := extendKnown K443 11 [(487,[]),(502,[64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V487 : Known true K487 := extend_ok (m:=487) V443 low487 (by decide +kernel)
def g494Y : Array (Bits × Bits) := #[(0x0,0x0),(0x6c600ae40001f9841f9e0ffff41f18355668b2,0x74700ae50200b9840b9e8513ed08390d1620a2),(0x808133181f801e03e0fff0f00b4458446c80fb,0x8001934807a41e0160aa30714500f8106400db),(0x7063c17e0fe1ffc00e00f00007845618314fb,0x7061c04608e081c42e00f00204841e10110f3),(0x0,0x0),(0x807c01800ffe007ff000fff94c7d6b0f1d15a,0xa87c01a54ff4453f4412a6400c7c6b0e1d058),(0xff8001fff000007fffff0002ac607e497f064,0x5ffc0897f84981769f55cc062ac607e493f020),(0xf000001ffffffff8000000004d26bc1fd6f209,0xf8d180db9f71f7e31819e0474da6bc1ed6e008),(0xffffffe00000000000000000719aef8a292f84,0x2000000000000000008810100000080f04)]
def g494C : List ColumnInfo := [(102,0,392,0,4),(34,0,460,0,8),(136,0,358,0,8),(68,0,426,0,8),(170,0,324,0,4),(204,0,290,0,4)]
def g494A : List (List Nat) := [[],[115],[98],[81],[50,118],[114,50,99],[33,101],[49,117],[81,98],[97,33,82],[113,49,83],[33,115,101],[33,49,101,117],[33,113,49,101,83],[49,33,117,101],[49,82,33,113,97],[49,98,117],[81,114,50,99],[97,114,49,82],[113,33,50,83,101]]
def g494D5 (j : Nat) : Nat := 0x708393268d622597258110
def g494D6 (j : Nat) : Nat := 0x1820e883940b083c20800008e1c3874c003870e1c3873e003873e1c3870e1c3800e1c0070e1c3870e1c3870e1c3870e1c3870e0000000000000e1c3870e1c3870e1c3870e1c398141c0000e000000e1c511141c38000000313f95e11725c760b6c68391e1171d8293fa564b845c760c4fe578460971d8297ba55c980d87609e6e9191e037358255fa564b81dcd60c57e577360b7158313f95e11725c560c57e57835c97158315f95dcd82d8560a7ae8182dcb6158237ba564b8058560ce6e53736076058319f94e4d879d910c7c60590e0a7644297ba5609809d910e74e4d816027644295fa564b835d910c57e57836097644319f94e0d825d91085fe9592a18764431f191642861d910a7a68296608764431f19164286dc910c1fe5a9661772442979a0a5985dc910a5be89966177244295da325985dc910a5b68896617724420ffa9618865c910c6765193219724431dba064c865c910c6e65190219724431d993640865c910c7c645902197244247da5a5b87d891087768e96e1f624431f19164387d8910877e8d98a1f6244319f94e4d87d8910877e8d98ddb624434759558476d8910d2d651611db624421faa921d80d8910a5e69487603624429b9a421d80d8910a7668c8760362442979a51d980d8910a6e69076603624429d9a31d980d8910a7a68876603624431f1916438758910c3de479661d6244319f94e4d8758910c7ae4b9061d624421dfa36637658910d1d655611d9624434b594584765891085f6a687e156244217fa961f8558910a57e8d87e156244295fa365f8558910a5b68897e156244295fa35db855891085faa476e156244295da31db8558910973e8d97d896244257ba564a7658110c76e8e981d9604429daa825f8358110976aa476e0d604429daa81db8358110b6669076e0d60442dc9a21db8358110d5665783dc9604426d9a3259725811087eaa0965c9604425b9a4259725811097668c965c9604434e9622597258110b3668c965c9604431d898e0d7258110a7caa07658560442dd1a31d96158110b786887658560442d71a5dc96158110
def g494H6 (j : Nat) : Nat := 0x1c00024e
def g494D7 (j : Nat) : Nat := (if j<1 then 0x3835d910dddc2700bb221bdb83e01764437e703c02ec88767e13835d910eebc8f06bb2219df92e0d764433bb25c1aec88677e0f825d910abfcab04bb2215df93609764433bf06c12ec8857ee41825d910eddc2700bb221ddb83e0176443be703c02ec8847f64a861d910cfcc850c3b2219ee96608764433df2ac10ec8867b655821d910cfcc850db922197f96617724432fd2cc2ee48865f65985dc910cbe4b30bb922137d95219724427bb26432e48863fe1a765c910c7e434ecb92215f9909d9724431ff0cbb2e48863f219765c910aefc9aecb92218ff86a1972442bf321432e488577e4d865c910afdc830cb92218fd8621972442bbb26432e48867764c865c910cfcc810cb92213f990e1f624429fd2dc3ec48847fa5b87d8910c7f4b70fb12219f990e1f624423fb3143ec4884f7e4d87d89109fdc830fb12215df9361f624433bf26c3ec48867ee4187d8910a7f4b10fb122157d9521f62442bbb2643ec48847f66376d8910af6c94edb12211ff985db62442bbf26bb6c48847fa6076d8910abeca8edb12215dd931db62442bdb243b6c48873d58476d8910cfc43b01b1221bf181603624433f72ec06c48867e9d980d8910cfc3b301b1221bdb93603624437e722c06c4884fe6438758910cfcc870eb12214fd96a1d62442afb2b43ac4884dfe5587589109efc9b0eb12213fb9061d624429ff2cc3ac48855fe558758910aefc9b0eb12211ff9661d624431ff2cc3ac488677e4d8758910cfdc830eb12211fe9821d624423fb31bb2c48857b64b76589108ff4c4ecb12215df935d962442bdf24bb2c48847fa607658910abeca8ecb12215dd931d9624439eac23b2c48865fe1f8558910cbf43f0ab122197d87e15624432f90fc2ac48865fe5f8558910cbf4bf0ab122197d97e15624432f92fc2ac48865fddb8558910cbf3b70ab122197d76e15624432f8edc2ac48857b65f6258910bf4c86c4b12217f1919d960442bf3253b2c08877c6467658110afd4c0ecb02215fa961d960442bf3243b2c088776e5f8358110eec4bf06b0221dda76e0d60443bb0edc1ac0887f4e478358110bbdcab04b02217db9360960442fe722c12c08857ea637258110afd4b6e4b0221ddb83dc960442df72cb92c0885be2597258110afc4c2e4b0221cfb965c960442bf12cb92c08873e2597258110eedc1ae4b02215fb97d8960442fe323b12c08857ee5d6258110bbdcaac4b0221fd383e0560443be4ecb0ac08877c1d96158110fe9c1ac2b0221df37258560443be2e4b0ac088567e5181dcd608bfcab05b8ac199f84dcd7158333f09b9ac2b04eee5181d81608efc9b0f3b22117f9560a764433e302c04ec88667e13835d9108eec990cb92211df9361f624423bf26c3ac48847ea607658110adcca0ecb02215d9931d960442bd3243b2c08855e6577258110 else 0xb682c3ac25609b0405a0ad040a5800b882c4004ac005681660027408401683a2cc00668114084058f3d41b10a10508003a2002a20f301a83620820012a04102c5984cc205281c2cc2820e1e617300104c20030b842c28c0078400587185869800d0d308284c34c4d60e1078f30a8b30b9ea621ea0400008e006dfa0001b6e01a38001d4f11ca800b47103180000533bd81bbde15993120001adf63d0a000000018501a0681bb3ea79fc2800001993138f5180061406c28004290a0c631800318c631800710c60001a068000000006b7c004281d81a0001a000017edfa000017481b6e01a27a8160bd90a0015337c0001b4cd320001b465191a81a0681adf4fedf01a0681a0001adf01a06cc928000df46adf3d80001adf01aa03d8df00000000df01a0681a000000001b0a077108010a2810a000f637cdf01a06b7cdf37c0981adf3f2f601aec39600026e5b7ce58260681a06b540681a06b54df01a06b54cb312c480031aea000000000000000b4000aa28031800000000681a3181a9281a002227b1c467000598004f8003e8c63801a068c60689e1d81a1002606800000000000137f9560b71d8337f09b92e3b066fe11725c760edbc8f08b8ec19bf92e1171d8337b25c22e3b066fe13825c760abfcab04b8ec15bf9460971d8337f08c12e3b057de45825c760abfcaae5b0ec1bdb9360361d833f2e4c06c3b06fc5c580d8760bcfca303b9ac17db9060773582fb323c06e6b057764b81dcd60ecfca303b9ac15df9260773583baf02c0ee6b077564773dc5609bfcab05b8ac19df7360b71582beb23c16e2b055fe5582dc560cbfcab05b8ac1bbb90e117158373f09c1ae2b06f6e43835c560dcfc26e6b8ac1d9f84dcd71583baf23b9ae2b0677dcf825c560cdfc26e4b8ac19df83dc97158337f08b92e2b0677e0d725c560eebb9ee2b8ac1bbb84e01715837b707c02e2b0776dcf805c5609bfcab05b0ac19df7360b615827f720c16c2b067b60b72d8560ecfc26e6b0ac1dd791dcd6158337f09b92c2b06eee138058560dedb9f00b0ac13f992e01615837e6e3c02c2b05eee5181d8160dddca303b02c1bdb73607605827f724c0ec0b06fc60771d8160bddca2e3b02c17db935c7605837e303b0ec0b05eee5161d8160cefc9b0f3b2211ff9261e764426ff2ac14ec886fc605809d910dedc9b013b2215f990e0a76442aff2ac14ec8865fe55829d910eedc9b013b2219f98260276443be302c04ec886e7e13835d910cefcbf06bb2219de76e0d764437af23c1aec886f664)
def g494H7 (j : Nat) : Nat := 0xb30200000000000083b15319270843140000f0170000933f00000000000000001041000000000000000000000000000032520000234600000000f33a000000000000000000000000000000000000000000000000000070260000500800004323000000000000000000000000000000000000000013435027000000000000d0040000e00d0000000000000000501100000000000000296045000000000000000000000000002d5035000000000000000000002056703df7354024b02b00009001000000000000d03e2384000030430000000000000000f01ce39e62200000d048000070000000000010224326724d0342205400000000000000000000000000000000000000002328f03800000000201b0000133500000000f02a0000000000000000904e00006018f0400000d32900000000000000000000c00ce009203c0000133c0000000000009081132500000000000000000000d01e000000000000000000000000a00b132f0000b33100000000423700000000000000000000b04dd00f000000000000000090360000000000000000c0428049e233000000000000731ef0200000000000006002000000000000b0070000f01400000000000000000000c08c000033130021a05100000000000000000000000030030000000000000000004b000000330000000000000000103a904c0000701f604700000000b034902cc02f00000000b015000000003208002800000000802e0000000030051052c0120000a025d01d0000000a0000000000000000c3080000000000000000000000000000000000000000d0060000000000000000e013600e00003235a01a0000000000000000731600000000000000000000d05560500000534a00000000000000000000000000000000000000000000a345830300007010000000000000d312000000000000203b00000000b03000000000000000000000000000000000303200001031000090166044231800000000c0190000b04a7037000080230000403fb0460000d32d000000000000000000000000804f000000000000000050390000000000000000000050530041312136010001381102030
def g494D8 (j : Nat) : Nat := (if j<1 then 0x4006101acc41216b31041400c48636801618c068401a85b11112b0c4c5aac4e8bc4303aad1111a80ac401112b100a91ac4ad108105b842c73080133e91004440091e80cc4031cda100cd10c2002a80085100c73a86a91cc3031cea131cea0cac730c0ce10c1002040cc31001736a11938400c08530c0e8bc4403a47313a00268008a002eb9c0bcf792e05e03ae76eeb9d739f282b35c9b8a642e0485abb576dd5b636c642d81a8b45672cb590b15612c017a141582bad72ad959ab055da07576aed03a0757681d57aa0528a511ea4352893000294498a21262074f89c1262434c896127a4c4868f40022e47a8f51ea2e44483509a0d40e7e0f49dd3966f0c31863245049d9ad35a684c91862ee5a0ac94a2824ec9900924642c768e122842c7e0ed1c2360048cf19e24c5d09313e2b84f89310e1ec390660121442283905406c09009000bfd82dc760dff72dc760ff980dc760fbf845c760bff825c760dff725c760dfd725c760ff7715c760dff825c760dfd825c760dfd72d8760ff980d8760fdf81dcd60fdd81dcd60fdf73dc560bfd82dc560dff72dc560ffb80dc560dff82dc560dfd82dc560fbf845c560fdf835c560fdf735c560bff825c560dff725c560dfd725c560ff7715c560ffb805c560fdf73d8560bfd82d8560dff72d8560ffb80d8560fdf7358560dff7258560ffb8058560ffb81d8160ff981d8160ffb71d8160ff971d8160ffb61d8160ff961d8160bfd829d910ff9809d910dff829d910dfd829d910dfe765d910fdf835d910bff825d910ffb805d910dff825d910dfd825d910bff865c910bfc865c910dfe765c910dfd765c910dff865c910dfe865c910dfd865c910dfc865c910bff87d8910dff87d8910dfe87d8910bfd87d8910dfd87d8910dfc87d8910dff76d8910dfe76d8910dfd76d8910dfc76d8910ff980d8910bff8758910dff8758910dfe8758910bfd8758910dfd8758910dfc8758910dff7658910dfe7658910dfd7658910dfc7658910f7f8558910fed7258910fef6258910ffa7658110ffb8258110ff98258110ff97258110ffb6258110ff96258110bbf845c760dbf845c7609ff825c760bf980d8760fdb80dcd60ddf81dcd60ddd81dcd60ddf73dc5609fd82dc560bbf845c560bdf835c560ddf735c560ddf73d8560ddf7358560bfb8058560fdb73d8160bf981d81609fd82dd9109fd879d910bf9809d9109fd829d910df9809d910bdf835d910bfb805d910ddf835d9109ff825d910dfb805d9109fe861d9109fd821d9109fe86dc9109fd86dc9109ff865c9109fc865c9109ff87d89109fd87d8910bf980d89109ff87589109fd8758910b7f8558910dfa7658110df87658110fdb8358110dfb7258110df97258110ff38158110ff161581109bf845c7609df835d9109dd831d9109ed821d91097d85dc910 else 0x1102b0cb045ac22c00ab68216b6b11006e10c0ac201a08bc400eb002161ac386b01a1312c00c046b0c1ac00f101a0eb01a0d1ac00d1ac2ac500385b0a105b8400db0210e16c00da071cda0f1cc0684144003c730034530030b1cc3453a834c010347308002a0aa0514c0a84a9310314428010a0)
def g494H8 (j : Nat) : Nat := (if j<1 then 0x21800000000026e8000000000000839a000000001601e4056e827800000000000040034019600009041e18740000e623e32ff809e012400000000703a000000000160b8000000000000000000003cce0000043bc3008800000000801a280a800000000051d4014800340000251e79384000000009339101388eef411b304a602e6c0e42603d0a1000000001c0bb0000083280000000000004028f81a2608d000000002c0bc0000000000001401e0000d043a02fc00000000906d0022c0001e68f0000101280000a64f000000000000000000000193b0836a000000001804227860000233f8000000960000932900001546c00005039c9df400000000000021a500000e1e5b045000038c5a00002001800000000655c00000000000008601000063aaacc60000000a1f0358000000000000000034c420000000000003c121c60bc02b000038cd940eb0000000000000607f6358800000000000090378000002c800001325c066ac0c1c1c960f68000000000000011500000000060e4000060ad80001c01cb39b8000141340000b62e81d5c000000000000000000000a09900005994fc0168617e0137010580aaed33000000002804840040000000018d2c000000000000000000000333cf87228d7bc0440000281d0000006a2000051c7981040000103b80000000000000000000010cae241800006109f00a000b100000000000000051000048127c01d4e9400001993248b8c04f72db49affcc0e00000066800000000000070350838c00000000d055f9c6bc3b4000000000828901a4e4b600000000000000000000009c6cc028cc59000019de40000c03c5334b05fc0000a0bc83310000301dbebbdb01de909a432a00001023c1ce80000000000000000181afed1700000000202240000000000000c091041100000000000016642e02078b75c1600000f383999600c406772000000001011f607b701c299b70026600a632da037f008a0000000010153c0b800000000000020d61473e3000000000000000000006825c0000000090c100001c12d8c5ac029c86980001c60653b6082b3018e000090cc2036500dc0000201800001403020810000498ba816e0075000000000000020c000000000040d3473c0000000000001802500000000000012698d38e619eec0d600005054a1d70000000000000000028e9941c2000000003413a000020188000000000000000040247809b00360000000000001e0a440263030d406a00000000282ea41bd8527a0622023143d5605d460c0117681380033030f5839441134098308d180bc000120d4000000003810a00000000000000000000001c000006019020009eb005012a40019c20688a16088000202200621080b0852019383b0c0720408100480080580404418860000839400 else 0x783b80000000000000000380d8000000000000000000000401f000000cefc076c33b218680000000040b2b01c4000000000000000034cf9e0cf0000000030a4c0000000000000000160b500000000080f00000000078361c07a00000000000000000e01d2073e01c08046000093a58000000000000a04700000000000000000380a0000000009302d8318000040d30000000000001a02bd0088000089c8a05940f4383240001a22c0000000000001a05a3040785880000a1e100000000300040000000000003416600000000000000001c05f5070800000000000000000000000000000000061a9800000000c062800000000c42cf096c032000018029000000000000101ec2309800000000000000003064000008a3400003803000f545e39061003a80001c0b2000c81cd98cca0000702b8000201d8461c1091000000001a067006e480b7083281dc00007800781cd2149000021df00a58000020b180000000000000000000024c8c01010000000000001e6e0f05f000000000000096ad500fe00420000c009701f3d46ea6197032800028c6400000000283a6c02a60160000000000222000000001837400000705305a68193414ee4c9237131461416d21ae00000000000000000602c0000141820000f00b8000000000000a0235001400000000000000003c01200000000000000001203a00000000000000000000000000000000000000482f40000000000007197101700000b0f4e819a01c44062a51f21a2d40d14ec10000000000000c71d0000000000000000043bd8000000000000000000000000000000000000000001a74000006007c000060a1435d000010a542079d00451abc0000a042d06ad02bbccfac084103eb06eb8137e1d600004072f005820a5d27180001cc0166bc00005073000000000000028280000000000000419bc000160d0b0100000140c20000c01ce801c000000000000000024c300ec300003018f406ee695b0578000080da0000735c8000000000000435380003cc66c66ec0700000243940000a32e9836c00000000e2eec0254414c000000000000000000685b0030000214800000838f800000000000000004b0ce4087269262643806c8abaa4d500000000000000000b06658338000000000000000000000c631000000001005c407e03af000000000000000000000000000000a21579a7fc1540000e21280003013ec05b000069aaa4262c0880000080c90cf00000704980000000040a8000009a0a8d26000090cc80000000000000000000000000000000001051800000000)
def g494D9 (j : Nat) : Nat := 0x3515804d2e21834b888522802022a98808cd426a2b0f400a33d00406a33102316802a80114919a8030341989bd043ac3198d4394ca58cb64e43deadb630018c005b2710463298bc2a00ffee3b07fd71d83ffb0ec1ffdc560ffae2b07ff61583feb0ac1ff9d910ffaec887fd72443ffb1221ff58910bfae3b07df73582ffb8ac1fed8160bfeec885fe76442febb2217f1d910bfee4885fd72443fcb022177dcd60
def g494H9 (j : Nat) : Nat := (if j<1 then 0x30000048c680679026c88274c6600005526000008008c148f23f0000000006183139df052b88ff6e6e00006821a04560000000000000000000009022191a2caca0000c0b9f80d0000000000000000000000000000000000180ca00001008000000000005d00000000080c7016a501fe34cfca4a22250000680f400000000e02b0000000000a4f70b9000000000813400000000240740000a30e00000000122750000480b9588c0000000000000000000000000000000000653da09bc00140001607b0000601bc00002707000000000000000000000000000001e052800d1861c8c06b20c00000000280eee04600000000000016033000000002c416a1360000000000000000000000000000000000000030088000000000000100a9d4200000430f8000000000000000039d04000000000000000000001246500004855682a0812a50ac80001009ea40bc0bc000000d00042b0000501e000000000000000003c1020000b81cb1823c27c4047429b80000000000000000491b5c28e000095064099d4303206d50390000000014b6a6022904440001c65b0000000000000000000000000000000000013e890f400000000760780000000000000000715b400000000d02d601b9c26a0000000000002cc1400000000000038cc9c00e301b000000000e56bf041a05ec0000a130e01e489ae830cc618e21339c388041c0669284928f80039e107000000000c09c00009323000000ad1e0797042795cc4e7246245235780bd890c453400000000000000076000018568844d8586e02d80000000000000000000000000000000004000c00000000000019498ce9fb23b2317d862d000de73ea0148000000000000d0a100001001000000000000000001252b0000000034c04c018a21b28404c0474222000000000000000009132a149e80f8a66c202c000000001442520b6f821d421b817c0000310ce81164635751e8000208fb8064900f800000000266100007809f4a900000039e800000001200a2000800000000000000002912400ae000000000a8efccd40000a009800000001c03b00000000140b9602500000000141000000e08b7822340a1c61b0025f858142c5c0492285d181e4c3ba473800780000000100120000480e40001e52d00006802400000000202a80000c293a019000000000000000001335f98e2c2b9cb81e116a018bce89c0715008800000001a11e00000000000000000d0168000000000000000000000c0d000000000000015a8c0000f29600000000000350000519a70115ac33308c809980000c46fa01f3982c00000000a137800000000203000001109c00000000c00f00003c0bc0000e00dd95bc00500000c0448000000405620ec0a00101a884201001781052ad0c014c09004500a4c0040301c2f2100470421010006800a10460 else 0x136e62b1800000000000080005010400010263a2241c0300afa0000000000000000000000000488b000000000b041681c1c00eea0e0000500b10043e04000000000240a8004c00188048400002437f02c80000827a00001235d95d6827e00009307e290700700000e084000000000c075f0bc8000240d200000000648e4802a000073318000000000000000038144000000000000101ac000000000000300afc02880536216a85580000400c00000000140c2254972162002dc10a000000003343d0c4b270c0000000000267a4670000000000000000062bfe86140001807a00000000188126567000000002ce980000723300000000080740000289fc000000000000000000001a01d0000201fc1473e434000000000000000000019000000004000000004857c0000000000006805a8cba607300000889c00000000923a881800000000062bf286080001417400007005d004c0000f03511a040000000000000000000000000000000000000000000000381080000000085248000000000000131a0000080fc461a000000000406e0000802f80002031400000000089f800000000b81dd01b00000000000000000000000000f240a919000000000000068093d4880000f006984f00000000000000000244c80000c29b790890b0200000000000000001e04353a48000380fb45640000294880001456ad3880812000000000913448128000105330000000000000e16e02b)
def g494D10 (j : Nat) : Nat := 0x174218509896b03ff60ff583fd10
def g494H10 (j : Nat) : Nat := 0xc5b000000000000000000000000000000000000000000000000000000000000c0a8000000000000000000000000000000000050968228000000782c0000000629800000051640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000401800000000000000000214bc44800000000000000000a1719660000001a2b00000000001a4a0000000716a000000000000000000000253000000000002027102000000000050a2000000000061220000001811800000000014110001a29390de23681200000000000000e07000000000000000058000000000060280000000000000000000000000000000582200000004068000000000000000000000001801216fc9900000e900000000000000000000000000000000000000140008aa00021620005821205498344b90ae00000000000000000000182480000000000c490498000000162a00010762117e690000000000000000000000000000000000000000000952450800c00000000004298000000000001680000000000000000000011390000000000000000000000001e42800000000000000000000512a0000001c49e1da855a49a0007418000000000000000000000e4b701e0000000000000000000000000000000000000000018a6982460b800000020060000001200e8160000000000000000000000000000000080e0000000000180a0000000000000000000005069026c1680000002882084c0882141
def g494D11 (j : Nat) : Nat := 0xb41ff
def g494H11 (j : Nat) : Nat := 0x3080000000000000000322000000000002a000000000000001ef0000a50000000039063cd035461d000000000000000004a58150400000000000600000000012334d52a01b67000799000a380000000000000000000000000000017200000054d8a40000000000000000001f
def g494L : Nat → Packing
  | 5 => (1,6,3,0,0,0,0,g494D5)
  | 6 => (87,5,3,0,0,7,0,g494D6)
  | 7 => (239,4,3,0,0,10,0,g494D7)
  | 8 => (140,3,3,0,0,11,0,g494D8)
  | 9 => (24,2,3,0,0,9,0,g494D9)
  | 10 => (3,1,3,0,0,5,0,g494D10)
  | 11 => (1,0,3,0,0,0,0,g494D11)
  | _ => emptyPacking
def g494I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 9 0 10 1 5 g494H6
  | 7 => lookupWord 25 391 4 16 7 5 g494H7
  | 8 => lookupWord 88 895 5 17 8 5 g494H8
  | 9 => lookupWord 70 711 5 17 8 5 g494H9
  | 10 => lookupWord 15 319 3 14 5 5 g494H10
  | 11 => lookupWord 8 79 2 11 2 5 g494H11
  | _ => fun _ => none
def g494 : Forest := ⟨494,11,fun i => g494Y[i]?.getD (0,0),g494C,g494A,g494L,g494I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P5_0 : block g494 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g494B5 : block g494 5 0 1=true := g494P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P6_0 : block g494 6 0 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P6_48 : block g494 6 48 39=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g494B6 : block g494 6 0 87=true := (@block_merge g494 6 0 48 39 g494P6_0 g494P6_48)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P7_0 : block g494 7 0 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P7_17 : block g494 7 17 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P7_65 : block g494 7 65 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P7_113 : block g494 7 113 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P7_161 : block g494 7 161 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P7_209 : block g494 7 209 30=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g494B7 : block g494 7 0 239=true := (@block_merge g494 7 0 113 126 (@block_merge g494 7 0 17 96 g494P7_0 (@block_merge g494 7 17 48 48 g494P7_17 g494P7_65)) (@block_merge g494 7 113 48 78 g494P7_113 (@block_merge g494 7 161 48 30 g494P7_161 g494P7_209)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P8_0 : block g494 8 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P8_5 : block g494 8 5 46=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P8_51 : block g494 8 51 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P8_99 : block g494 8 99 41=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g494B8 : block g494 8 0 140=true := (@block_merge g494 8 0 51 89 (@block_merge g494 8 0 5 46 g494P8_0 g494P8_5) (@block_merge g494 8 51 48 41 g494P8_51 g494P8_99))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P9_0 : block g494 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P9_1 : block g494 9 1 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P9_12 : block g494 9 12 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g494B9 : block g494 9 0 24=true := (@block_merge g494 9 0 1 23 g494P9_0 (@block_merge g494 9 1 11 12 g494P9_1 g494P9_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P10_0 : block g494 10 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g494B10 : block g494 10 0 3=true := g494P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P11_0 : block g494 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g494B11 : block g494 11 0 1=true := g494P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494T : checkedTables g494 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g494 0 0 0 = true)
  · exact (rfl : block g494 1 0 0 = true)
  · exact (rfl : block g494 2 0 0 = true)
  · exact (rfl : block g494 3 0 0 = true)
  · exact (rfl : block g494 4 0 0 = true)
  · exact g494B5
  · exact g494B6
  · exact g494B7
  · exact g494B8
  · exact g494B9
  · exact g494B10
  · exact g494B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494G : graphValid g494 (boundsBefore K487) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low494 : Lower true (varsX 494) (graphGoal 494) 12 := lower_forest (g:=g494) (i:=0) (hints:=5134906960) (before_sound K487 V487) g494G g494T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K494 := extendKnown K487 12 [(494,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V494 : Known true K494 := extend_ok (m:=494) V487 low494 (by decide +kernel)
def g503Y : Array (Bits × Bits) := #[(0xffcc300f1887c8ffc6305800aa4a6c4ce4d0b,0x4944340b1882c826462010022a482c4c64903),(0xcc7003f88e1787f9c12e6145c5e03b1538c1f6,0xcc7001988e128428c22e200740a073012881d6),(0xf837c0f0ff8070e003c021b00e715446334f2,0xf81540b0a98070e002c8019006505046124e2),(0x0,0x0),(0xf003800ff01ff80ffd015ae11872453998a259,0x5003800f4017d00d99015ae10852453918a218),(0x3fff0001ffff00006f12881558c47713c25,0x220bfe6660497bd01000d10881558c46513421),(0x3ffffffe0000002486216c99078cb199313,0x204aabf4f56260e012006206c99078cb189111),(0xfffc0000000000000388fcca731c39a22535e0,0xab683080084002600288a40ed10138022114e0),(0x3f080ad651bc23ac6ca88,0x40001215108e0260a0030864a08)]
def g503C : List ColumnInfo := [(292,66,145,0,4),(129,16,358,0,8),(34,0,469,0,10),(144,1,358,0,8),(68,0,435,0,10),(16,0,487,0,11),(163,16,324,0,4),(322,36,145,0,4),(70,0,433,0,7),(1,0,502,0,11),(262,96,145,0,4),(145,0,358,0,8),(164,67,0,272,1),(352,6,145,0,4),(35,0,468,0,7),(69,0,434,0,7),(100,0,403,0,7),(38,0,465,0,7),(197,16,290,0,4),(212,1,290,0,4),(148,97,0,258,1),(178,1,324,0,4),(213,0,290,0,4),(98,0,405,0,7),(84,0,419,0,7),(71,0,432,0,4)]
def g503A : List (List Nat) := [[],[98],[81],[64],[33,101],[81,98],[97,33,82],[97,82],[64,81],[64,33,101],[64,97,33,82]]
def g503D6 (j : Nat) : Nat := 0x391114057185d425f835c97148560
def g503D7 (j : Nat) : Nat := 0x7820661cc10001b22050101c8816440f2245017c56440a03ae876b656565546565656565545443002700aad7c36c1a621d7148783b5c8b86989748570b5a5c425d725c521d82cc7f15b2e53835c560e31fa5e5383649715838c7e9794e0d725c560cb57b5e0da2dc5715824e7f11b9a5f8348560d3c5b26c697e0d215834c7ed7b465f8348560d3c7b2ec597e0d215828f5b2897e0d7148560b2d5c625f835c521582cd571497e0d7148560b395c425f835c521582d69710975c97148560f1c497e0d725c521582d69710975c97148530
def g503H7 (j : Nat) : Nat := 0xa800003c000000000000
def g503D8 (j : Nat) : Nat := (if j<1 then 0x42e85d30a6142e85d0ba174c29180ba6542e85d0ba174ef9df0ba77c2e85d0ba1748c05d3ae4608c1cf384174dd185206614d91b20ba40c3018534a6748199d32a6147b11820640c8190331a614b805d30a5e0b805d206578a613a25a460901181ae42c819032063d88190320640c818f61ec3a46b8361942f40e0b01462303d0680c01742804306c0d81481c000b3ed7443aecb8ac327fae6a7e19764864ff5c94ec32ec90eaf7b0698875c521d5eb60d310eb8a438bfae1a625d215c317e5c34c4ba42b84b7fb568b9161f60a6ff6ad1331b8ec18df663a564b71d831bec3f4ac96e3b063f59868772dc760b76b71d0f28b8ec15cfed5a2e5171d8339fd2f28c92e3b063bda8e53725c760ce7f4bca2e4b8ec1aed6a394dc571d827bbdab45b8ae3b047bfb46a69748760c7eb50d0d2e90ec19f9689a1a5d21d8339fd2f48cba43b067e7a2e85974876087fb715392e90ec147f6dea961d21d828ffdbb52c3a43b053bfb46a5874876087fd754bb0e90ec14efed19761d21d821ff5d12ec3a43b052fdb625d8748760a77b684bb0e90ec14fd6e2975c521d823fb5d12eb8a43b053f5b825d7148760adeb6c4bae290ec15dd6d4975c521d82bdada12eb8a43b075e4975c97148760d6bf4bc1b25b8ac1cd7e978364b715835ebc1b43b96e2b0573fb568b945c560f72f63ca706b8ac1ce7ecb94e0d715839ced9729c1ae2b0739f94e0f925c560ce7f4bca324b8ac1ad7e9783649715835cfd2706c92e2b0739f94e0d925c560e73f29c1ee4b8ac19cfe97945c9715839cfca706b92e2b06bd783e85725c560f72f29c1ee2b8ac13dded5a2dc5715835ebc1b45b8ae2b047bfb46a69748560cfcb44d0d2e90ac19cfe97a465d215833f3d1742cba42b053ddb9a5f8348560b7ab634bf0690ac1cf56c697e0d21582dcfda32fc1a42b05bd7b165f8348560e73f68cbf0690ac1cf5ec597e0d215829ef5b92fc1a42b047f6ba25d7148560adeb6c4bae290ac15dd6d4975c521582bdada12eb8a42b073d697e0d7148560e7a92fc1ae290ac1ee5e93835c521583de3c1f44b8a42b075e4975c97148560f78f06b92e290ac15cfed5a2e51714c339fd2f28c92e298673fa5e51725c5309eef6ad16e2b8a611efed1a9a5d214c33f2d13434ba4298673fa5e919748530cfcf45d0b2e90a611fdae8975c5214c2b7adb12eb8a42985775b525d7148530af6b684bae290a61d7925d725c5214c2cdada10ebb2e2b0d2dfb36819621d21d1db4cb910f3b243a5b6957221e7648669fda343caaeab8497eb8aa5515d570a9eb6c4bae290ae155d6d4975c5215c2adada12eb8a42b8635fa5e0d92dc560a73f68cbf0690ac14b76d897e0d215829ceda12fc1a42b041bfba65c9761361c36b2ed092ec26c325b6d4a760972d870b6d2ae44bb0c90d9a5b421d725c521 else 0xe0817978238c3304c301c0010000431052207220a024a0179014c3640b6406a204b0040607a401826881f172270c3f1722f0c3f1522f0c3c89280806e902c881c8aa40bc507c5c882f15220bc5c88280fc2c202684000bc3030270c0c0bc9c89c30004c8bc3030348bc30003e88103a22a022c4a808060002d04000ba1000260808fa7e500050d82e85d4207f82e9e70ba17)
def g503H8 (j : Nat) : Nat := 0x498ac180000038000000000000000cc140000000000000c6fb4280000000000000000000000000303fd0460e0000003d1560dc088a10100000c08702c0000000000000c1020400070240000000000002c02000f01581680c000d488000000000647c40c
def g503D9 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x875d921aef690875d9218ffaa7865d921a7fa9f865d921a7f69f865d921a7fe9d865d921a7f29d865d921abf2a5865d921afd69a875c521afd698875c521a7faa391dd570b6fe9191dd570b5f687955d570f5be97925d570f5be57925d570b6fe91915d570b7be89915d570b5faa5515d570f5be49515d570f5de45515d570d5f65775dc5709dfe9592dc570d5fe55755c570f5d545755c570d6fdd7945c570d6f5d7945c5708ffaa297485709efe9197485708ffaa097485709bf69897485709ef6909748570d7d25d7148570aefe919161f609dfe9592dc760cef61f945c760afd6a3715c7608ff6a297487609efe9197487608ff6a097487609bf69897487609ef69097487609dfe9592dc560cf7e0d92dc560ee7e53835c560cf7e0f925c560ef5e0f715c5609efe9197485609bf69897485609ef6909748560cf7e5f8348560cf7a5f8348560cf765f8348560cf725f8348560ef5e0d71485609dfe9592dc5309efe9197485309bf69897485309ef69097485309afe9191dda768df69792606769afe9191dd9768dfe9592e05768efe9191a1c768df6979260476add697926047696f69297e1b718bfea58621b71caf6199421b71cbb6199221b71caf619941db71cbb619921db71cbd619911db718dfe9592e19718bfea586219718ef6a686e11718efea586e1171caf65896e1171aed68496e11718efaa476e1171aeb68876e1171aee68076e1171acfe9592e1171ccfe578460971ccfe57845c9719dde9592dc5718dfe9592a1f61c6fe5e9761361aaf69a9761361aede859761361c6f65c9761361aeb6889761361aed6849761361acf69792613618df6949760b618ef6909760b61caf65984dcb618dfe95985cb61ccfe55845cb61a7b29d825cb618ef69297a1d618dfe9592a1d6187fea58721d61cede859421d61ceb6529221d61cdba559221d61cdb6559221d61ceb6519221d61ced6519121d61cf9a499121d61cf96499121d61cee6529021d61cfa64a9021d61cee6519021d61cf664d9021d61cfaa499021d61cfa6499021d618efe9198dd961aaf690879d961abb688879d961c7de1f915d9618bfaa4875d961aaf690875d961abb688875d961c9f9d995e0961c9f5d995e09618efe9198dc9618df69498dc9618ef69098dc9618df696985c9618fdaa4875c561aed690875c561af9688875c561b6d690875c561ced263945c561add697825c5618efe9198a1d21cf964991a1d21ccfe579461d21cf9e4b9161d218ef6909761921c7b5c89761921cf9e4b91619218efe9198dd9218efe91985d9218fdaa4875c521abd698875c521add694875c521aed690875c5218fd2a5865c521e7921d725c521ce7e51835c7708dfe9592e05708efe9191a1f608ef69097607608fb68897607608df69792607608efe91985c760ce7e53835c560 else 0xbdfe9592dc760cff61d92dc760ddfe9592dc760cff66372dc760bfd68772dc760efde85875c760eef61f945c760fede87945c760defe8b945c760def68b945c760defe53925c760cff61f925c760bdfe95925c760befe91925c760defe51925c760aff6a3725c760defe53725c760defe51725c760bfde85725c760efd6a3715c760efd61f715c760fede53715c760bfd68b715c7609ff6a69748760aff6a29748760bfd6869748760cff6a29748760dfd6869748760befe919748760bfde859748760defe919748760dfde8597487609ffa9c9748760cffea58748760cffaa58748760cff6a58748760cff2a58748760cffe5d8748760cffa5d8748760cff65d8748760cff25d8748760dfda5d7148760dfd25d7148760efd61d7148760fede917148760ff9e897148760ff95c97148760ef7e0f92dc560bdfe9592dc560ef7e0d92dc560ddfe9592dc560ef7e0f72dc560bfd68772dc560fede87945c560defe8b945c560def68b945c560defe53925c560ef7e0f925c560bdfe95925c560befe91925c560defe51925c560ef7e0d925c560defe53725c560ef7e0f725c560defe51725c560ef7e0d725c560bfde85725c560fede53715c560bfd68b715c5609ff6a69748560bfd6869748560dfd6869748560befe919748560bfde859748560defe919748560dfde8597485609ffa9c9748560ef7a5f8348560ef765f8348560dfda5d7148560dfd25d7148560fede917148560ff9e897148560ff95c97148560bdfe9592dc530ddfe9592dc530bfd68772dc530fede87945c530defe8b945c530def68b945c530defe53925c530bdfe95925c530befe91925c530defe51925c530defe53725c530defe51725c530bfde85725c530fede53715c530bfd68b715c5309ff6a69748530bfd6869748530dfd6869748530befe919748530bfde859748530defe919748530dfde8597485309ffa9c9748530dfda5d7148530dfd25d7148530fede917148530ff9e897148530ff95c97148530aefe919161e769efe9191dd9769dfe9592e0576d3fe5f9660576d6fe5f9460576adfe959261b71cbfea58621b71cbfea5861db718ff6a686e0b71cdfa1b9560b71cdf61b9560b71cdf9db9560b71cdf5db9560b71cfd61991dcb71adfe958260371ebde1b915d971bed69b91e1171aef69e76e1171cef65b84dc9719fd6a676dc5719fdea576dc571ded65b84dc571cfd65991a1d61cfde5b9161d618ffaa4875d961aef690875d961afb688875d961a7faa4875d961e7de1f915d961abfaa4875d961b3faa4875d9618ff69a97e0961cdf5d995e0961afd69a875c561e7d21d765c561cfd65991a1d21cbfe819621d21cbf6819621d21aefe91879d921abf698879d921aef690879d921e7b5c8879d921aefe91985d9218ffaa6875d921aefe91875d9218ffaa4) else (if j<3 then 0x551040be281800271644280f8a06d207c59105c5912903e1f04001b8400138dc2000f46000942a30386a3030003810002a1304001b04001508001001d3c28418c57298400e9e1420c63a8400100c0c000f47a100072105052100040390800391c84001e08001609c7e9f28005e183c181f0c181093860c0c1bc3060624e181d440c1400140b86070606c30005c96180039170c0018000f810c0e00d170440001d82181c00c1910800d169182201c01c10c01a2618a040cb0c01a2143046000c451c1138ba2e1f044f2505441e8983640d83220b8bc3e087c5d10a186c11463c5e18a3822e8a82a80d51a2d25044a0e882606540b2860c8b48271745cbe089c5e5f043e2e89862865b04618f179628e08b83c08003108002001840e19840012040016040011040010000c160c0c000d86060007c3000482e18003c1018001e840017a7ca000f05e9f28004417a7ca0012c2000b0408f4f94002d0400170400101800179145410e03b01d80ecd64042021010808404285b9844ce26113209844c225e12e196480e65932a89438776076f420eec99a48b22d90ac6a63e91ca8d4c6222cf14676fc4b83bb10d871c32e16707484dc20e0e904a81d808605901d7fe3f6df86fbd7c9bdedeb4f4278c3bb9dbeeb574e91ddd1cd2c7052e69734d0266c32ddc14c8d631b0c1cdae437112f4dc14b1f5cd2a6dbd2b9a58fade5734b3758fb721b72da156a3601566a9b53d3559a58b9a5cd34099b0cb7646b18d860bfd5e9ac7d734a9b5d92e6963eb795b52cdd63eaf556a2a6d566a9b53d083441aa59010808511627613b08f5482a20520a88135ca084f3a6b847a9c6400808535c98d4ba87743ba1dd0ee80843781dd01087750020214aea4a91ca12946684a425288b456222d15888b42da16d0e685b41d20650027ce3841c20f2a7ad3d69b9cdce7953739e54ee81833a99c80e106e7367860cd9e6ae0c19a34cd864231097dcb9a5ac2c11518a384f2258134496049823b91108223f01e30f1872636919f8c785c42af106808451c039010808404202113b09d84ec27613b09d825227611e80844aa021010808447a10808404201bc20d0108894042021010808404220d10687d40a205102880840720210108084042021010808404202101080840420210ee808404202101080843781bc0de008433603901080840421830b105040420210a0842021010808404a425202109484a42100de06f02d013806902880e40420210108084042000cffea586e0b71cffea586dcb71cff65986dcb71efde1b915d971dfdea576dc571affaa4875d961affaa6875d921affaa4875d921affaa7865d921aff2a5865d921aff68b9161f60eefe919161f60affe899161f60efde459161f60cffe8998dc760cff68998dc760aff6a392dc760cff66392dc760cff66192dc76 else 0x1d42118800060cc406080ee4080d640824081ec810a00e000c2564d106e40380030539000181c0010034410180e000c6164050004d101c001d900c000ec8070006070028839101829101c001828500003080060840018840051050800040607480605000451020804000a9010060c0600030600a084029010000308130305221400030048829149010001210060069049102080048948259250159019468ac81f16c943030964946883d15902e284c0c1f1406060d50081950171787220f97c5e08004e28a00e00138ae4038004e2829c800138a070007c5d101c0027140c07000830e2d9014001697c5b2018002f16c8070009c50b0183e28182e2c20001f141e2e900c0a000bc))
def g503H9 (j : Nat) : Nat := 0x325ce0ac281e814283a0001e8b800060430001c1bac1c8000906e00000000000d018869400000000001a12c00000000001e03400068c0000128e400000000000c0ff12619c9449c6189112000000010075105d0c100000003c2281ec0001008c00071eb8059a8554030000000121645158000000180ec00000000001689dc108000d341606c0000000109a0000000605f000000000000000000000000003865b4d787200000000000120d8000000000000000000222c000021440000000000100080002a4fc0b600018290000000140f800512000001a0ab01748140000000000000000000000000000000001a18400000000000e068000680f0000e09800000000000492e0d88000c366000000028340001676b4e5800000000000000400100a8e7638d3ca2a0001410400040006012000002e88112177e04d81c0000000000010e200000001613c000000000000003831c8b9a03e000000068250000000000000000001a88c00051b2a4710020c1a99e2e09427340000000000000000003205205a46a000049d9d3740001c03c012245e000302e203040d800000000000f0ce00000000000c3be200d0210000000000008342069604000000000000908000000000000000000000000000e37e0002c36800000000001024c82200000000000000000000001023000014a4000103300000000605c0000000703200000000024009ce0ac000121a0000000000069e1c00a8850c5200000001e0bc0025010000000000002833136c000342402348098002c4189226d053a15c0000000902a0000000000000000000000285003ba000112a700e0000811c01e9055704e00000000000a0bd428800000000000c1a800068440001814fc0f00000000e1ac00079a6a0c160f253628180000000345a8000d3680003d2d983200012916c2d6816e39461bc85e68c2803800021250000d45be192cee38580504f2b02e3544238c4a464012982127d001882211462
def g503D10 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xfc2704b8cff65b825c6eff2ac12e37bf9460971ddfc2304b8eefe13725c777f08b92e37f7915c971bfacb6e2b8fede13715c6feb25b8ae3bbf84e0171bdfca300b8eefe11805c67fb2543ec33ff9261f61d7fcc2edb0ebfa1d76d8777f2ec26c3bbe9761361ddecbb09b0eef25d84d8777f24c26c3bbd92613619ffcbb05b0cff25d82d875faecc16c33ff98dcb619fecc6e5b0dbf65b72d8777b09b96c33ff985cb619fecc2e5b0ddfe5572d8777b08b96c3bed825cb619fec970eb0e7fe1e87586dfb2d43ac33fe97a1d619fecb50eb0ebf65a875867fb2543ac3bf591a1d61b7fcb30eb0defe51875873ff2ec3ac33ff9661d61d7fcb30eb0eefe51875867ff24c3ac3bf79161d619ff4c10eb0e7f61c87586f7b2843ac37ed9221d61cff4b90eb0eef650875877dd2443ac33fd9221d61df6c910eb0efd644875877f52043ac3bf99021d619fecc6ecb0e7fe1f765873f90fbb2c37f591dd961b7f4c4ecb0dbf65e765875fd0f3b2c3afc879d9619ffcc2ecb0e7fe1d765873f90ebb2c37f7915d961e7fc3aecb0ebfa1d765875f90ebb2c3cfc875d961f7bc8aecb0ddf657825867fd2fc12c33fd97e0961d7f3b704b0ebf5db825876fb2bc12c33fe98dc9619fecc6e4b0cff26372586dfb2db92c37f591dc9619ffcc2e4b0cffa61725867f930b92c377f955c961bfbc8ac4b0efd26171587bef0eb8ac3bf6875c561dfa43ae2b0f7d21d71587def2cb8ac3ef4965c561f7b3b2e2b0fbd5d971587f6f28b8ac3bf7825c5619fecb70e90cff66287486feb2343a433fd96a1d21dfac8d0e90defe5187486fef22c3a433ff9661d21ddfca30e90efde45874867fd2e43a433fd9621d219ff4bf0c90cff65f864867fb31432437bd94a1921bfac8d0c90dfde45864867ff2ec32433fc9761921dfbc8b0c90cffe63764867fb31bb2437f591dd9219fecc4ec90ebf61a764867ff30bb2433fd985d921d7ec32ec90cff66076486f7b283b2437f5911d921bfcc80ec90efda1d714877e90eb8a43bf7865c521dfac32e290fede5171487fcf24b8a43fe5725c521ebfcaaebb877be4975dc3afaa2baee13ff9260770deec1ee3b86fd60771dc2f7f28b8ee1bdd835c7709fecc243b86f760d21dc37eb0290ee1d7f955d570ef7c92eab875f545755c27fb25c0ae17bf945c570dfbc0ae2b84ffa61215c27fb2343ec13ff9161f609ffcbb03b04ff25d81d827ff24c0ec13ff98dc7609fecc6e3b04ffe6171d827fb30b8ec17bf945c760dfac0ae3b04ff66121d837bf07b8ac17bf945c560defc1ae2b06f7e0d21582f7f28b8a613fd92e1d109fec910e884ffa5f824427fb2fc122177f955c9109dfca303bb4bfe61761db5eaecc08ed37f9560b71d5ebb309b0cefe518758677b2843ac33ed9221d619becaf04b0cefe51874865fb2c43a433bd9421d21 else 0xba42986ffe45879db7fb22c3ced7fd91dd976bfec9702bb77fe5d815dbdff2cc0aedfbf9460576bffc9302bb7fde05815daffb31436e3bff9261b71dfec930db8eff61b76dc6ffb313b6e37fd979db71bffcc2edb8effe6176dc6ffb2dc16e3bfe86e0b71dfec3705b8effa1982dc77fb0cc16e3bfe7660b71dfebb305b8eff61b72dc77ff04c06e3bfd8260371bfecbcecb8effe19765c7fef22bb2e3fbe76e1171fdebb708b8eff9db825c77faedc12e37fd96dc971ffb4b6e2b8ffd65b715c7fecedb8ae3ff576dc571ffac86e2b8dff65a875877fb2d43ac37ff9661d61dffcb30eb0effe1d765877fd0ebb2c3bfc875d961ffbc8aecb0eff5db82586ffb2db92c3ff7965c561ffabb2e2b0dff65a874877fd2d43a43bfd96a1d21dfec850e90dff65e764877ff0f3b243bfe879d921dfec3cec90eff21e764877ff30bb243bfe985d921dfecc2ec90eff261764877ff0ebb243bfe875d921dfec3aec90eff21d764877ff0cbb243bfd865d921ffb3b2e290ffd5d971487bff23baae1dfd91dd570effc8aeab877f645755c3bfeebb8ae17fd92dc570effbaae2b877f5d5715c3f7f28b8ae17ff925c570ffbb8ae2b85ffe5d215c2ffd2e90ae17fd9748570bfe4ba42b87fd5c5215c37ff22c3ec1bfd9161f60dfecc6e3b06ff61f71d82ffb25b8ec1bfd875c760fdfca2e3b05ffe4971d83feee2b8ec17ff9748760bff4ba43b05ff65d21d82ff92e90ec1bfd8748760ffab8a43b05ff64b71583f7f28b8ac17ff925c560ffbb8ae2b05ffe5d21582ffd2e90ac17fd9748560bfe4ba42b07fd5c521582ffb25b8a61fbf945c530bffc92e2987fddc5714c2fff2e90a617fe9748530bfecba42985ff25d214c3feae290a617bf9460776ddfca303bb4ffe4981dda7ff22c3cedafd98dda76b7ec8eed3b4ffe49819dadfb23bb2ed3fd92e0576bdfca302bb4ff646871db5ff30bb0edafe875d876d7ebb3023b4ffe49811db7ed2ec08edbf79460476dfaca3023b6fde49811db7eb24c08ed5fe97e1b71d7fc350db8cffe4986dc6bfd2e436e3afd8621b71bdeca10db8dfb64886dc6ff320436e3afd86ddb71bfac8eedb8cff66276dc79feed3b6e33ff985db71d7ec30edb8def65076dc6fdb243b6e37f5911db71bfcc80edb8ddfe5582dc67ff2cc16e3b7f9560b71bfac8ee5b8df764f80dc67fb25c32e35fd97a1971d7fc350cb8def652865c6bff2ec32e37bf9461971d7ec310cb8cffa63765c75ff0d3b2e3cff769d971bfac8cecb8ebfe19765c6fef22bb2e33fe981d971bdeca0ecb8dfb648765c6ff3203b2e3bbf86e1171ddf43708b8eef61b845c77790dc22e3fb791e1171ddfcb708b8eefa5b845c777b2dc22e3bbc96e1171ddfbb708b8eef9db845c777aedc22e3bbc76e1171ddfc9708b8eef64b845c777f21c22e3bbd90e1171dd) else (if j<3 then 0x10890c0034300080a04003810008001820201030800061820001830700e4a24115041c20241000c1c03908b0452241000d04002c5c3e422c1179289043a8a2a44113172f908b04508018300120c002c3000b0c1f04004c2e9e50700141c0400342c307c100170d081c18005c3c207060017a7941c004e9e500c20817a7940044205afd0a9caf3aba8ae0ab5cacbaaf8ab4aab4aa3aa60a8eaa0ca2ca87ca75a808a6c2982a532916a3828b2a1f2836a0227da9eb27689e1a7689ce8e529c326de9ae2692194a66c98fa62052c26023949612977143896ba588956a534941a4d092ca48c9199546910241a8fb23ce8ea237a8d723368d723368c622fa8b722be8a40a9c89ca244889a200878a1bc296219650e13d685e215a84f212683e20d28142076827207681420327ff1fbe7e81f7a7d31f167be1ed27b49ea479f9e5878c9e047779dc07669d7c05f9d5674a1cfa7331c960c19c6070c83067011bd66ec1b8a6d71b266be1aca6a51a6668e1a0a67919b66601980652991462e18e662e1892619182e5fe17c25e3176e5d20c100e790a80e783345c88ef85bf03b404310a804316de0e796c05b0105c0e78e52194969a19486521948652194967c59796381949612194865252c065252c15f44a795c64550652568065256094ec394955c1948e5255194b0533952854294ec53394b052c144e50e14125269474513943850493f44f593b84e4935c4cb93004b892c4017129e04a927048e920447591a845e9154449911043c90d4346839e42f90a82a7039e0ed107a417039e0e79036043027009c0ebc3f702704060ffa3f70fbe3e603883c78f623cf0f1e3be0e703b68af639482f03af0e8e3040e700e20a9c2a70a9c3948e3437f8c103760db235f0d560ed038831e83b40e20d380e78d1a0e78cf4331839e0e20c543280c7a3150a9c30b8c1009c0bea0cd0a9c2ef0b8e2da0b422c703342a70af60ed0a582a70ad02ac8a9c29d8a582960a2a28109de26e098a2590926216090023688b421f885820a87e41af07be194865219487a01de87441c986bc1c006da19486521af068e19a06521948652194862415f05fe17605a215f0546148017e05f819413703d213e84dc0f482700f484ae122044a10b04060fa03d20ed039e0e203520cd02700c182f00b482a40a18270089024208901fe074019406501aa065017e056010c043012a04300de02c0082020805c00b8000fffcb302bb7ffe6176dc7fff25b8ec1ffd92dc760fffb96e3b07ffe4971d83ffb24b8ec1fff725c760ffeb92e3b07ffa5d21d83ffb2e90ec1fff92dc560ffec96e2b07ffdcb71583fff24b8ac1ffd925c560fffb92e2b07ff5c971583ffd2e90ac1ffd9748560fffc96e2987ff64b714c3ffee5b8a61fff925c530ffec92e2987ffdc9714c3ffae4b8a61ffe9748530ffec else (if j<4 then 0xd84001c50061070d8d84001c4c2230600071609840038263610012098c0034100060c19040030700060f08181d040050681000d100f0a040054281000e101c00184c241000e0801041c42321880010058c0030a21000c2284003a10009091002842854213a1001109102a8e8400600a3a10a11228e84004a3a1000d0910028e8428642440301a3a1001c008428348082100120a10218400582840a63610019880050362c3070c10930d881c3050f0ec30c10901f0c004a2c3070c10930e881c3052200c30710030c1c30e22c30010070c003240ec30a1004903b0c005222408c300143403918a0450d0600e46281181c001b92890460007a264c117901c008b0450700a264c1141c008b04400a2c12810a0028a930450a2800a2a4c118004e8b04a050800a2a4411428a0008a93046c5c3a264c11717930c8b045c5a2c364c117148b0f044c5a2c328c11714a28a930f046c524a2c3c1281b14a30c8a93046c5e4cb22c117172e8993045c5cb22c113172e8b04a05c528a2a4cbc11b14a32e8a93046c513cba2c1281b14a32c8a93046c3c1000c081f0400407838100130f041c0046481000c88180036403a107108c8400302a1000f081c008444207000613a79400308e9e5070014202a841c40721000c081e840042107088c841c342a1000c08840034221000f088400361070ba40b94004006361071184002076361001009841c36361000c1c018436361070011a59409918400664e9e507001593a794280056963070da58c00307036100100ba7941c00510a4e9e50a001a928e87a794006a4e9e50700141d0ba7940056382610007140ba7940048207e9e500168c1c20223000c3a8c00301070804002026403810015901800303108100102104003c2c1000e91040032441000c200c180040203080106001b081c010444341000c201f040044107000c1d040030207c3c100150b040030106000d0818003180fc20800061823080018442034100102c0c3f090400601c243001308040030881000c043400184030107000614060e0400403010006110a0e040040803c100101f040030743410010081c0f04005031701060017090d040044203c100101c0f0400407c3c1001208070400482c3000c18002824107001209040030182434100170c0b040048207c10010200d8400410e9e50a001447a79400401c2c4636107001fa7962000401e9e50010000d8428402c4e9e50a00190ba7940040301e9e5001407a794018f09842080003a10a1008480030803a100100804200e840064212000c402a840040a10a100100e840030a1003a10014208c8400421000a0823a7940058200610a120821840040a02c4e9e5001a0ba7940040a8244e9e500183c930c004c9c5c3001289040030fc924c30c1724901f0c408000724c362141c2000543c90700c3 else 0x2881801041c56428c1001305901c004c1a200641289901c00428a2640a001590a1041e88006a20007641104a00030a060028131590a30f045c564c3c1131689930f045c56428a2c3c11b14a30f044c5430600281715932ca304006cbc5c10764001b172f068801906c5a26407001714a28990280064bc564284107a2002316881c019054bc5412800142b141800a0507628100118a0400324c3c1070016881d0d040050722c3c100170f04001c4c322c10011928e841c40064a3a1071608840030621000e918d8400412a463610016901d84004a46361070016101d840048463610700144a92098d840060fa3000d901e8c004c2002107128d0a840040600610712098)))
def g503H10 (j : Nat) : Nat := (if j<5 then (if j<2 then (if j<1 then 0x605600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008c400000000b695e0ced0072000000000000000000000000000002d1e060a4000000000000000000000000000001613af0a500000000000007092d227000000000000000003cdce00ae000000000000000000000001180000000000000000000000000000000002c0420000e0190a4a40000000000000000000000000f3860000000000000000000000000080ee00000000000000000801400000000000000000000000000000000000000000012102102d80002845c000000000000000000000000070238000000000000000000000000000000000000000000a1888000000000000000000000000000000000783d40000000013410000000000000000000000000000000000000000000000000000000000000000703180000000000000000000000000000000000000141ac000000000000000000000000000000000000000000000008dd20000000000000000160c7000071c00000000000000000000000000000000000000000000000000000000000000000000008e1c000000000000000000000000071cb800000000704b800000000000000000000312560000000000000000000000000000000000000000000000000000000b37d1025000000000000038ca4000000000000000034406000000000000000000000500a0000000000000000000003021967290000281cc0001c2f60000000000000000000000000000000000501b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028e0600000000000000000a03400002010940bc000000000000000000000000000000000000006064000000000000000000000000000000a04e000028e6200000000282ad85600000443f000000000000000000000340760000f04680002402c00000000000000000000000000124400000000000000000000000000000000000000000000000000000000000000000003c21c0000000031bd8000000000000000000001e141b09700000000000000000000000000811400000000000000000000000000000000006392404480001810b00000000000000000000000000000000000000108a80000000000000000000000000000000000000000000000000000001605a00000000101cd0129a0528000000000000006c800034607e11300000000381f000000000000000000000000000000000000000b0a300000000000000000000000000000000000000291b600000000000000000000000000000000000000000078cfc0000c2004204004000041105400121504000114110400100a1805c else 0x240f000000000000000000000000000000000000000000000000000108d30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000341f80000000000003d26c00000000000000001e6f400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000280dfce43a03000000000000000000000000000000000000000000000000000000000000000000000000000000000000007013800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084bc00000000701d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000016143000000000000000000000000000000000000000000000000000000000000000000000000698b580be00000000000000000000000000000000000000103dc896400000000000000001020200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003024200000000000000001806d000000000000000000000000000000000000000000000000000000000000000000000000201c800000000000000000000000000000609ac000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000161270000683900000000000006015000000000e38500000000000000000000028dee000000000000000000000000000000000000000000000000000000000000000000000000e39d0000000014725000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080ac000000000000000000000406600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000683a000006895000000000000000000000721a000000000000060074000000000000000000000000000000000000000000000000000000108e43059000000000000000000000000000000f05c800034c5e000000000000000000000000000000000000000000000000000000000000000191f0000000000000000000000404780000000000000000) else (if j<3 then 0x1208c51a08000000000000000070478000000000000000000000000000000000000000000d135580fc00000000000000000000000000000000000000000000000000000000000000000003865400000000000000000000000000000040f20000000000000000000000000000000000000000000000000000000000000000000000000000200a4000000000000000000000000000000000000000000000000000000000000000000000000000000001a43c00000000000000000d13c00000000000000000000000000000000000000000000000000000004079800000001a1070000608c000000000608280000000162430000000000000000000000000000000000000000001c2800000000000001844fe048f48e80000000140de00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000041a6c80900000000000000000b02200000000000000000403ec00000000000000000000000000000000000000000000000000000000000f46780000000000000000000000000000000001a33800000000000000002c0220000903b800000000000000000000000000000000000000000000000000000030c5400000000000000000000000000000000000000000000002400ce7060000000000001c0960000000000000000000000000000000000000000000000000000000000000000000000000000000000000739b000000000601500000000000000000000000000000000000000101ff813600000000000000000000000000000000000000000000000000000000000000000000000000000a358000000000000202a80000000000007095c00000000000000000c46b866f00000000000000000000000000000000000000000000000000000000000390160000901600000000000000000000030cf0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006837400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003835000000000000000001c01c00000000000028272000000000000000000000000000000012000000000104240000000050508000000000000000000001c5b8000000000000000000000409b701540000000000000000000004047000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030c5c000000000000310da else (if j<4 then 0x401b00003004c0000000000000000000014331000000002c2500000000000000000000000000123bc000000000000000000000000000000000000000000000000000000000005437800000000000060910000000000000437f8000281a000000000501f80000000000000000000000000000000000000000000000000000001e0e00000000000000000043968000000000000b378800000000000000000000000000000000000000000000000000000000000000000000000000000000506bd80c400000000609f59c75801000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000285fc00000000000000001808b00000000000000000000000000000000002138800000000000000000000000000000000000000c298000000000000000000000000000000000000000000000000000a06000000000000000000000000000000000000000000000000006e00002b0240000000000004815c000000000000000000000000000000000000000000000000000000000000000684f0000000000000000000000000000000000000000000000000001413282d80000000000000210800000000000000000000000000000000000000000000000a0180000000000001e80f0000000000000212d00000000000000000000000001c0a60000000000000000000000000000000000000000000000000000000000039bf8000000000000000000001011d00000000000000000000000000000000000000000000000000000000000000000000000000001ce580000000000003401e00006488800000001409d0000000004de4000000000000292200000000000003817c000000000000000000000000010cdc00000000000000000000000000000000004e3c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001814d000020411c4d000000000000000001201000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c5c2a05c00004248501b400000000000000000000000000000000000000000000001060800000000000000000000020280000000000000000000000000000000000000000000000000000000000000000000000003c1d600000000484d000000000000000000026a00000000183a846280000035e000000000000000000000000000000000048c2c000000004096000000000000000000000000000000000000000000000000000000000000000000000000000000000c08b0000000000000243f8 else 0xbd400000000000000000000000000000689cc0000000000000000000000000000000003061e0000000000000c1b80000000079c8c4034000000000000291e4000000000000000000000000000002d1040000000000000000000000000000000000000001271a4a2400a00000000000000000000000000000000000000000000000000080860000000000000000000000000000000000000000000000000000000000000000000034510000000000000000000000000000000000000000000000000000000000000000000042471004400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002412a000000000000000000000403400000000000000000000000000000000000000042340000000000000000000000000583bc00000000000000000000000000000000000000c1302189800000000000000000000000000000000000000000000000000000000000c08000000000000000000000000000000000000000000000000000000006048c000000000000282d00000000000005012f827a00000000000000000000000000000000000000000000000000000000000000028c5600000000000000000000000000000080c80000240600000000008f30000000000000000000000000000000000000028bf400000000000000000000000000000001d00001e3020000000000000000000000000000000000000000000000000000000000000000000000001001c0000000000000000000000000000000000000000000000000000000000000000000000000000000000003814e0000000000000000000000000000000001c6f80000000000000000000000000000000000000000000000000000000000000001632400000000000000000b002000000001c728000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000305100000000000000000000000000000000000000000000000000000003c1500000000000000000000000000000000001c8a030660000000000000e0598000041e0000000000000000000000003600003c04c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0600000000000000000000002016a0000000000000000000000000000000000000030048000311b40000000000003c182000000000000000000000000000000000000000000000000000000000000000000000000133f800000000000000000000000000000000000001c2880000000020ba680820000000000000000000000000000000000000000000000051a4000000000000000000))) else (if j<7 then (if j<6 then 0x60bac000000000000000038048000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040050000000000000010d0000000000000000000003c04000000000284540000000000000000000000000943a800000000000000005824c000140d583268000000000000000068184000180e3000000000000000000000000000000000050a4800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000122fa000000000000000000000504a800000000000000000000000000000000000000000000007039c0001866d00000000000000000000000000000000000000000000000000000000000181140000000000001803800a90000000030cea0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010147000000000000000000000000000000613b00000000380a400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0800000000000000000000000000083a5c0fac08800000000000000000000068400000000000000000000000000000000000000000000200100000000000000000000000000000000000000000000000000069ba00000000000000000000000000000038cbc00000000000000000000000000000000000000000000000000300e140fad3868000000000000a01e00002815aa0bd0000000000000000000000000000000000000000000000000000000000000000000000000000240ea0000f043b046000000000718b8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001600d000000000409e0000000000002860200000000000000000000000000000000000000000000002420600000000000000000004a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c81200000000000000000000000000000086ee0000121900000000000000000000000000507b000000000000000000000000000000938100000000000000000000000000871a0000000000000000000000000000000000000000000000000000000000024e600000a0868000000000000000079 else 0x31ccc0000000000000000302220000000000000000000000000000000000000000880000000000000000000000000000000000000000001205100006808c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006148000000002126e000000002922c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000c0000000000000000005ba000000000000000000000000000000000040c500000000000000000000000000000000006021800000000000000000000000000000000000003114800000000000000000612b000000000000000000000000000000804c00000000000000000b246488d800000000603280000000000000000000030d4c80afe07a0000000000000000010ce4000000000000000000000000000000000182852cfb000050c240000211f0000000000000000000000000000006133000000001c1ca0000000000000000000000000000000001009281a1800000000000000000000000000000a026800000000000000000000000000000000000000000000000042000000000000000000000000000000000000000000000000000000000000000000000000000000000417c80000000000000000000000000000000000000000000000000000000000000000000000000000800b000000000000000000000000000000000000000000000000000a19e000000000e0a300000000000012081000000000000000000000000000000000000000000000000000000000000000000000000000000001210f0000000000000000000000000000000000102c80000000000000000000000000000000000000000000000004880000000140e20000000030178000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000833ea47d8000000000000000000000000000000000000000000a680000050b88000000000000000000000000000000000000000000605300000000000000000000000000000000000000000000000000000001419e000000000000000000000000000003826e000090670000000000000000000000000000000000684280001a6fc00007818a018720f7b027283e40000000000005229c00000000240b00000000000000000000000000000000000000000000000d3954827800000000347d0000000000000000000000000000000000000000000000000000000000000000b44a000000000000000000000000000000a05b8000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if j<8 then 0x70507005c000000000000580bc0000000000000a3c40000000000000000000000000000000002c106000000000000000000000000000000000000000000000000000000000000000000000000118700000000000000000019bb044600000000000000000000000000000000000000000000000000000000000000000000000000000000000000676000000000000000000000000000000000000000000000000000f48d8000000000000138400000000000000000000000000000000000000000004878000000000000000000000000000000000000000000000000000139c00000000000001068800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008032000000000000000000000801a80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e035800000001414b0000000000000000000003235480d20000719600000000000000000000000000e13f000000000000000000000300cc000000006033a83080000a2e0000000000000000000000000010e080000000000003501c000000000000240d4000000000000000000000000000001c1620000000000001822fa0760000000010e6400000000000000000000000000000000000000104d00000000000000000000014456000000000000000000000000000000000000000000000000000000000000000000000000000000003827000000000000000000000000000000000000000000000000000000006064800000001e6eb00000000000000000f0620000000000000000019ba80000602d60836026000000000000000000000000000000000000001e7110000000000000000000000000000000000338800001c17e000000000000000000000000000001c1a4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200f801740000000000002c0de000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000084c80000000000000000000000000000050b3400000000000000003c02400001483000000000000053440000000000000000000000000000000000000000000000000000000000000000109300000000086f3000000000000000000000000000000c705846880000000000001199000000000000000000000000000000000000002d0cc871f000000000000000000000000 else (if j<9 then 0x10448000000000000b00000001c10a00000000000000000000000000000200920000000059bbc00000000000010492407a000000000000000000000a01758bec000000000000000000000000000000000000000000000059c6c000000000000000000000000000000000000000000000000001c13e0000000000000000000000000000000000000000000000000000000f16d8000000000000000000000000000000000000000000000000000000000000000000000001d23c80cb0000000000000000000000000000000000000000000000000000000000000000000000000000340f40000000000000000000000000019d0000000000000183fc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cf80000000000000000000000000503c40000000000000000000000000000000000000080ca90128000000000000000000000000000000000000000000000000000000211d660ed00000000000000000b02e8000000000000c475000000000000000000000000000000305c0000000000000000000000000000000000000000000000000000000000000000000000001c19a0000000000000000060df808d80000000000000000703b000000000511980002cd4a000000000000000000000000000000000000000000000000000000000000000000000000c01c282ec000026f000000000000000000000000000000000006058000000000000000000036c0000000000000000000000000000000000c18c271c000000000000148f40000000000000000000000000000000000000000000000000000000000000000000000006a47c0000000000000000000000000000000000000000000000000000000000000000000000000000d03e0000000018330000000000000000000000000000000000000000000000000000000000000000000002015000000000000000007838581fd201e000000001000200000000000000001201f00000000000000000000000000000000000000000000000000000000000000000000000000003828a000000000000000000000000000000000000f2000000000000000000000082080000000000000000000000000000000000000000000000000000000000000000000000000000000000002c1b00000017e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002001800000000000000000000000000000000000000e08e00000000000000000000000000000000000000000004058000000000000000000000000000000000000000000000000000000000000000000000000023500000000000000000000000000a02280000000000000000000000000000 else 0x1016c0000000000000000000000000581c400000000000000002c240000000000000000000000000000000000000000000000000000000060988000000000000000000000000000002167f8c64000000000183883f4000000000000000000000000000000000281580000000000000000000000000000000000000000000000000000000000000000000000000000504640000000000000000))))
def g503D11 (j : Nat) : Nat := (if j<1 then 0x2006049008d111a1d3944001816911945001810842004462108010508468400a22144008450222442888c3a1004a94a084210030f1ca5180162a2930c00a3a4c5450c00d26288860050e3a4e4440218e03249441e18d24422480218c1c064450451001422490468b0f222822c5510d124823459791141162a896892411920e860040f921a282006c59008010383020041b921a2820060e000879110002223c8861080c087d3961240040ac88e1210e364d39410700303d2072c2481c011a72820e0051108001106c2000448490001106811f0e1000c387c90a1c10030dc90a1c1003030e100c38400311080010c683030800a000c3849030c340c3050400c0c080d3961081c40303a72c2881c0122018a03a72c2881c014101e900072c21040a470908814444848d08018469ca28144003c948021883d200862491e88003147c9c49218b271248620f440018808400022084400088200031c224063834590087a72e404202c8043c5900871aa8d546062a315189b421220d0d6856c21209ae1580b3fb5f50f7f7a7bc99e16ee2763ba95cf8e4570ab795b5cd6969cb45d9dcccc66632a9910c6661b306d7d6bd05d3addd68eb2557aab15546a8152c28bd3d49ba4c8a5a127090f46c22a10f084f427a07cfec7f63e31e74f3a76d3a59d2ce3600037c82c0dae6a70691a30cd46483051768b5456c2a19484a424ff26e92988ec4462040fb47883941b20cb45d029c12f08d440a1ce0d606282c213808b03d01a4000058023811c07302c000006c01b0000003ffe0776ffd81ddbffdd976fff815dbff60576fff86dc7ffa1b71ffd86dc7ff21b71fff76dc7ff9db71ffd76dc7ff1db71fff82dc7ff60b71fff72dc7ffe0371ffd80dc7ffe1971ffe865c7ff61971ffc865c7ffdd971ffe765c7ff5d971ffc765c7ffe0971ffd825c7ffdc971ffd725c7ffe0171ffd805c7ffdcb61ffd72d87ffe1d61ffe87587ff61d61ffc87587ffdd961ffd76587ffe0961ffd82587ffdc961ffd72587ff58961ffe87487ff61d21ffe86487ff61921fff76487ff9d921ffd76487ff1d921ffd80487ffdc770ffd71dc3ff48770fff715c3ff5c570ffd215c3ffdc760ffd71d83ff48760fff71583ff5c560ffd21583ffdc530ffd714c3ff48530fff72443ff5c910bfd81ddaff61e76eff769daff60676eff765daffe0576bfe871dbbf5d876bfd811daff61b71bfd82dc6ffe1971fbf845c6ffe0971ff7715c6ffa1f61bfd87d87bf5db61bfd82d86ffe1d61bfe87586ff61d61bfc87587bf9d961efd76586ffe0961ff571586ffe1d21bfe87486ff61d21bfc87486ffe1921bfd86487fd5c521dff75dc37f5d770bfd81dc37fdd570dfd755c2ffe0570bfe87d82ff61f60bfd81d82ffe1d10bfc87442ffe0910bf5811dafe60076bbf845c6ef61361bdd83dc2f7e0d60 else 0x8a1c100222481c0011520d868a080191a1001e40e8e121003294a0922100301848d080143e4840108a06242461d0801d22310874e5003a4d394380161a382861694994012392a9460050ea7242008c601091a10e2c2420030f091a1002c2421c3848d08010064841d08a0620047090871d4a549090801a169499438018442d29328a003a4108d0c2d394380274e584903801a129461c41ca6123002c24904008061000c20787040090a1c10022406080800c342020030d106c200046480030690443820054806143820060e352438)
def g503H11 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xa04f8356000000003060600d00000d05880000427e0000501e98e4800000000d63fc01fec1a1c02160060000298324094703690d580000000000002814e425ea347806d680a40001a0ba819572368000040df10b0d861b00c7c980b1cb80000000000000000000000a2200006018b3585110400000000000000000000002b98000041f80000609bd824bc0ac000000000000000012481000000000858fc0498093c9638802a0000000060d200000000000000000241e9623e71ba80003019c000000003343606edc204000000003d2ba00000000000000000a00ab1538000140e8000000006034482fde082f08e80002c2a9231d2052e05900000000000007042441e000000000182f40001c2fa0000182fc0000000000001017f457a00000000300c2429c0000e01900000048800000000101a80000000000002008c00000000000078270000100a3903e00000000040c3f3a00000282cded3000000000000000008e063a005c0000001a866cc8db40001c934000000001c260000000006a49ec570415fc04800610800000d90000782f9c22c204f2174800038d90000031185065c000121a731d2800000000402600000000000014035000000001d0ff80810000681e40000000000003a11ec072c025d0578000000002069164080000409a0000000052d5a0db2c006641eb14a012c3a001d1cdf10c40000000082990016bc876e73751d0601b8000143a360ba893bd86a6000071210000380dec0dea0a4000014090000022a2b85c0c0ea000000004852fc2174726405c285b410940000000031e9000000000000060848000000000000605ad08400000c0ab8000000000000000042054000000000000305a00001408b00000000090040000c00e1855801d7e02b0000000000001402713d1000018e54000034220000010720000a209800005058632600004849ac4780000000011cb9828e0000000000000c84200007478d0414000000000000000000001217d000078451ca1a000044063853443220000000019cb400000000f0bc8000000012379000011c7c0000a41c53d00000249b60000000000000000000000000000000000000000004063c000061491001000000000000000000000000000000000000001c4560000a79fc88db0ece000043960000141a6802fd1be0000000418d92b054d10980000e0b440d05a2074602e34c30080847c000020e41022000000000c0e0b4a3b25b00000000000002800c000000000000000000000a042000000003990fcd320085406300000000001400801203164230841080810950c080002a0820886601c00602a802201288cc58825214870282400a40705d2208081129740040004020948c1acc01b02011008388118000018800185421200320804110010900b08c6101400010210c801321c00d003 else 0x60c48000000000000493cb448c0000000000001526cc2b91390d03cad078000061cf80003033e0000000048360034800000000492080000604c000008050000000000000000008e7a0000000000000000000b72017000000000e07e0000000019812000000000000000000000000000000422a284b0090d868b81f40000e0500000000000000f0308807801600000009510e9c000000000000000000000000000005a21cc192699bc097385800000225c000000001c0500000159400001c10820f960bd8000000000000704c528ec0000e0f8d020e84b44e6ce05044c68000340b884190000000000001c48700004051400000000115680002420e00000000000000000017200000000182a2000000000000381820000b6878000000000000205b720808284000000002827c0000e58d000000000000000000000000034e4ac9150000223d40000817a20cad8e9b8259c8c1d18170de801782c15e0bbe0e4c0001403400000000000000000700240dde82500000000011a2000000000429a921480000603b000000000c224000000003827b995520e50000604964c5a000000004142980fa0000f68888ac30e3ce29d00001b0b000000cf1b190000004b180000e1b7084fb8657a689615180002c05920cc04bb000030452000086c762154000167310000000000000639100001020d52e7c2b1b31dc811ec5e3800d00000000000000000b0d280001c176ac6d0000000000000e1a620400000084e400000000305280000000000000000000008774000020aa6c23c0000000000000000000000000510a8000000000000701c800000000000008877085e0000000000000809400000000435b00000000000002a1aec1c30180009a800000000290d71938000000000000e0a99a00000000000a0b7783758f52000000000a0a40000672900000000000000000d3cf0000381cd26bc5637c86a00000000031d40000000000000b0b4d033c00010171002e921bc0001c01800004835400000000048f000000000000000000000000000000000078a54000000000000482e75818a08c0000000000000a47f00007010c000000000000000034256000000456067800000000000040e1c0000c39ce2b0e143c00018099c0aa9007c0000000004d20a1b0000000000000000000000000000007818000000000c004800000000000000000000000000000908628628000000000000602d7403a0000900b3830800000000d135303dc0000c0fd1653000008316a0d25099c81c000010d070000000034734c85310360000000000000000000001c2b60000000069e8f06a800000000700640000000000000000382800000617f2858c00000000000040d000000000060b38000000000000c0358000010ac0000000000000641800070000431a10f4200003617f) else (if j<3 then 0x2140001e3840000301e8000000000000214d040f72036f03159dd6805ae21690a080b06d8f40000000058e540000000000000000103200000508d80000000000000000000000000000094838a2980001c935908be0410000000f101a580a2c447ec339d02d80003806fa12970b6000000000216f0000000000001c1760000085940000886d216d000000001e0ad608d23208000001a9000000000000000000000000000000000000000000041366106100dfb1ae4e700000a0535026a411e0000000029cf3011a0000406b80000000000000000000000001c72f9055624c381f6000000000000350320000708cb1ced51b20000235d00001dae7ed5d00a32a167c1a98544601120e5306bde0a100000000280b20000f19b785cc00000000000000000000000000000103d80000aa2a341b80000000040e8703bc05790f3600000000000000000000000001242800000000000072300000063240065800000000c02430ad380e00001698c000000001ce75c507d39380003808be132718c0000000000078000079e64000002ca8077800000000a139e2ab6883c0000872000003044c0b00a87a30cdd88e800000000000001c900000617800003868d528c81930000483b2409c2723d1bc000000329c04b0000780fc0001c02a404e8000000000000000000002c1ac00000000002b80001c199e0d0984800001e30e000000003107000005087003a5473c06ef00000000000014c1cf09200000000000000000000000000000000000000000000000018a800000001817f903b0000000004da400000000000000000009180000000000000000000000001c7a7a07191c88000000c80161000008596a1aa00001065800000000c1cb389cdc0220000b0a900001d0d000000000000000000000000000000182d52087b37cb8404000000000000000000000212230398000000000000c12280002c60ca409000070e7400002111109eb0460831a000000000000000000000b04aa0245921f615081ba00ce382e968e03077500e942b3c134a0c700001cc48400b94c930897cf380000000000000000000000000000000000000016098000000000000e05459e76d0ce000010ae80002402681871190ea1318e72000076c02a4cbc1272328842be815cd840275700000000391de60c0211d80003821a0000508100000026c0000a69a0000050380000b120a0d4602c400000000580cc19b40000d06e1022582b1c19c108838dedd04200007685394c381ea000000005067400010066e146e02c809b2408e820900000000000000000000000001014400000363000014415d3cf80003d07400000081d02cc0000e2430000000000156000000000000181fc000000001185082380000000000000065c00006079d0c780000a05800000000040a940a74152b90f4462e0 else 0x3b3bc00000000000000000000160c60000000000000000013648000391540000369a800000000000076c68000000000000819e00000000000000000000000001e28c000078d18c28660e7000000003018a000035090000140c80000b1110000000000065000078016030a0000000001e9400000000a04300002d0120000000000000000187a6b3cd000000000000000000000000000000106d991e8000000000475f084387060000000028223184202370000128f402000000d156583100000c0ed6066ba4448f31805100000000000018052a0cd00003061923a4000000002c30640400000404e268180000c009000000001617c50a628e2c00000000100700001027823a904c700000000000007137000018210c0ea0000086600001805ee3d430156c29fc0ca0000284ec008c000090ae5028800006618000010a42812e00000000000024587603cd11500000000000006120000024636000080389843c0000000000006950e00ce0000304b4a0bc8e5661890000000015b362182305200003c69e000072a10000041c40000d007a84c400000000f198d90b00000000090c9606228158c13a00000000000000000501f00000000180ff000048))
def g503D12 (j : Nat) : Nat := 0x229030442450848a40470c1a659021a40810c39010840c12299421071498a40c52629031229010c50e29011452e29011499020c4c019b01509349a1cf060270fc662107801ffddbff3b7fd76ff8edffdc7feb8fff61ffac3ff487ffb87fd70ffec1ff583fe987fd10
def g503H12 (j : Nat) : Nat := (if j<1 then 0x823a90980da00000000000000000000000000000000020a00000000008140000000b03e0000000000000010d040000000000000000000000000000000000000000000038a0fa5ec686a6ee55b00000001a8dc000100a0000014400003225072000000000000000000000000000000000282a80000001e52790fd01830f00000000000000000000000000011a200000000000000000000000000000000000000000000000000000000000000015b1800000000000000000000000000000000000000000000180c00000002c9e00000000000088f800000000000000487900000000000615300012ddb51a983000000000000000000000000000000000000000000000000000000d84800000000000000000000000000000000000000000000000000000000000133746bd61a80000000028ce904000000000000000000104e86f200000000000005a0000c290000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000319ca4300000000c38800000000000000000000000000000000000000000000000000000000000000000007230061f2afc876ea400000cc78000000030f40000000000000000000000510f2192019400000000000000000039c100014190d19800000000000000000024ee00000000942000000000000000000000000000000612c000000000000000000242280000000000193d00000000000000000000001c2f000070230001a1d000000000000000181e80000000000000000000000000000000000000000000010730000e04c000000000014520000281500000000000000000000001c248000000020768bd0000c4a6000000000000000c03c86800000000000000018c681264d0000000000000000006f8000b0c2000000000000000000187600000001ad4c0000000000000000000000f45c0000000183c000000000000000000000000000000405fcd68000393600000003437800000000000000000000000000000000000002cd4000000000000000000000000000000000000094ec000000000000000000042b2b05000000000000000c0220000000202100010118000281900000000000000000000000000691b0000000001d80000000000106100000001406800009540000000000060430000000000000000000000000000000000e088000000000000003825000000000002d3c885000000000000281c000000020bb282c000000000508000c2c40000000000000000000000000000000000000636fd190000000000000000000000000000000a18c000000000000000000116ff0e400000000000643c0000d27800000000000000000090840000000000000012830000000018001961498140100940124024000044c0086340001082c8 else (if j<2 then 0x720000d1d0000d07c0000420000010cda24800000000000000000071840000000180b800000000000000000000000001d860000000000000000000000000008338000000000024f48000000000000004d34000000000000000f00600004de000000000001004000000000590837000000000000000085e000000015b1000006e2000000000000000000000000000000000381f800000000000000000062e2000000000000000000000010120000000000000000000000000000000000000309e800000000000000000000000000000000000018cf800028d28674000000000000000ec7c0000000904e00000000000000044fb013385d000160934dd2053000000000000000f0b00000000000000000000000202800006368000000000000000000000012c261100000000000000000000000000000000000b6e000000000000000d09a00000000000000000034910000000122d4000396e000000000000000000000000000000000000000000000000000008998000000000000000000000060c583051b9f4e2000000060700000a8d00000000000000000000000801600000005250e0d000000000000000000000000000000000000000000000000000000000000000000000000012e00000000000196a000000060ddb6a168f80001143000188480002804c23800000000000000000009a200000000a9900000000159200000000000907000000000000000000020a2000000000000000000020b5451c0000000000000000000000b01a00010e1a05700000000000000000000000000026e0001658c00000000000000051e80000001aaf0000025ab6e0000201a8000000000a800000000000000000000000001276cc36000012e1ede80000000d2720003ce0000000000000803800000000000000633080b2000000000000000000000000000000000000020860000000300b70a664c200004e112c6415200008014137000000000000000000000000000000c1350ce287580000001c0d29b2000000016cac000000000012ddc0000000b064000389c000000000000522104b0000c0800000000000000028bcf806c37e0000000000000000000000000000000000000000000000000000000000000000000333dc37c0000000000060be00000000000e2600000000281b000084160700833000000000000000000000000004854a4e000000000000908200000003a43d18f8870d6168d966b2000000068250000a1880000000000000000003a0f00000000000000000016d8400000009668000000000000000000358e0000000034d400000000666ccb800018b400000000000000000000002115984c2256000000000000172098c0000000c590e8e243580008074000000000001000000000000000000000000000000000000000000000000201400 else 0x1c4e80000000000000000004cb4609e000342d9b4fe67600000000000105200000006075000000000000000000084ec000000072ef22d800000000000000189f8000106e00000000000a0ec0000000084800000000000000000000000000211e000000000000000000000000000000000000000006809c0ee000000000000000000102e00000000000000000000000000212c8000000000000000000000000000000000000000000006814000000000000000000047a80000000a4de000000000000000e005c15f036238b886c00000000000000000000000000000000000000000095000000000001633c0000000000000000000000000000000000000425c000358d80000000000000041dc00004379c348000703c00005aa0000d47600000000000000000000000000000009880000000c58e00000000000000000000000000905c00000000871000000000000000000000000000000000000000000000000000000000000101c00010de80000000000000000000000000000000000000488800028100000000000022090000000245f8000f5))
def g503D13 (j : Nat) : Nat := 0x1251104ff
def g503H13 (j : Nat) : Nat := 0x33000000000e40000000000000e28000000000000000000000000e00000000000000000000000000000000000000000000849656000000000a32000000000000000000000000a90000f2ae02769b26000000000a4a000000c48000000000000000000000000000000000000000000000000000000000000000000000000000000a01000000000000000000000000000260000000000000534000000000000000730000000000000000000000000b0500000000d00000000000000000000000000000000000000062700000000000000000000000000000000000000000000000000000000000000000000000000000b00000000000030c000000000029000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000147000d07000000000000000000000000000000000000000000000000000035000000000000000000000000000e0400000000000000000000000000000000996a06800000000000000000000000000060300000081600000000008050850a000000000000000000000ea0000000000000000000000000000000000000000000000106000000000000000000000000000920000000000000000000c0e0000000000000000000000000005670000000000000000000000000000000000000000070
def g503L : Nat → Packing
  | 6 => (1,7,5,0,0,0,0,g503D6)
  | 7 => (18,6,5,0,0,8,0,g503D7)
  | 8 => (112,5,5,0,0,11,0,g503D8)
  | 9 => (334,4,5,0,0,13,0,g503D9)
  | 10 => (428,3,5,0,0,14,0,g503D10)
  | 11 => (123,2,5,0,0,13,0,g503D11)
  | 12 => (15,1,5,0,0,9,0,g503D12)
  | 13 => (1,0,5,0,0,0,0,g503D13)
  | _ => emptyPacking
def g503I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 11 0 9 1 4 g503H7
  | 8 => lookupWord 5 61 3 13 5 4 g503H8
  | 9 => lookupWord 36 369 5 15 7 4 g503H9
  | 10 => lookupWord 109 4399 2 17 9 4 g503H10
  | 11 => lookupWord 160 1611 5 17 9 4 g503H11
  | 12 => lookupWord 64 1299 3 15 7 4 g503H12
  | 13 => lookupWord 8 335 2 12 4 4 g503H13
  | _ => fun _ => none
def g503 : Forest := ⟨503,13,fun i => g503Y[i]?.getD (0,0),g503C,g503A,g503L,g503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P6_0 : block g503 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B6 : block g503 6 0 1=true := g503P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_0 : block g503 7 0 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B7 : block g503 7 0 18=true := g503P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_0 : block g503 8 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_5 : block g503 8 5 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_18 : block g503 8 18 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_66 : block g503 8 66 46=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B8 : block g503 8 0 112=true := (@block_merge g503 8 0 18 94 (@block_merge g503 8 0 5 13 g503P8_0 g503P8_5) (@block_merge g503 8 18 48 46 g503P8_18 g503P8_66))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_0 : block g503 9 0 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_48 : block g503 9 48 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_96 : block g503 9 96 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_100 : block g503 9 100 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_148 : block g503 9 148 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_196 : block g503 9 196 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_203 : block g503 9 203 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_251 : block g503 9 251 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_299 : block g503 9 299 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B9 : block g503 9 0 334=true := (@block_merge g503 9 0 148 186 (@block_merge g503 9 0 96 52 (@block_merge g503 9 0 48 48 g503P9_0 g503P9_48) (@block_merge g503 9 96 4 48 g503P9_96 g503P9_100)) (@block_merge g503 9 148 55 131 (@block_merge g503 9 148 48 7 g503P9_148 g503P9_196) (@block_merge g503 9 203 48 83 g503P9_203 (@block_merge g503 9 251 48 35 g503P9_251 g503P9_299))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_0 : block g503 10 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_12 : block g503 10 12 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_60 : block g503 10 60 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_108 : block g503 10 108 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_156 : block g503 10 156 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_204 : block g503 10 204 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_252 : block g503 10 252 25=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_277 : block g503 10 277 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_325 : block g503 10 325 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_373 : block g503 10 373 26=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_399 : block g503 10 399 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B10 : block g503 10 0 428=true := (@block_merge g503 10 0 204 224 (@block_merge g503 10 0 60 144 (@block_merge g503 10 0 12 48 g503P10_0 g503P10_12) (@block_merge g503 10 60 48 96 g503P10_60 (@block_merge g503 10 108 48 48 g503P10_108 g503P10_156))) (@block_merge g503 10 204 121 103 (@block_merge g503 10 204 48 73 g503P10_204 (@block_merge g503 10 252 25 48 g503P10_252 g503P10_277)) (@block_merge g503 10 325 48 55 g503P10_325 (@block_merge g503 10 373 26 29 g503P10_373 g503P10_399))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_0 : block g503 11 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_6 : block g503 11 6 46=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_52 : block g503 11 52 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_100 : block g503 11 100 23=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B11 : block g503 11 0 123=true := (@block_merge g503 11 0 52 71 (@block_merge g503 11 0 6 46 g503P11_0 g503P11_6) (@block_merge g503 11 52 48 23 g503P11_52 g503P11_100))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P12_0 : block g503 12 0 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B12 : block g503 12 0 15=true := g503P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P13_0 : block g503 13 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B13 : block g503 13 0 1=true := g503P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503T : checkedTables g503 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g503 0 0 0 = true)
  · exact (rfl : block g503 1 0 0 = true)
  · exact (rfl : block g503 2 0 0 = true)
  · exact (rfl : block g503 3 0 0 = true)
  · exact (rfl : block g503 4 0 0 = true)
  · exact (rfl : block g503 5 0 0 = true)
  · exact g503B6
  · exact g503B7
  · exact g503B8
  · exact g503B9
  · exact g503B10
  · exact g503B11
  · exact g503B12
  · exact g503B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503G : graphValid g503 (boundsBefore K494) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low503 : Lower true (varsX 503) (graphGoal 503) 14 := lower_forest (g:=g503) (i:=0) (hints:=4329571924) (before_sound K494 V494) g503G g503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K503 := extendKnown K494 14 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V503 : Known true K503 := extend_ok (m:=503) V494 low503 (by decide +kernel)
def g511Y : Array (Bits × Bits) := #[(0x25f807998601e1e6666666667fffe6006dec43,0x255003998600a0a6662222666aaaa20065e441),(0x3931981e07f99998799999fff999801a157b0c,0x3930880a02b99998788888aab999800a047b04),(0xc1c661e1f81e1e1fffe1e1879e1e0068857e30,0xc1c220a0a80a0a0aabe1e1879e1e0028017e10),(0xfe0781fe001fe01f81fe01f81fe008884de680,0x6e0781fe001fe01f81fe01f81fe000000de600),(0x7fe00001fffe001fffe001fffee059a9203,0x7fc00001f5f4001dddc0015554c059a0202),(0x7ffffffe0000001ffffffe00000f329a40c,0x777f5fd40000001777755400000f0298408),(0x7fffffffffffffe000000000000f62ec030,0x5df5f57f5f5f554000000000000d62c8020),(0xfff800000000000000000000000011fa201ac0,0x90a800006180000000000000000001fa001880),(0x1f05d20500,0x7e01d20000)]
def g511C : List ColumnInfo := [(8,0,503,0,14)]
def g511A : List (List Nat) := [[]]
def g511D14 (j : Nat) : Nat := 0x3ff
def g511L : Nat → Packing
  | 14 => (1,0,1,0,0,0,0,g511D14)
  | _ => emptyPacking
def g511I (_ _ : Nat) : Option (Nat × Nat) := none
def g511 : Forest := ⟨511,14,fun i => g511Y[i]?.getD (0,0),g511C,g511A,g511L,g511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P14_0 : block g511 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B14 : block g511 14 0 1=true := g511P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511T : checkedTables g511 14 := by
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
  · exact (rfl : block g511 13 0 0 = true)
  · exact g511B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511G : graphValid g511 (boundsBefore K503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511R : Impossible true graph 14 nineInputs.toFinset := by
  rw [show graph = targetOf g511 by decide +kernel]
  exact root_index (g:=g511) (top:=14) (i:=0) (before_sound K503 V503) g511G g511T (by decide) (by decide +kernel)
def mo511Y : Array (Bits × Bits) := #[(0x3fe001fc41180940284082,0x942a8282a82ac6d10229221cfc94a044642077),(0x7ff800000007e0002007008450104,0x4d99a9919a999243516096a7426b87a00180ff),(0x3ff8000000001f800204060601120011,0x3c879848798781c8c8e3906e83f3218a0203ed),(0x7fc00000003fc000000180800094802068,0xfc7f87c7f87f8fc7c7e78e1cc7b8acac4000f7),(0x7fc0000001fc01680820281282,0x6855054550550926e5d6cc0003284cb9081c80),(0x3ff80000000000000007e000a00300a410904,0xb266566e65662d8c8e8709588590380ed24300),(0xfc00000000000000001f800014028600128411,0xc37867b786783e0717040f9144089e24d1c012),(0x7fffffe00001e0710164805228,0x380783807803008180011e30043130293c308),(0xffffffffffff8000000000023885c09304ac40,0x403020186000380440512c3c00)]
def mo511C : List ColumnInfo := [(34,0,477,0,12),(360,6,145,0,4),(270,96,145,0,4),(137,16,358,0,8),(152,1,358,0,8),(17,0,494,0,12),(68,0,443,0,12),(171,16,324,0,4),(102,0,409,0,8),(8,0,503,0,14),(186,1,324,0,4),(300,66,145,0,4),(51,0,460,0,8),(187,0,324,0,4),(153,0,358,0,8),(364,2,145,0,4),(330,36,145,0,4),(220,1,290,0,4),(24,0,487,0,11),(42,0,469,0,10),(119,0,392,0,4),(85,0,426,0,8),(366,0,145,0,4),(78,0,433,0,7),(205,16,290,0,4),(221,0,290,0,4),(79,0,432,0,4),(108,0,403,0,7),(9,0,502,0,11)]
def mo511A : List (List Nat) := [[],[98],[81],[64],[33,101],[33,81,97],[81,98],[97,33,82],[64,98],[64,81],[64,33,101],[64,97,33,82]]
def mo511D8 (j : Nat) : Nat := 0x3279581750c76c1a326121d16d605d4325b72a12160345b9c0750c96dca848580d175605d3325b72a12160345d9c074cc96dca848580d16d605d72a1b425d21603472d82754a86d09748580d1cd605d52a1b425d2160347958174ca86d09748580c1f5605dc2a1b325d2160345d58175ca86cc9748580d1d3609d52a1b325d21603475581754a86cc9748580
def mo511D9 (j : Nat) : Nat := 0x1c203181a0c61e280be2e2808d424308d424408d46430b900c40021ed6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d59cbbda193afafa19380715f5c1b76d4a865d21e2bee836eda950cba43c67d706d9b52a1974878bbae0dbb665432e90f177741b76cca865d21e3aeb836ad9950cba43c5f5706ddb12a1974878beba0dbb625432e90f1bd5c1b66c4a865d21e3bab836ad8950cba43c7d5706cdb12a1974878fcae0d93625432e90f17e751b76c0a865d21e3dc6e368d8150cba4395ddc071db326187486afa9aee03664c30290e5f571dc06cc9860521daf2e838e4c304c0a43c57dd5325b72a1216038b7ba864b6e54242c0717774cc96dca848580e2fae8992db95090b01c5f9d0325b72a1216038bf192e036e54242c061f7761c32e5a748580c3beeab965412e90b0187ddd372ca825d216030feba2e59504ba42c061fd605cb2a09748580d2fac0b8e5412e90b0187dddb70ca825d2160353bbaee1950c3a42c0697d365c72a18148580d6f8e838e5430290b01a6f497718a86052160355eb0ee3150c0a42c069dd25dc52a18148580d5bac3b8a5430290b01a7d49770ca86052160357ab0ee1950c0a42c069f574cc969d8148580d3da543884bb0290b01b7a58271097605216034fa950e192ec0a42c06df1609c325d8148580b4fa6e34ec3b0290b018f6d82714b869d215c31eeb02e2970d3a42b863f5605c32e1a748570d2facc38e5430290ae1ade58271ca8605215c34deb30e3150c0a42b869dd661c52a18148570d7b2c138a5430290ae1a7d5d970ca8605215c34fab30e1950c0a42b86bf1609c32a18148570d7e8e83865430290ae18df8da71cb8485805c33be302e397090b00b867da609c52e12160170cfb8c0b8a5c242c02e19fd18170cb8485805c24f3ba863b60d193090d16f750c96dca848580a2eee9992db95090b0145bdd72a1b425d216028e7baa543684ba42c051e774ca86d0974858083eeee150d992e90b0145ddd72a1b325d216028ebbaa543664ba42c049f574cc969d8148580
def mo511H9 (j : Nat) : Nat := 0xd05c07000d08000000000000000000000c0100000020b50c704b4214900000000000000000020a000047000d4310600000000000000094c900802e0964b000b44000000000903024
def mo511D10 (j : Nat) : Nat := (if j<1 then 0xa7ddc32a09748580c7bda86d09748580c7bca86d09748580c7dda86cc9748580c7dca86cc9748580ab7dc52a18748580abddc32a18748580a9fccb69d8748580afd5c32a58148580adf5c72a18148580aef5c62a18148580af75c52a18148580afd5c32a18148580a7f4c969d8148580b7b5c425d8148580b7d5c325d8148580e9f5a761d8148580af75c52a1815c570afd5c32a1815c570afe5c22a1815c570c7ddc96cca848570cfd9c06cca848570a5fdc72a19848570a77dc52a19848570a7ddc32a198485708f7dc52e1a7485708fddc32e1a748570adf5c72a18148570aef5c62a18148570af75c52a18148570afd5c32a181485709df9c72e121601709f79c52e121601709fd9c32e12160170975dc52e1a164c8797cdc22e1a164c87b755c32e99564487b765c22e99564487b755c32a19564487b765c22a19564487b755c52a19364487b7c5c22a19364487b6e5c62a19264487b765c52a19264487b7c5c32a1926448796f5c62e1a2644879775c52e1a26448797d5c32e1a264487b771c52e19164087b7d1c32e19164087b7e1c22e19164087a75dc52dda326171a7cdc22dda326171a7d5c12dda326171a7d9c02dda326171e66da6695a226171e6cda668da226171e74da568da226171e755a568da126171e6e5a6689a126171e765a5689a126171e7c5a3689a126171e739a5691a026171e759a568da026171e799a468da026171e6e9a6689a026171e769a5689a026171e7a9a4689a026171e7c9a3689a026171e771a5685a026171e7b1a4685a026171e7d1a3685a026171e7e1a2685a026171d755b56cc9860571d6e5b66c89860571d765b56c89860571d7c5b36c89860571d771b56c09860571d7b1b46c09860571d7d1b36c09860571d7e1b26c09860571c57db76d4a865d21c67db66d4a865d21c5ddb76cca865d21c75db56cca865d21c5f5b76c4a865d21c6f5b66c4a865d21c775b56c4a865d21c7d5b36c4a865d21c7e5b26c4a865d21c5f9b76c0a865d21c779b56c0a865d21c7b9b46c0a865d21c7d9b36c0a865d21c7f1b16c0a865d21877dcb261a521d21a57dc7261a521d21a67dc6261a521d21a75dc3261a521d2187ddcb261a321d21a5ddc7261a321d21a75dc5261a321d21a5f5c7261a121d21a6f5c6261a121d21a775c5261a121d21a7d5c3261a121d21a5f9c7261a021d21a779c5261a021d21a7d9c3261a021d2196f5c62e197605219775c52e1976052197d5c32e19760521b5e5c72618260521b765c52618260521b7c5c32618260521a7e4ca65d8260521877dc52e1a125d8087ddc32e1a125d8087edc22e1a125d80a775c52e1a125d80a7d5c32e1a125d80a7e5c22e1a125d80877cca6d49760580a7d5c32a5815c58087ddc32e5a74858086fdc62e1a225d10877dc52e1a225d1087ddc32e1a225d10 else (if j<2 then 0xf5f5b065d8760521d7bda26d09760580d7bd826d09760580d7dda26cc9760580d7dd826cc9760580d7ddc32e5a25c580d9fccb61da25c580e7ddc32a5825c580c7fcc96dca848580cdfcc96dca848580cf7d876d4a848580cfddc76cca848580cfdd876cca848580d7ddc32e5a748580e7ddc32e5a748580d7bda86d09748580d7dda86cc9748580adfccb69d8748580e9fccb69d8748580aff5c72a18148580ebf5872a18148580e7f4a825d8148580ebf4ca61d8148580f7e4976098148580fbe5876098148580cf7d826d4a85c570cfdd826cca85c570cfedc66c8a85c570cfed866c8a85c570aff5c22a1815c570cf7d876d4a848570cfddc76cca848570cfdd876cca848570cdfdc72e1a748570cf7dc52e1a748570cfddc32e1a748570cff5c12e1a748570adfccb69d8748570aff5c72a18148570e7f4a86618148570aff4cb69d8148570aff4c869d8148570edf58769d8148570efe4a86098148570f7e5986098148570efe5a76098148570dff0b86052160170ffe1826052160170a7ddc86dda326171c7ddb26c1a326171d75db56cc9861d71d5ddc76cc9861d71d6edb66c89861d71d76db56c89861d71d7cdb36c89861d71d775b56c49861d71d7d5b36c49861d71d7e5b26c49861d71d779b56c09861d71d7b9b46c09861d71d7d9b36c09861d71d7e9b26c09861d71d7d5c76cc9860571d7d5c06cc9860571d775b56c09860571d7d5b36c09860571d7e5b26c09860571d7f1b46c09860571b775c52618760571b7d5c32618760571b7e5c22618760571a7ddc86dda326121a7ddc86c1a326121a7dcc76c1a326121c7ddb76c1a326121c77db76d4a865d21c7ddb76cca865d21c7ddc76cca865d21c7ddc06cca865d21c7f5b76c4a865d21c5fdb76c0a865d21c77db56c0a865d21c7ddb36c0a865d21c7f9b76c0a865d21c7f9b46c0a865d21d5ddc76cc9861d21977dc52e19761d2197ddc32e19761d21a77dc7261a521d21a7ddc7261a321d21a7f5c7261a121d21a5fdc7261a021d21a77dc5261a021d21a7ddc3261a021d21a7f9c7261a021d21d5f5c06dc9860521d7d5c76cc9860521d7d5c06cc9860521b6f5c62618760521b775c52618760521b7d5c32618760521a7f4ca65d8760521b5f4cb65d8760521b7e5c72618260521c7ddc86cca95c580c7ddc26cca95c580c7ddb36c8a95c580a7ddc32a5a85c580b5ddc32a5875c58097ddc32e5a25c580a7ddc32a5a25c580a7ddc32a5825c580b7d5c32a5815c580e7d5c32a5815c580af75c52a1815c580afd5c32a1815c580afe5c22a1815c580c5fcc96dca848580cdf9c06dca848580cfd9c06cca84858097ddc32e5a748580a7ddc32e5a748580c7ddc32e5a7485808f7dc52e1a7485808fddc32e1a74858087fdcb2a09748580a5fdc72a09748580a77dc52a09748580 else 0xba40700836034401c021380510070084e034401c02106418c020c640082c20011f0630081a1ae5c20640ca428fe50084691a3f940210a4b94020ee90082c93230083493650083007e9009e58205821e50083223650083044020888f94020fe5020020e0402c0101c4210010b6601c84004400407080b0048401c40080a0be98a001f140214c40082110010bc5e83a60044417440082510020944004022a1431745004022a1441745004022a3431745004022a14317a0e9a430da602a436a04f14a8d103f14a85103f14a891030a0c400830a3c50083c80c4004330f20e983c83c50043f14070283714028a0c413522a1440f522a3440d522a1440fc5683a6d0f4417c5e83a650d441401fa402f1428140100bc50a04e14021a3841385008686104008070b83008260c02098001c020f8001c020fe50082290a30083290020aa40082491230083c8c0209230082603e50083e03e50083023e50083d1811008301c010807008202f200048413a0e98011104c0c0209030082bbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbcbbc0900aa090b9809009009009009009009009009009029a7ce29a29a29a29ab6ab3cb0eaeaad0a8ea6aa0ea3c1e01c6a0e9ea1ac1c61c61c69d09ac18815415415498816e15415495092c92c9089089088ee8ca8a68780aa0aa81681685e0aa8308167e87ce7ce7ce79645277c76276272a7106f66be68664e6165f25c45f25c45a057c5585345105105105104ec4c84c84a448048048045245242e40a3e63ae37633e33e33e3102b42e22b409009029a09009009009009009009009028028026609009009009009009009009009009009009009009009009009009009009009009009009009024221e24221e24221e21e21e2042042042042042042042042041c61ac1e01c61ac16e18816e15415418816e18816e16e15418816e15410c13010c0e80e80e80c40900900900aa0aa0aa09006203401a01a000cefd706d8a864971cf7d706d4a864971cfdd706cca864971cdfdb02e98764971e5fcc86c1a726121e7ddc86dda326121e7ddc06dda326121cf7d706d4a865d21cfdd706cca865d21d77d706d4a865d21d7dd706cca865d21e5fdc06dca865d21d77da06d49861d21d7ddc76cc9861d21d7ddc06cc9861d21d7dda06cc9861d21d5fdc02e99761d21b5fcca65da061d21e5fcca65da061d21d7f5c06dc9860521d7f5b02e58760521b7f4cb65d8760521))
def mo511H10 (j : Nat) : Nat := (if j<1 then 0xc008202400000000000000390ad00a000000000003034337a00000000037000000001098000000000000000000000000000000000000000000000000000000010d4f8350000000000000000000000300b00000000000201d0000000000000000000000000000000000000000000000000f0580000000000000000000000000000000000000000000000001c060000a006000000000000000000000000000000000000000000000000000000000000000000051b7a04880578d08000000000000000000000000000000000305e00000000000705400000000000000168bc00000000000005c000000000000000000481f442200000000000000000000000000000000000000000000000000000000601e0000000000000000000000000000000000000000000000003d0280000000000000068270001a8300000000000000000000000000000000000000000000000000000507a0002c030000d33000000000000000120340000000000000000000000d4140000000401d0000000000000000000000000078310000000000000000000000000000000000000001100000000000000000000000000000000000000000390080006061603800000000000000000000000000000000000000000000000000000000000091600000000000280100000000269400000000000000000000000000000000031990000000000000000000000000000000000000000000000001a66c0000000407600035130000000000000000000000000000000000207800000000000000000000000000000000000000000342f20b54df0000000000000000000c43e000000000000000000000000000000000000000000000000111980000001283c0000000000000000005832000000000000000000000000000000000000000000227f03000000001194938400000000000000000004e280000001e00000000000000a6e800000000000000000031930000609b1068000000180b80003d1a000000000000000b43a000000000000001c6fc0000000000000018e180000001e0ac0000000000066480000000344400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004019000000000000000000000000000000a390000000020120000000281c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000041910000808dc1f0000000000000000000000000000000000000000000000000000000000000000a0518643c2080000000000000038440000000000000000001e7000100000000000014038000000000000000000000000000000000b0840000000000000000000c228000000000000000000408c010840040 else 0xd011e0a4000000000002861c09e8360000000000000000000000210d0000546c00005000000000000000000000f07e000000000000000e10c000000000000000c1c80000000000000000008382000000000000000071000000000001e11c0000a2b000000000000000000000000000000f38c00000000000904200000000000000000000000000000000000005848000000000000000000000000000000b02800000000000a03400000000000000000000000000000000028cab2120000000311c0000000000000000000000000000000000000000000000000000000000000000103cc65c00000000000000000049c7d02000000000000000000000000000000000000000000008000028cb0000000000018028000c450000000000000000802c0000000000000000000000000000009100000000128b4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000408800000000000c198000000000000000000000000014008000000000000006025647200000000000108c000000000000000000000000006370000000000000000000000041a30000000200d800000000000000000000000000000000000000000000000000000)
def mo511D11 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x69d815c76fa54b0ec0ae37dd6d48760571bfab6643b02b8dfe5b221d815c6ff8d810ec0ae35fd2e5a2605719fe974c9302b8d7f4b9609815c73fa54b04c0ae35df6d49864171afbb664c320b8d7edb2261905c72fed834e4c2439f76dda326121cfbb60d193090cf7db52a1974867eed9950cba433fe6c0a865d218ff974cc32e90d77db52a197486beed9950cba435fe6c0a865d21cbfb6e5432e90e77db52a1974873eed9950cba439fd6c4a865d21cff3605432e90d77db526187486beed9930c3a431ff6e99761d21abf974cbb0e90c7fdba26087486afedb93043a435df6d49821d21afbb664c10e90e77da96948748773ed334a43a439df6e5a521d21cef972d290e90e77d98694874873be4c34a43a439df65da521d21dedb64d290e90e7dda968c874877aed2b4643a439f76e5a321d21cfbb30d190e90e7dc9868c874873eecbb4643a43bbd699a121d21deeb4ad090e90efd5a3684874877f2d134243a439fd661a121d21cfe930d090e90e7f597684874873fcd4b4043a43bde695a021d21df7348d010e90efd9a3680874877f8d0b4043a439fe661a021d21cff130d010e90e7f99768087486bfadb930c0a433fd2e99760521afe974cbb0290e7f4ba65d81486bfa5c32ec0a43d7d65d8760521afeb7243b0290def5b621d81486fbada90ec0a437f56cc8760521bfcb6443b0290dff1b021d81487bf24c304c0a43df965d82605218ff970d092ec067f5b8684976033fa5c3424bb019fd6d5a125d80cfeb64d092ec0577db525d81602bdeda12ec0b015f76cc9760580afdb644bb02c057f5b125d81602beed9952b8b019f76cca95c5808ffb6454ae2c04f7db52a1716027eed9950b8b013fb6c8a85c580cfe952c0ae2c079f587605716027eed995290b0137f6dca8485809efb6a54242c04fddb32a1216023fe5cb4e90b011ff6e89748580aefb6a4ba42c057bdb425d21602beed992e90b015fd6c49748580d3fb4ec3a42c04f7db52a1715c27eed9950b8ae13fb6c8a85c5709bfb6e54242b84f7db52a1215c27eed995090ae11ff6e89848570afeb624c242b867f8a9605805c33fc54a42c02e11ff6c8a865d108ff970d112e8847fcba65d824423fedd12ec12215fb6c897609109dfb6c542e4884f7db52a1724427eed9950b92213fd6c4a85c9108ffb744c2e48855fdb726172442bf6d9130b92217dd6d4a85c510bfab66542e2885fe5b22a1714433aed2b464c2e39bb699a226171cedb4ad1130b8e7cda3688985c73bad2b424c2e39f568da126171cfcb44d0930b8e779a5680985c73dcd23404c2e39f668da026171cfd344d0130b8d775b5261815c6bead9930c0ae35f96c898605718efb6a5432e90c7ddb32a197486afadb930c0a435bd6d89860521aeeb6a4c30290d7d5b3261814863fa5d32ec0a431f76cca95c580 else (if j<2 then 0x1bfd2a58148580dfe950c0a42c06ff5a760521603bfa4bb0290b01efd61d8148580ffcb04c0a42c04ffdb22a1715c37fa54302b8ae1f7d61d815c5709ffb6e54242b867fda8661215c33fe5433090ae13ff2e1a7485709ffb74c3a42b86dfda761d215c37fa5430290ae1dfd6618148570dfeb4ec0a42b87fe582605215c2ffcdc242c02e17fe2e12160170ffe30290b00b867fdb269c984433fed93504ba215ff6c8a961d10affb644c30e8867fca968987442bfedb930c12215ff6e09760910ebf972c3ae48857ddb86859321ebee5c342c990f7dd6d4a864487bfab665432243dfe5b22a19121fbbadd32ac890fddd2e99564487eee950cab2243f7d4a864d9121fbead2b26c890fddd655a264487efab26d132243f7e5ba6499121fbf25d324c890fdf92a19264487efcb6ac932243f7e5a56499121ebfa5c344c890fdfc2e19164087efe36ac8b2043f7f1b26459021f7bad8b4a43b03bd7695a321d81dfab62d190ec0eeeda6688876077b6d2b4443b03bf368da221d81dfcb62d110ec0ef75a5684876077ead1b4243b03bf9689a121d81def34ad010ec0efb9a4680876077ecd1b4043b03bfa689a021d81dfe342d010ec0e77d98694985c77aed2b464c2e39f7661a326171dfab62d1930b8eeeda6688985c77b6d2b444c2e3bf368da226171cfdb30d1130b8ef75a5684985c77ead1b424c2e3bf9689a126171def34ad0130b8efb9a4680985c77ecd1b404c2e3bfa689a026171cff330d0130b8e77db2694985c73bed834a4c2e3dd7695a326171cfbb6ed1930b8e7dcb768c985c73eed93464c2e39f76c1a326171cefb4ad1130b8e7dda3688985c73f6d33444c2e3dbb699a226171eedb4ad1130b8f7cda3688985c73f6dbb444c2e39fb2dda226171cfdb6cd1130b8e7edb0688985c7bbad2b424c2e3df568da126171cfeb44d0930b8f7e5a2684985c73bed2b404c2e39f768da026171cfdb44d0130b8f779a5680985c73fcd23404c2e3dee691a026171efb346d0130b8e7f9a2680985c7bf4d13404c2e3dfc685a026171aefb6a4c30eb8d7ddb3261875c6bf6d9130c3ae375f6d49861d71bbbb664c30eb8ddedb2261875c6efcd8130c3ae39df661a521d71dafb0ed290eb8e7dd9868c875c76eec3b4643ae39fb661a221d71dbdb0ed110eb8e7f998680875c76fcc3b4043ae33bf6d8a8649719efb6a54324b8cfddb32a1925c6b7edb130c92e35df6d49864971afbb664c324b8d7f9b0261925c73f6d9152c12e35bf6d89860971aefb6a4c304b8d7ddb3261825c6bfcd8130c12e33fb2e99260971adfb6c4c2e4b8d77db5261725c6beed9930b92e39fd6c8a960571beeb6a4c302b8dfd5b3261815c6ff2d9130c0ae37fc6c09860571eeeb6a4c302b8f7d5b3261815c6bfad9130c0ae3df96c89860571efe3604c302b8e7f4a9 else 0x60c3b24b8fdfdb061d825c7bfe5d32ec3a43bff6a5a061d21effb52d030e90f7fca968187487bfecc340c3a43dff261a061d21fbfb2ed030e90fff5b061d814877fe5d30ec8243eff6c9a161d80f7fb44d0b0ec07bfdb261d81603bfe4bb44c0b01eff61da260580eff92ec1302c07bfd8760981603bfed412e90b01bff6e98748580dff974c3a42c06ffda861d21603dfed430e90b01bff2a18748580f7fb74c3a42c07ff587605216037fed1342c3ae1dff661a260570dffb4ed1302b877fd98609815c37fed9350b8ae1f7f6c9875c570bff970d12e2b86ffda8689715c3efec3b44b8ae17ff6e9825c570dffb74c12e2b86ffcba609715c37fed4304b8ae1bff2a1825c570fbfb0ec12e2b87feda2609715c3ffad9302b8ae1ffd689815c570ffeb04c0ae2b86ffdb76a1215c3bfed433090ae17ff2e1a748570dffb50d3a42b86ffdb869d215c37fe5c34e90ae17ff6e98748570dffb74c3a42b86ffcba61d215c37fed430e90ae1bff2a18748570fbfb4ec3a42b87ff5b7605215c3ffad3b0290ae1ffd61d8148570fff364c0b00b87ff982605805c3ffcdc242c02e1dff2a5a261d10eff972c3b048877ddb161d9321fbfadd30ec890fdfd2e98764487efeb6ac3b2243f7f5b261d9121fbfac3b4ac890fdfd61da264487eff362c3b2043ef7d87694876077eec3b4643b03bfb61da221d81dff30ed010ec0d7fdb025d926073fe53b24c83039ff689a026171befb6a4c30eb8dfddb3261875c6ff6d9130c3ae3ddf6d49861d71efbb664c30eb8d7fdb2261875c7bf6d9130c3ae3dfd6c49861d71eff3604c30eb8edfcba61d925c73fe54b0ec12e3dfd6c09860571efe952c3b02b8f7f49861d815c7efa53b0ec0ae3f7d6c18760571dbf974c3b20b8e7fda729d98486bfed814ecc2435ff2dda066121cffb60d393090e7fdb72a1974873fed8150cba435ff2e99761d21affb70cbb0e90d7fcb865d87487afe5d32ec3a439ff6a5a061d21cff952d030e90f5fd9768187486bfedb93043a439ff6a58721d21defb0ed290e90efdd8768c874877fac3b4243a439ff661a021d21cff930d010e90eff98768087486ffad814ec0a43dfd2e58760521efe930c3b0290f7f59761d81486ffad810ec0a43ff961d8260521bfe96ed030290cffdb72a1904867fedc14ec82439ff660a764121dfe94ec0b2090e7fdb22a5716033fe54b50b8b013ff6c8a85c580ebf952c3ae2c079fdb261d71602bfe5cb44b8b019ff2a5a25c580f3fb0ed12e2c067fca960971603cfec3b04b8b01dfd2a5815c580dfe950c0ae2c07df587605716027fedb95090b015ff2e5a748580cff972d3a42c04ffcb869d216033fed412e90b019ff2a097485809ffb74c3a42c06bfda861d216035fe5430e90b01b7f69d8748580d7fb74c3a42c06bfcba61d21603cfed3b0e90b)) else (if j<4 then 0x987c5140c430104430085604180434180820a8220602100e020810430086a6218043c2004242004201e100219300214100217140210298001038085057000207010b44200040e021489400081c042d128001038085605100207010bc0220040e021781440081c042fa7ca80008085f2e00020213d3e5c0004042b038de9f28040437038de5008085f4807ca02040a01f28081020638c01088085f368008071260498126049812604981260498126049812604981260498126049812604981260498126049812604981260498126049812604981260498126049812604981260498126049812604981260498126049812604981260498126049812604981260498126049812604981260498126049812604981260498126049812604957e5e3595a5c25eee5a1960255f94d650b942e50b93864b7927c78c1e3078c4aa12c991d53e0912e42a8fdd03e8f5a38b8eb238b8d863408ca22fe8b522aa8a02256886a1e786ae181851611b837cbeb8252094825209482d60b5825206a81260287fb09097ee5f8f7d59f567db9f5640f878c7cf9f1d7ba83ba40f9ec97a7de6c1e31e4b78a9e12432d0cb7759d9a7555d2b7291cef7339ca4720dc5970e1c176fb5bb16df9b4b6c85af76b35aa369c1a3467999aa65b993263fd8c3621d854603d7dc40f97bb0da579a5de50565d6173721cd70410b042c10b16e35ae56b959dd65611b846e3fd96a159dcff6595961a57e55d83fd8ba954a952a552d52a552d5ae563556c55b152a552d54b552d52a542503e54254e840f903e40f94c740f903e40f903e40f903e40f94a65214ba94aa145b50e90e31d292ea4ba94224f814014f813c810b139e4e18ba92e212ea4d953234d113234aa130b4b252c94ba92c94aa126c48c11f447291a0468117f457913d44710fb44710fb44710fb3558d5635590e3438d0e3432c42c428507741dd05640f9026409900e3fd8fcc3e88fa23e04f603cfc9f33cfcf3f3c78efd3b70ebb3aecebb3aece9a39e4e583900e403900e0d3768da73618d8635b8b013558d5634f8d263498d2633f0ce431bccba3264c6f30f0c1b300cbeb2c04b012f28ba92d54b1929e8b882c04b012c04ace2a48a7a2c04b012c04b012d54b1929e8b012c04b012c04b012b38a9229e8a4728749f3276c9b1261c90924cc95d242493324248e822f889421cc840207c80712fc7e61f987c51e9078c1d883691d2874a1d287201bb46cc1a6466f18f05df129c4bf1848612129c5df16d45b5162c54f144c4d712fc4a7121846e0da444410b040b0fa83d20f483ba0e643690e043690d443510d4431e0bac31e0bac2b80a14252087c1ec07b01b9061815c04a40ed02e8087021c087017402a0003bfec9322c830fdff6c99164187dffb44d030ec0effcba61d90607efed1340c3ae3bff2e98764971fbfb else (if j<5 then 0x39900425980ea30089440105840380802230008830109c04200830201d11e5008b800101c3c05100e021300430106e507e0088222002070cc6160b8c07320084e301cc6011004e58419045228fca0210220a5200840149247e5f49206019224923008a04019224923010c2411f9402259403c0e3122483594052464096500f038c48120cc603c9004200846010f01c631840444794041d9700020f00083218fca0119cb80a3004042e038c630088070085030a0042010282018040e1b9807a0e28045e2804141d980e840089c5d0599080b144002050720e28043143102088285003a20086a280b41a600d0c65302a8a01012a286380c5001a208a05300f8b44540c28e28043e2e834d44138aa8a207c5541100220a188020e41c5010611903100223140401906998630078b20d3310500c814dc5010bc50139814271440070509c5424810627158828618945016834d441540a601d4a88a81823c503e834c28a1d108e2e834c28a250c6e2e834c282210c61000405e9e28a066280a41a6620bc508e9a40c4618de90080b8b20530d8501582cd84170a603300c0584340f8501182cd8415cd03008602820043b3210021e98860b0f4c040086041980c04071440070106041040c0420080e101141030108a0038083501980604c180863040c0419800e020d81469180442008c021d0046010f80230086c011804329834021da40e010da60d0086c0820043a0034041da40202038869038083068082600080e1f0004070d9c0108cc07f28084620042a00080e191004070e880203860f038401038083e001c041b000e020d81e9c20040e021b80e9420040e021b81e9c20040e0219800a038044e00280e01138004008640818043a000c021b0206010f800300860d0084440084a60179402269805e50089a6220043038042c70042470042818082f2a000e0113cb80038044c0110021a000e020f0007010700218043c000c021a0086010f00430086030c8043c001c021d9906010f4a0108c802f4b96102da42e02f2c2050b99004e5840a01f28083120082f28042120042f280820c047ca021148020804e9f292040dcb802180bcbe92408030401146021548a30107a30104a30105409700832001c041d000e020c80c600c8c0429018c030248c04308c0413018c01918085603180604918086118042047a7ca01010a080084404260005e50088190085800479404260011e5008880c318c0226010c63008980c318c022023ca020f0146f2804404012060210c1030086600200c020714c0070087030085e6d010c3d010c021a8086010c02070b8a04f301c407828205c800284138a0b900050828a02c440d8802f4f14502fa78bc41408e96200b8a281741a6d410c4e2e834c01220bc501798142715cc070508c46180bd3c5140dc40170fd3c5140ce9620 else 0x141030086a08180839001c04180906010dc1030087400088c04270002230109a60)))
def mo511H11 (j : Nat) : Nat := (if j<1 then 0x120af00000000000000000c02b8000301b2c015000000000000000000000483d4000106e2000000000515c0000000000000000000000431d81840000a063716490345113e8818b02d80002d03ea112f31e800000000000000000000310520000000000000000008a000000807c0000006e000000003c0e0000000007890fc5fa00000000702e40000c038d3340000000018092e04580003810e0000f028621bc0001004e635fd0368000146c300000039640f9a8db207500003ccda00000000000000001c08a706b80001419a0000a07cd83f0000061060000583ff44a60000b065b006b40cbe04ce370918eb8171e051a41070970ce0e2674748098164c57a42910000583900000a02a702f8000000000000000000000000000000000200868146e6eb00000000000014037000000000000000000000000038d84e089d033680a40001a02cc02680003418288d75007000000e08666cc01100000000040a150698000000000000000000001505720ca000031af1c1000000000070b18000000000000089570d462013b40a283c7405c0000000000001d14e20bfa0388000000000000702c0000000000000d02ee00900001890200006829c00000000844f000000001e099f08a80001903a0000501680003c0ec8209403f11b4b0cf4000000005039f003ac01e0000108d181fd60cca03d80002406000000000000000001c0de2008181dc00000000000000003019140f70000000000000000000002837c00000000d06a80000000000000000281a4000000000000323740000000000000000000000000d38900001847600000000298c8000020b0000008b948022000000000993c80160000604800000000100b50000000000000000000006000c000000000000680bc00000000000021ab580b520b3000000001905400e00000000010cc8a8210000782200000000000000000280f00000000000002407e60d60000000030d1882cef14ad9c18000086ae000019bfc0000670d046c08ae6416880401389800004517403e00003842dc00e0000f355c0126cdea000000000000141c60000000000000000000000000281f40db7610000000000000000000000000002c1d8670e0000000020085e296b30a00002403226ce0000384328137e6d4138a7a2760db9e875307c2027680e6000010295a0334da68075d138680f000000000b02581a2c00000000000000003c17760ce000000001416e00000000000000001003df04680003446e00000000321c800000000b00300000000000000033f89360dba0000a43461be4000080bc000038b8fd0cc0000404d50258000120ee0000000000000000010317a190000162ca105951259461411327103011712601031031053a3300001200301202433b514177371130d235101101110302b02350041004c2 else (if j<2 then 0x5b11890000000006030180580ced46d70000000000001c6a0d00c00000c1da0000b37381997400320a4000000000000106b500000000000000000000000000c0240000000000001c08e80e200000000000000000e372788bd001f26c0000000000000062f800000000000000666000000000000180e90000300500000c081b46ce9abc0001c04a000000002c5fe0000000008173d14a60c0b3520a344c1e60000c0558000041594861c13f2226b020400000000518ec000148b4b40f72058411e2091000070bf8000000002018c02780000000000000000000000000000000002c0da000050230000284840000b33c721c34064000000003999d4e1e0000017100000000000000000000000000000000000000281c20000135f000008e2bc108f11e5815b81e80000147500000000020a600000000000000000000000000000148ffa11ed04144dbc00000000688180000a2e60000698e30dd9e0930000000020dbf4702000000003421f481af056800000daa0000404a00003c0d80000b42f8817a008a0000b339a99d40001a0f2e0227033d8e060000000000002410480a2e45180000013007090000583e8000060fb0000681040000a6bdd16a81a3400000000b000782b800000000b088f803401b00000000000002501c0000000000003ce0266e0000020324000160080000020260e0a207fb44051bb800000000131b883db81a40000636b31a8b017c000000004a1c40000000000004892c00000000d454e010c0001a884800e7827000000000d341d1c2c0001c8990000618964019e074e43b48b0a8c2b60230000000000000a0eb0000688cc000000000000319e78cde0000000000000000000000000000000000487700005809c5020e0c7d342000020040000000000000180e5470c10020000000000000c46a802f540d1c10a00000000000000000000000000820e000000006031000000000000060441412a000003180000000c9e0b11409580a300abc0fd0000583bf0c9ce0c5d005000000000000000005438c000000000000580d80000a6ed0000000000001e10d101a80000000000000000180ad0cc5a11300000000000000000934f583180001407a000000000000000008123000000000000000000000301b648d60000399ac0001025a000071ba40000000000000000000000000c38500002412e862f00007843b42290104417d8000101b94054537980002c1a80000000001937811c2009e12b0000000014900837341ab2c10a0000a476780d18d42000000354805c0000000000000000000000000f03580003cd63664000004a26e0db000009439a984c4c7c0000406ee80140000000000002009800000000000000000000000000000689bc84d80000000060120c07740ba037a000028118000000000000181e18827000000000 else 0x2061a027c0000c0d0000000000d032000000000a2c2c1500000000079b65404a0000b041f80e401414621912c000000001c82e0000000000000000000004198c00000000e330ea0928074c290403c889f30cd3806fe43d000000000000000007040cc5f84622c027800000001c6c56074203980000666eb0548000000000000000058210000000000000000024004000080848000044a840aa00000000140a6e2710000303098164a01bd36d202940000a086232480001c20266e500000000000014033a))
def mo511D12 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x6ffda960971dff6a5825c6ffca960971dff2a5825c77fd9860971dff261825c7dfd8760971ffb649825c77fd985c971dff261725c7dfd875c971ffd2a5815c7ff49860571ffd69d815c7ff4a760571ffd61d815c7ff48760571ffd689815c7ff59260571ffd609815c7ff57260571ffd681815c6ffca864171dff661905c77fc9864171f7f61d905c77fd9264171ffd605905c6ffca766121dff69d984877fca766121dff68198486ffca865d21dff661974877fda865d21dff2a1974877fda065d21bff6a5874877fda961d21dff2a5874877fd9861d21dff261874877fd9761d21f7f65d87486ffda921d21dff6a4874877fd9821d21dff260874877fd9721d21fdf69487487fdda321d21ffd68487486ffda021d21ffe68087487ff5a760521ffd29d81487ff59760521ffd61d81487ff48760521ffd68181486ffca864121dff66190486ffca764121dff65d90487ff58164121eff685876037fc9760580eff61d816037fca95c580bff6a171602ffca85c580f7f61d71603ff5815c580dff6a521602ffca948580bff6a121602ffca848580bff69d216037fc9748580eff61d21603ff58148580ffe681216037fda960570dff2a5815c37fd9860570dff261815c2ffda85c570bff2a1715c3dfd875c570ffd605715c37fda948570bff6a1215c2ffca848570dff661215c37fc9848570bff69d215c3ff58148570ffe605805c3ff92160170dff2a5874437fc9861d10dff6a5824437fca960910dff661824437fc9860910dff65d824437fc9760910dff2a572442ffda85c910bff2a1724437fc985c910f7f61d72443fed825c910ffd6a171443ff4a85c510ffd68971443ff5825c510ffe609804437dd8764c87df76859321f7dd9364487dfd6559121f7f59264487dfd61d9121f7f5a564487dfd6899121f7f99164087dfe61d9021e7fda225d81bdf69487606fdda321d81bfb68887606ff9a021d81bdf694985c6fdda326171bfb688985c6ff9a026171ddf694985c77dda3261719ff688985c77eda226171dfd684985c77f9a026171bdf694875c6fdda321d71bfb688875c6ff9a021d719ff2a5825c6ff4a960571dfd2a5815c77f49860571f7d61d815c67fda7261219ff2a1974867fda825d219ff6a5874875fd9761d219ff6a487486f7da521d21bf768c87486ff5a121d21bfe680874877f49860521dfd65d81487fe582605219ff684976027fca95c580e7f61d716027fda1261709ff69c984427fda2261109ff2a1974427fda825d109ff688974427fca864910f7d61d714437759564487df564d9121f7e59264487dee6519021f7d99364087dfc6459021e77da5261719f768c985c67eda2261719fe680985c67f4a96057197f69c9848677da5261219f768c984867f9a0261219ef690976027dda325d809fd684976027f8a960170 else 0x102010260e6030f83980c3b96a688b8b265ab83a47cb7c2dbab632d66b4e2d0ab392cb6b1e2c42b012bdeaee2b92ad92b26ac22ae2aab2a86a942a22a7d29cea6e2992a5b1284a49a8f8a32a8caa21283ea0427ea9ed27669d0270a9b926b69a2265a98d260697a25c2969258e95624e694ea50c932247c939a47c932249a91f245690823f28f323968dc23428c522e68ac2292893a26c893a22087ea1cc867a150846a0ec82da09881ea05c8099ff87f29fa47df9f487cc9f0c7b79ea079c9e547899df076e9d9c7599d407429cc47299c787169c2c7019be86ee9b9c6ca9b6e6d61b2a5d79af46b19a906969a3468399e067299a414c196e64a18e2627187e618183a60317d65f0175e5d797a25dd175e5ca17025b9169e59e164a58515ee57415b2563156654c150a53714ae520143a50712844ff93c04de93544c792f04a89284497924048691fc4739198458912c44390b8418902c4058fe83e68f743d18f283c08eb63b70eb63a20e6238d0e1e37e0dca36b0d8e35c0d523490d0e33a0cc20000c9431b8c483088bfc2ed8b782d480002c90ae62aa0a6a28b09e6268095a24d08ee22c086220707ce1e207621c5873c1c586d01aa866c18f8600174858415b853013e84b411d844010083c40e383580c882f40b382ce0aa028a097023608601f2071019606001620510000000001e04780f803480b4025807801e005200f0000000001e0003ffda264587fff6499161fffda064587fff6459061fffda161c87fff65c97607ffc9761d81fff68987607ffda061d81fff61c87607ffd8764981fff61d82607ffd8764181fff261875c7ffda261d71fff61d925c7ffd8760971fff61d725c7ffda961d21fff66187487ffd9761d21fff68187487ffd8721d21fff61d90487ffda161d80fff69d81603ffd8760580fff68981603ffd8260580fff6a171603ffda25c580fff60971603ffda848580fff69d21603ffd8748580fff685875c3ffda760570fff61d815c3ffda260570fff609815c3ffda85c570fff689715c3ffd825c570fff6a1215c3ffda748570fff61d215c3ffda261d10fff61d824437fd9264587dff6459061f7fd9264487dff61d9121f7fda264487ffd2a19121fff5a564487ffd6899121f7fd9725d81bff68897607ff5a125d81bff68097607f7da521d81ff768c87606ffda221d81ffb68887607ff5a121d81bff68087607ff9a021d81bff29d926077fd9764981dff25d926077fc9760981bff29d906077fd9764181dff649906077fda266171dff681985c77fd9826171fdf694985c7fdda326171bff688985c7feda226171ffd684985c7ff9a026171dff688985c77fda026171dff261875c7dfc9861d71f7f689875c7dfda061d71dff660875c7dfd8721d71bff688875c6ffca864971dff661925c77fc9864971f7f61d925c) else (if j<3 then 0x6040308e50119a69823940454443080d01170023940440308e501102d2698239404607010a980b940448353a6e5011699110c082394047a6c001e50b149b94043a603088e0116100c13020c046c00403a6e5011a01380434443e580070119a60138044100b018002431b940c2fa512010c0488043010d990e039404580e5010e01990f9404503804e011201100430ca5030401154e940430ca5c004011694042a54003840115a703182394046c0c604630217031810219404624230801e502188c23940446908e50110908c2394045650108a52394044040203e5e94818100f031b97a4040884046020403e5e948239423a70318908c04848e5010c048c083c0c62302110118068c08540460304a302188c042c623020f031890048c5230209a60318239404680c66310102394043080280c6e9e50b102202198c04480c60865011454302006940862308a50110948c5032524010c542294044c5e66084100409179a810c6c5e6a044102c100c041c5c515a00f841480100c3c2850b0ac501e60fa00420803e1030328440fa6829b10071408720260403e9c5c428229a803d104a80145a0a6431aa3168299105080102e9c420a6c51024211004352a0440112810c08352e6a04412810c043c584e6a083171480139a0c286c50704e6a0031b141e1398820c64544010c10040c0b13a716829b0ca2026c40302c304e9c52828214a829aa110643020b151282990c52801c402e9c520c3a62617998210485606668841798113030102044c12980930044a60844011298200b1404545a64401111406990d3050401083022100440c08038401143010043a604010c9a1004313c5010f14000e10045c5010a159a100446608840112a59980080c5a6a00203119880080c420026603108283980c4e90166038420070223a6821198060c0876660020310219b00080c5e9c624400123021da7180493008c087e9460124c023021fa7180493008c0870b0ae5e9e6400701202c29a7979b001c0480b660ae9e5c00701239b00041040ae9e5e601400207202b97980700081c708040301e9e5c0660224299ba7940700081c8e90401e6034440020727a410079913001c088c6400103111b00040c4c6c00103102ba4100f02981c088e680010313a7980512010c087e9e580010214100c2fa796000470403e9e508141303180fa7942004089080308100fa7031b9404708e9c0c6e5011ba703189020048c088e94024c60123021c930318048c086e9012440c623021fa4930318048c0870001e9e502081843a71a0394046e9e58046010218302180040c5c5e6a004102180080c4e6040c0c0613a598305c0080204139b000c366c001031302982008105c50b80010417980c2a0e6030e81980c3e5e9e64011a7979b00466e9e5c0139b00103e680030fa7942031769e508 else 0x66e9a0e50115a59681100456083010f008c083696683e5c00119a5979b00905c0012302129997000408565c0a6010214330090044400403010715980e120f0394047c0084407e5011a9b01110c2f94047c0a6030111a79520044a548020110908f95200456965c848c0c6241c088c04314882401102c0717998210645a044011314040b9a8110666a001c5021683159804085a003010a12100420a66840b10a314080448828c501a8a0a64423179982120c5c5e644a0431710070c0ba59b16808c401c302e9c5a0662280a316101c5c566840713141e119a820c6a0a602c44301e9c528271510a10c4c52844a0a64319319a100448c4ca644011683a59b94045a9a5e660841681980c084880102a00314060c0832004830210801c0838302082c400b00048c64023020c0f9b0058905c0662e0111008c043c624c0012317008c043c008230211a48f029b9404680a61063021698210c404020ce6c00123189700900446623c0a501159ba703940456965c0440115a6120f00340464007010f959834044c007010d00100c1c045c0040701119b00041c08565c04402071411200c07a702101c0890403c00a070119a59b03940450a6965e6c00419020c043c003010d980c043a))
def mo511H12 (j : Nat) : Nat := (if j<6 then (if j<3 then (if j<1 then 0x27be519880000000000000000723e0000000000000000000000000033a3800000000e1a6000000001417a000000000000000000000000000000000000000000000000001813d00000000000000000902f0000000000000000000000000081c7c03300000cc580000000078efc00000000534800000000000000000000000000000090590000000000000801d800000000022f00002060c00000000000000000c2520000000000001c2e6000000000000000000000142a09f4c000000009030c023c00000000a1550000000000000c3e700003014800000000000000000000000000000000000000000000000000000000000000000000000090a880000c6c8000000000000000000000f058902f28648ae1e71c08a4c40000000000000000000018742000000000000000000000000000000000010938000000000000a03c80000000000000000000000000000010957a07c00000000000000000000000000000000000000000000000000000000000000068650000083b2e3e50000000000000000000000000140c9000000000000000000722000000000000000000000000000000000000000cc5200000000000014e5600000000000000000a0d3000000000000000000000000000000000011e1000000001c10800006831b8288000061a391f2c000000000000280a80001c7870000682ac000000000000000000000000000000000000016fce37d58000000000000000000000000000000000000000000c92400000000000000000000000000000000000000000000000000000007831c000000000000000000000000000000000380680000f3a2800000000000000000000000000000000068c8400000000000000000000000000000000000000e1ac83da800000000000000007b0c8000000000000000014da5e09c00000000000000000000000000000000000000000018610000000000000000000000e00fb1ce000000000000000000000000000000000000000000000000000000000000000000003c20aeef5205a80000000000000000000029df800000000000004e6c0000504c8000000000000000000000c43600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000510c400000000b0560000000000000000000003584b06f400000000000000000000029cdc0000000000000163a014a000080a4700540000000000000000000004684000000001800420100000020200000000011110301000001001010100200010100010000040000000001110100000001001101202000010020101010010000000100001000100000000011200001000000011000110000101000100100001002000120001010101 else (if j<2 then 0xc1fa00000000000000000000000000000000000000000019cbc000000000000000009038000050468000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003016c000000000000000000000000000000000282a400009031800000000000000002015c0000000000000000000000000000031f478f4c000000000000000000000000051b8400000000e4435847c00000000000000000000000000000203bfc58c000000000000010ae0000000068938000000000000000000000200ab17e800000000000046ad000000000000000000000000000000000009119dabee11e0000608f1ce7ca3d300000000000000000402e00000000000000000000005dec00000000000000000e0640000000000001a0d500000000000000000331d000000000000040be000000000000091e7000028ec4815f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100b90000000000000000000000000000000000000041c9dc212000000000000000000000000000000000000000000000000000000000000000000000388000000000000000000000000000000000000004a13800008189000021e5245af00420000000000000000000006213c00000000000000000000000000000000000000000000000000000000000000049d28000000000000000000000000070518000000000000f104000000000000000000041c00000000e024000000000611c000000000402400000000000030c540000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048ecc00000000000000000000007cf21bc800000000000043b580000000000000000000000001668b0000000000000000000000000000000000c137000014e9800000000698bc0001645f000000000524600000000000000000000000000000000000000e3d60000000000000000000000000000000000100c400000000a02780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006006000000000000000000000000000000000000005587400000000000000000000000000000000000000000000000000000000000000000000000000000000000014542000000000000000000000000000003c59e00000000000000000e0ece09e000000000000000006960cc4e0000000000000000000000000000000000029a702c3082c00000000000000000000000000000000000000000000000000000000000000000000080a40000808c8000000000000000000000000 else 0x1c2f2000000000000000000000000000000000000000000000000000000000000000000000000000018200000000000000002e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000046bd000000003d0a00000000048748000000000413000028e8600000000000000001604d00001824681ca0000041800000000000000000000000000000000000000301b000000000000000001c2250000000000000000070cb0000000000000000000000000143d10000004fc000000000000000000000000040017a14c0000c059a050800000000000000000000000000000000000000000000000000000000000000000005b430000102b80000000000000000000000000000000000c3ea0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e9a90000000000000000000000000000000000000000000834f21b90000000000000000041dd00000000000000000000000000000000000000000000000000060c78000000000000000000000000000000000000000000000000000000169060000000000000000080b68000000000000000000000000000000000000000000000021578000000000000000000001002146c60000000028390000000000000218660000000000000000000000000000000000000032c280000000000000000000000000819a00000000000006188000000001116a00000000000000000000000000000000000000000000001d16e0000000061b1e8796605f00000000110ac0000516ec962c478c00000399800018cba00000000000000000000011ac80000000066180000000000000000080cd8000000000000000000001d2940000000000000000000000000407240000000091ae000000000000000000000000010182000000000000000000000121540000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000014185000000000000000000000000000001068e0000000000000000000002854c00000000000000003c0dc000000000000000000000a0748000000000000000000000000020f000000000000000000000000000000000000000000000000000000001026c00000000000000003807da9c600004046c00000000000001dc00000000000000000000000000000059f08000000000000000000000000000001020800000000000000000000000000000000000000e7cc000000000000000000000)) else (if j<4 then 0x907f00000000000000000000000000000000000000000000000000000000000000000000000000000000063e2618f505da0000503a522d8000000000000000000000000000000000000000000d45c00000000000000000500dc0000000000000000000000000000000000000000000000000000000000024aeb04b38e640000f16700000000000000000000000000000000000000000000000000000000000140950000000000000a0dd000000000000000000000000034338000000000000000000000000000000000000000000000034342e31d000000002c1500000000058b2c00000000000068df400000000000000000000000000000000029172000000000000000000000000000001c2aa0000000000000000000000000720164cbc88330000000000001c7960000000000000000000000000000000000000058d88000000000000000000000000000006873692be000000000000000000000c0d8000010f06000000000000000000000000000000000000000000000018c2c00000000000000001266100006800e89ee000000000000000000000000000000000000000000000000000000000000000000000000f40380000000000004080982a6c67400000000000000001eefe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000049e9c0000000000000000000000000000000000024c000000000000000000000000000000000000000000000000000000000000000046640000402d00000000000000000000000000000000003818800000000000000000000000000000000004078000000000000000000000000000000000000000000083cc00000000000000000479e00000000000000000000001e200000035400000000000000000000000000000000000000a3c059e6948ec0000000000000000000000000000000000000000000000000002e7000000000000000000000000000000000000000000000000223413db8000000000000c03500000000000000000282d00000000060c98000000000000000000000000000000000000000001e79b00000000000000000331c00000000000000000000000000000000000000000000000000020031875200000000000000000019de06bc24cc00000000000000000000000003128000000000c1ad000000000000000000000000029abc000000000000248ce000000000000000000000000000000000000000000000000000800800000000280d6000000001211400002036000018504000046b500000000000000000f13600000000000000000000000000000000000000000000000d7d80000000000000011900000000000000000000000000 else (if j<5 then 0x484c000000000000000000000107b8000000003c02e00000000693d7cd1000000000000000000000000000000000000500d081000000001028e000000000000101170000000000000000000000000000000000000000000000020cad05d8000000002128508c000000000000000000000000000000f3ba00000000000000000000000000000000000000000000000000000003875c0000000000000000000000000000000000000000000000000000000000000000000000000000000018f7400000000000000000000000000000280f800000000000018f8ee6e5000000000000000000000501a4000000000000000000001a72c000078ca8000000000000000000000000000000000003500000a0bba03d400000000000029ca6c09200000000000000000e0f943ce000000000c65b0000000000000000000000000000000000000000000000000000000324c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005029a033e000000000000000000000000000000000000000000000000000e1af000000003c58a0000a49a000000000000000003a628ce540000000068540cf6083d4000000000406a00000000000010cb80000fa0f920a80000000000000000000000000d05000000000000000000000000000e98320d8800000000000000000000000000000000000001096b49840000000000000000000000000000000000f097392ec0000000000000000000000000000028d6a41860000000000000000000000000000000001035d939a8000000000000d4ca800029384e02300000000000000000107f80000000000000000000024098000020c900000000000007393000000000000000000000000000000f7c500000c68c494f0000002200000000000000000000000000000000000000000000000782240000000000000000000000000163000001c76a0000000000000000000000000000000000000080538000384260000000000000000000000000000000000000000000000000000000000039ea8000000000000000000000000000000000000016782e03000000000000000000083440000e14900000000040ce000000000000000000000000051db400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000382b80001a0cd00002a007c2ff430200000000000000000000038b040000c13b00000000000000000e0818000000000000000000001cf3a0000000000000000000000000406f400000000000069eb40001e69b00000000000014178710d00000000041b60000000000000000000000 else 0x6b0c4000000000000000000000000000000000000000000000079ce4000026cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006a24d4f4a000000001804c0000000000000000000000000406d000000000000000000000000000000000000000000000000000000000000000000000000000000000d4c2800000000022800000000000000000212e150700000000000000000289720000d39d486ec0042a2640000000020e50831c718c80000000000000000000000001635e0000000000000000000000000306ac0000000000000000000000000000000001aefd0000000000000232e00000000000000000000000000000180c10000000000000000000000000000000000d0de0000000000000000000000000000000000000000000000010b4800000000000000005053518bc0000000000000000000000000000000000000000006587dd8da000073d4000000000000000000000000000000000000000000000000000000000000000000007274c000000000000000000000000000006820c0000000000000000241da000000003844c00002014000000000530e806d63ad80000000000000000000000000000040c50000000000000000000000000000000000000000000000000000000000018158f3cfd0495019c00000000000000d526957f0c300000000000000000000000001c7af000000000000081c3000000000000000000000000000000807600000000006160000d4a2800000000000000000000000000000000020434000000000000000000001807d00000032f82d0000020be80000000127b10000000000000875c0000000000000000000000000000000000000000002d12800000000000018e5c00000000000000000000000000000000000000000000000000000000000000000000ea68000000000000000000000000018888000000000000000000000000000000000008baa04800000000182ab000000000000000000000000000000000000000000000000000000000000000000000000383b800000000000050a9400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004bd0218000168430000000000000000000000000000000000000000003044800000000000000000000000001274742440000000000000000000000000098300001223000000000000000000000000000000000000000000000000000000000000103a0000000000000000000000000068110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a19e800000000000000007069400000))) else (if j<9 then (if j<7 then 0x142e4000000000000000000000000000000000000000000000000000204a00003828a82b000001097400000000000030047ec3c00000000000000000000000000000000000000000000002ce5a0000347dd801c0000e98e000018adc000000000000000000000000000000000200ee0000000050586808e00000000000038e0600000000000000000000000000000142700000000071b28000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e63b0000000000000009b00000000000000000631d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007069000000000409b80002d11400000000000000000000073bbc07540000000000005810c000000000000000000000000000000000000000000107db01bc0000000091710000000014695000000000000180ea00000000000000000410780000c1e40000000000000000000000000082cc00000000d0476065c00000000f15600000000000004082000000000000000000000200a800000000081c5022000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e08d00000000000000000000000001013100000000000000000a35000000000000000000409440000000000000000000000000b193b93d800002167000062174000000000000000004e4a000040e0000000001e065000000003444e00000000000018793e0720000180fc000000000000000000000c3820000680ac00000000000061f200000000000000000000000000000000000000000000000000000000000000000000000000000a01000003017e000000001842c000000000000000000000000000000000285d0000000001822c00000000000008bac0000000000000000000000000000000000000000000000281f80000000000000000000000000432d00000000000000000000000000000000002031510c1a124000000000000000000000000000000e068e07b00000000147c944290000000000000000009bcc00006fa7000000000000000000000000000000000000005068c00000000000000000000000000000000000000000000000000000000000000000000475800000000000000000000000000000000000000000000000000000000000581580000000000000000000000000000000000000000000000000010d5c00000000000000000000000000000000000000000021c8ac690812d0000000000000000000000000000000000000000 else (if j<8 then 0x54000081630000000000000000000000000000000000000000000000001990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ce47e0e8741b80002821c00000000000000000c0eb00000000000000000000040590000000000000101040000000000000000000000000000000000c3820000000000000000000000000000000000814c17228000000000000c017800000001ee1d000020718000000000000600040000000000000000102b200000000000000000000000000000000000000000000000000000000000000000000000000002a6500000486600000000000000000000069c0800000000000000003009400000000000000000000000000000000002078000000000000000000000000000000000000000000000000000d0c2000000000000000000000000000000000000003cf42000000000000000000000000000000c4a6000060070000000000000d0a000003dc4c000000000000213560000000000000000000002148d0010000000000000000000000000080da000014f48000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000521b5c13a00000000006f8000000000000000010dea000000007890c000000000000000000000000000001051c0000000000000000000000000675a80000812600000000000014708679700000000000012eb70000000000000000000000000000000000000000002413c00000000521d8000000000000000000000000000006bea40000000000000000000000000b21900000000000000000000025e9400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008e9c00000000000000000000000000000000000001e171c073a0e4c00000000000000001041600000000000000001406c000000000000000000000000000000000000000000000000000000000000009c000000000000000000000000000000000161424315b8312438a00000000000000001014e0000000000000000000000000000000000142c0000000000000000000002484a00000000000000000000000000000000000000000000000000000000000000000001026b616d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001cc5f0000582dc00000000000000001805a000000000000001c200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000027a30000000000001618f0000000020246000000000000000000000447a0a5580001c660000020370000000 else 0xd23e00000000302d8000000000000000000000000000004802c0001209a00000000318ce018c0000000000000000000000000000000000000021e824f7200000000502a80000000000000000000000000f09980000000000000000000000001c0e200000000000000000000039e640000000000000000000000000000000000000000000000000031d720000000048a740ab40000000000000000000000000703480000000000001957c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001d6c000000007a18c0000000000000000146186eb840d900000000000000000000034124000000000000242220000000002110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000708c4000000000000309480000000000000000000000000000000003c1c8000000000000180a000000000000000000000000000000283840000000000000000000000000000000001a86400000000000000000000000000000000000000000000001203300000000000000000a06f000000000e87100000000000000000000000000000000002097800000000000000000000180a6000000000000000000000000000000000000000000180c80000000000000000000000000000010ec1413000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e31f000000000000000000000000000000000000000000000000000000000000000000000000000000000747a800000000000000002a1c80000000000000000291f80000000000000000000000000000000000000000000000000000000000000000000042a9512f00000000060d40000000000000000000000000000010266000000001827c0000000000000404a0000000000000000000000000000000000000084e7000000000e2b100000000000000000527d000000001200f0000100e800000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000b0110000000000000000000000000000000000285ac00000000000009b1400004198000000000000000000000000000000000000000000000000000000000000000000000000000000000000050c8000000000000000000000000000000000000000000000000000000000001e070000000000000000000000000000000000021cd80000000000000000000000000000091ca0000241ee000080a5686800000668d000000000000180fa22808000000000000d316c81)) else (if j<11 then (if j<10 then 0x5390c0000000000000000185ac0000000000000000000000000000031005015ae42c800000000000040640000000000000000000002c2ba0000000000000000000000000000000001c01c4051186000001267f0000000000000a14b00000000000000000000000000000028f6000000000000000000000000000000033b000000000000001b7e0e98000000000000000000000000000000000000000000000090e7000000001e25f00000000000000000000000000000000000000000000db8e7590000100e0000000000000000000000000000000000000000000d123898f0000000000000000000000e312000060a9800000000000000000000000000000000000000000000000000000000000000000001063000000000000000000000000000000241c6000000000000000000000000000000000000000000000000000000000000000000000000b0e50000000000000000000000000000000000000000001010c0000198380000000000000000000000000000008d4c00000000000000000000000000000000000000000000000000000000000000000000000000000000000034118000000003821c0000000080c0f872c00000000f1d4210cc0000000000000000000000000000000000000000000000000000000000000000000000000000e05780000000000000000000004030000000002801400000000000000000000000000000000000000000000000000000000000000019d04000121430000000004c6c00000000000000000000000000000000000000000000003c20000000000000024a1e00000000000010e08000031930000000000000000000480000000000000000000000000000000000000000000000000001c4b4000000000000000000000000000000000000000000509880000000000000000000000000000011a3c00000000000000000000000000000000024dcecf83000000000000000000000000000000e31f00004be10000000000000000000000000000000000280fe00000000000000000000000000000000000000000048204000000000000000010d88000000000000000000000e090800000000000097e100000000000000000000000000000000000000000000000000000000472400000000000018698000000000000000000000f10b000000000000000000000000000000000060e9400000000036480000000000000000000000000000000000000040800000c40e800000000000000000000000000000000000000000000000000000024f300000000048eb400000000000000000000000000000000000000000000000000280f40000000000003c37e000 else 0x2026a0000000000000d20fc0390000000000001005800000000000000000000001d54c048e10600000000247460000000000000000000000000000000000000000003182c00000000000000000000000000000000000000000000007a5540000000000006855000000000000018747c0ea000000000000000000000000000000000126f700000000000000000000000000000149b0000000000000000000000000000000000000000000000000000000070300000000000000000000000000000000000000000000000000000000080160000000000000a804000000000000000000000000000000000000000185c000000000000000000000000093b4f8c18000000000000000000000000000000000000000000500c8000000000000000000000c12c0000d134800000000e162000000000000000000000000000000000040b70000000000000000000000000021660000000000000000000000000000000000000063e14000000000000000000000000000006861f00600000000000000000000000000000000000000000c680000000186e4000051f54000000000000000000000000000000000000000000f7a280000000000000000000000000000000000000000000000000000000000000000000000000000000021e0580f5438800000000000000000000000000000000000000d1390088400000000b14b00000000000000000193f7057c0000000000000cd9a000000000000000000000000000000000000000000000018e77a1320000000000000000000000000000000000000000003422a0000000000001df0e00000000000000001afd30000000000000c0db000050e2800000000000011ed800000000c0b28000000000000d0e78000000000000000000000000000000000602e8000000000000000004268000000000000000000000000058d8000000000a1e180000000000000000000000001a8620000000000000000080700000000000000243f000000000000000000000000014637000000001c1e80000c1d8a3f440000000000000000000006396a07c00000000000000000000000000000000000000380120000000000003c2f4000062af00000000000000000000000000000000000000000000000000000000000141b3000000001032be1a200000000000000000000000000000000000000000000000000000000000000000000675d00000000000000000000000001e72410bd800000000000090a780000000000000000019380000000000002a1c00001401d000000002d0960000000048450000044b6000000001c11543170000000000001e2f4416c8000149780000000000002855c000000000000085f0000000000000) else (if j<12 then 0x2c2d8000000000000000000000000000000000023c1000000000000000000000000000000618e00000000000000000b04f8000000000000000000000000160510000000000000000000000000000000000000000000000000000000000018ec6000000000000000000000000000000000000000000000000000002700000000000000000000000002835c0000000000003c33c0000000000000000000000000000000000000000000000100340000a1c7a1f0c0000c10a000000000000000000000685a8dde80000a3b2000000000000014d1800000000c6b6000000000c2ec000000000000102e400000000000000000c6cb0000000000001c878d7c700003468aa23f0000000000000000063e300000000000000000000000000c3b400000000243a8000000000000000000000000000000000000000000000000000000092c3800000001e8fe000000000000102db0000000030316000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c6e3914e73c1c00000000d07e00002005ca882000000002c1ac00000000000000000000000000000000000000000000000000000000000000000000000070dc000000000000000000000000000000000000000000000000000000000000000000000000387ab47b4000000002463600000000000000000000000000000046f4000000000000000000000000000000000000000000000000000000071de0000181bf017400000000000000000e1db00000000000000000000000000000000000000000000000000000000000104ba000000000000000000000000000000000000000000145f8000050ba80001437400000000000000001a460c0890000000000000000049cc0000000000000000000000000000000000000000000000000000000000000000000000000000090b7a0c68000000000000000000000c1a9000000002c3560000000000000000000000000000000000000000007057b08de00000000000000001815b61160000000000000a0ab800000000000000000000000000000000000003c21e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000526d80000a38000000000382c14c7500007012cc6aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000505700000000000000000342e00000743400000000000000000000004f660000b3cab1e88000000000000000000000000000000000000000000000000000000081cc0000000000001e2a700000000000000000 else 0x58367504e00000000000000001941d00000000000016323000058e4000000000000000000000000000000000000000000000000000000000000000000000000000000000580b0000000000000000000000000000000000000000000000000000000000000000000000001c34a0000782b40000a2610000000018184000000000000000000000000040a900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000202ad0338000000000000000000000000004f5c87c0000031e780000000000000000008bc000000000000000006116000041d6b019e00000000191b400000000000000000000000000000183c400000000b739000000001621200000000000000000000000000000089580000124940000000090068000000000000000031ec800000000000000000000000000000000000000000000007034000000000000000000000023a4a1a700000000000000000000000000000000000000000000000000000000000160290000684ac000000000000000000000e44500000000000000000000000000000000000000000000001c139000000000000140cc00000000302fc0000000000000000000000000000000000000000000000000000000f31700000000061460000000000000000000000000000000000b12a0000000000000000000000000000000000000000000a05d0000000000001c337000000000000000000000000014660000000000000000000000000000000000000000000000000000000040230000000000000000000000000000000000102100000000000da8000045d9813a5213000000000000000000821400000000a4840000000000000f0736806c000000000000701145c3fe3be0000506440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038050000000000000000000000000069ea400000000000011eac000000000000000000000000000000000308e800000000000000000000093dd8000000002930000000000000000000000000000000250c0000000000000000000005a20000000000c013000000000000000000000000000000d03d80000417c0000000000000000000000000000000001c39900000000000000000000000000000000000000000034f7800000000000000000000000000000340e600000000000000000000000000000000000000608e8000000000000600f00000))))
def mo511D13 (j : Nat) : Nat := 0x101e5cda500ca52e0cc1054c80103105e6d39600118825d399240460884a074e64901182234e54d00082180e5d301302185e9cc9202502384062f369cb000902c20315974e68004395974e6080e00d1a0010620407a6026ca04716101e9cb01301234c00898181192e6800420b02301d3941081f4e50220410101e5811b4c8200a511a52408c8c112074a548205d3173444028acc80208202698a8132888445c0133031420389a7345410c88a1c266400c65010444d3150268648ccd002081066989013450240c809840108369cc101a015066061e0cc101899a0030c203cb9b4c018203cba73401b2e6d3004080f2e6d2006080f4e5811860018203cba440e101e5811b4881c18808465d20230a1706606245c1982084b06608260cc0c30b8330410004cda460a1734008205cc0c6090130808245cc002099a0040d4e0cc1018a834e6080c5c1a7304062d155008b4cefcd7cb89a3c99c81c69c4e42f4093f13e03c4ba5b8db7935db4cb2db0b2f68d32e22d12b229da7ea66a442332141fc0b49e79da1c90b49bb9a398b97a96294a92f1139098f50e40d30c20b48a383d88f07e06d05c04b03d8290148007ff64587ffec830fffd8721fffb2243fff65d81ffe4bb03ffd87607ff90ec0fff64981ffec1303ffd90607ffb30b8fff26171ffec3ae3ffc875c7ffb24b8fff60971ffeb92e3ffd905c7ffb3090fff65d21ffec3a43ffc87487ffb2090fff61d80ffec0b01ffd71603ffa42c07ff61d70ffec0ae1ffd715c3ffa42b87ff61d10ffec1221ffd72443fbb2643dff64487ffac890f7fd9021fff32043dff25d81bfecc2e37fc985c7bfb0eb8ffd60571bfecc2437fc98486ffb2e90dff25d21ffac0a437fc976037fb0ec05ff66170bfe4c2e1ff9805c2ffb30885ff26110bfecba217fc97442ffb24887fd5c510ffcc02217dd9321efeb2243dfe64087
def mo511H13 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x50000205e400002247000000000000000005014d446de42100888000000000000612b000000000a8ef826500002812a0000000039c130c86000000000000000000000000040bec0000c00500000000000000000000063807021c0000000000001c46e00000000711cc00000000e08961bd40000000000006a1880000000000004919000000000000000003c91a00000000000000000000000000000000000000512d000000000000020820000000000000000000001014c00000000000000000000000001812400000000000029a0800000000c0060000081610e5b000000000000000003b2900000000068526157119a4000100350000000000000000000000000000000000228d00000000000002b7a700e80001664ec33300000000026ff247a000015e29a0d600000000150d5ef19000000000000020d2d38b00000000000000000280cc0000000000000000000002e6c000000002cdf600006054f8163c0d400001161e03f40000000000000000201da0000000000000000000000000000000000000000000b9740000000074193b08c0000000000000000000000000000000000c476000000000000000000000000043c200000000000000000000002032902f00000000000d45235000000001e08000000000000000000000000000000000005420000000000000000000000380b80000f04f8000000006016000000001d921c2940000000000000000000000000000000000000000000923c00000000000000a3ee70d015e00001c8640000d18b8000358ca00000000000014df20000000000000000000000000620c400000000000052167184800005472b016c00000000000000000000048890000000000000c06bd0550000205880000000000001805c20ba0000389ded0dc00002354800000001d456f16100000518fe4fdb48560250000000000000000000001483f301378a3a8cee000000000000000000000c110800000000000000000000319220000000000003c17d628800000000000000000000061c7d010be8e4401fe10cc0001407e00000000000000000000000000000068af040691203009724230000504349040000000000000000000000a4718046cc196a0770000589ce4e0ac2640000000000000eec8c146a19c000000000715e800000000000000000000101c600000000000015c3400000000209c800000000000000000000160ad000028308000000000000000000000000000004924000000000000000000000000000000000000000000090608000000000000000049aaa1c9a00000000204140000cf1ef2328000000000000098002213023010100413002400101100200260074122220106414210020013430061003001312126301104000010140020222701e11242c10060331000463000040001106103020100 else 0x70ebe723dd11d11c36e82443070000285dc2258000000000000000000000000000000000000000836000000000d33e12228000000000000000000001600b00004988545d6000000000000000000000000041464000000000000000011002000000004036c000000000000000000000000000000000000000000000000001d122000013021ba0400000000000009b68000000007720000000000e21000000000000000000000038c340001007c403780000000000009346801b39ca4e0ab202400000858a000000000000000000000930680000000025080000000031c90000080161833c000180860000000000001aef4300d00000000000000000383c00000a68777728000040c0b65342224096d018702b15163aa14cade7c644815c4813891e600005789201880000866a000009bf40000010ff223eb9b8000000000000000000000000000000000000000000000000000000000000000638fc00000000f341800000000000000000000000000000300bc837d8a3c000000000000000000000000008af800000000f39000001c6280000000000000000000000000000005dc80000000000000000000000000000000000c0b1b02600000000000000000000000000000000000000000018ee30000000000000000000000000000000000000000000000066ab0000000000000000000000000000000000f28500000000000000000000000001626300000000000000000d31a10aa0000000000000000000001441d000000002c1899655e07f023c400018855f15c80002ccd6000000000000000000000000020bd400000000000000000000000000000000000000000000860000000000000000071c01c1ec0000802aa03c80000000010698011c000000000000483e00000000000000323800000000914e000000000000000006b0875060000000004042c00000000202b48b740000e274000000000000000005126e045541de00007018000000000000000000000100f20000112c800000000c0b2f3657238642000000000061c6800000000433d000000001683e0000000000000000000000000318e6ec6400498000288340000d646f19d9423d208900000000000000000000000000ce1400000000000000000000000005811bc1afa430000000000000000000000000000000000000000826c0000e0dd9328521fd50dba7060000781ebc1386029b47018338000000000000000000000000000005240c0000000000000000185160000001a0000240ec000000004232800000000e08500002822c6007b076598ea40400000000000002804a00000000000011de200000000103280001a86cf017f846800000000000000002020c00000000039840000000000000000311974015000000000000000000000000029c8e0000000000003c0260298e22) else (if j<3 then 0x80000000000fc0000000000000000000000000000000000000000000000000000000000005182000000000139400006014000071c064d9c00000000000000001a2750000000000e066e590000238c4000000000000000000000c46e00006887c000000000084a831705f200000000359594883c6d0642b48ae905d2e09a533630c021a1b8e4b000000000000000003015000025d8fa0ae00000000000015452000000002420200000000000000000c2890000000000000000000005840c0001823f000000000000000000000000031228000000003246800010e0d90450000269e8000093317a12f5de6e0e40729a939ac15e00000000718f80000000000000000000006844000000001c822000030025003c0001eeef0000000000001e85bf050000000001491b000070212c5f00000a16780000000182e300000000000000000000060090000000000000000000000e3180000403cc000000000000000000000000000000000000000000170ef1b82c147666500003232509e200000000000000000000000000000000000000077080000000000000000000000001ae3e000000003c07200003328800000000000000000000380c7809100004008c0000a0a8000030184000000000000780a000000000c0090000000000000000000001018c000000005143441a0000000002846000000000337f000000001e87d772a800000000ee6d0000639fc000024490000000034897aee00000000000000000000602b3d70dec00000000000000000c8888048000000de20000000019a15017e0000000000000000000000000400440001c6f80000000000000000011898000000000000e03280000000000000000000000001c882347ea22f985a40000000050c1b4044000000000000000010c74c06e0000000000000d0250000000000000000000000000000000000000000000000000007a1c8000102d300000000000002043000000000000000000000000000000000000000000000000000000009aa191000000e4640000281cfe01e00006823c00000000e06d0000000012461f4408000000000000000053b240000000001890000048d800008064000000000a1193078b19ec00000000338400003c0e00000000000003407a0000000003be24cf20000000000000000160f7000000000000160a400000000241a362d8000000003013a000000001021dd0f6000000003814000000000000000000000000000000000038990000000000000000006e7d000000000000020b4d12a4a17440f6e4f5000070420c13000000000000000000000000000000000000000000000003001400000000000000000202b000000001c062a24527088000000000000602b80002c11988bc000000000000000006457000035094000000001845000000000000000001e8b else (if j<4 then 0xd5a179800000000000000007010800000000f07c800000001422200000000000000000000f8000312320000000010b6400000000000000000000000000000000005cadc88f00000000000000000b20d800000000000000003b403001200000000700400001a0e80000000000000800100002086000000000b48f8000000000000000000003c06c0000000000000823aae30000000002851e0000000031a7ac5bc0000000078898d090005d548400000000124e1900eb10f80000000010598000000000000a26480367c24266d7f05c0014800018912000000002903594539a79d8265dc956eba11050000000000000d07a00000000000000000000000001c038f1438000000000000b04b800008e0400000000000000000000000002bbf5800da0bc304f011b400014117523f800000000000000003138385b8000000000000241bc0000000000000c8fa0000000001430000000000000000000000000000000000000000000000000000ccc60000000013c0e051800000000603a7109ba1020000000001d950e80a0900000000000000000000000000000000000000008004000000000000000000000000008147049000000000000000000001900000000000000000000000001001000000351800011d972500540300000000000000000302e7444e0000000000001ce1622f000002099d022674550000182944083a03b8188fbc7c84a60000847f8000000000000000000003481a0000000000002c0f0000000000000000000000000000001017a00000000000000000066e800e0000000000000000000000c902000000000000000006321000000000000000000000000000000a68e000000000cdb320c900000000041cc0000733ee810000000000000008bd00001822500000000000004067000048038000000000000600f00000264f000070980c04e000000000000000000000000000000411c0000233980000000000000000089880001c021000000000000000000000000000001a0883334523700000000000000000341cb66720000101f400000000c14a80000000006f76121101c7049e0000000000000000000000000083e800000000000000000c0dc000000006b9a941040000320080000000120b68032681cc0000402d000000003811a0000000000000000000000000000000001c00d217e5bb04000000000000301c800000000000000000000000000000001a00000e68100004a07c0000000000000000000000000f719000000000000000000000000000000000063bfc00006044000000000000000000000000000000000000000110081c40000000020a4800002847000000002c49c011c0000202b0000000000000000000001229a000000000000000000000000000000a709204080000000000000000000000001a30cea2e else 0x7b9ec00000000c27f8000000000000e08f800000000000000006909000000000000000000000060b50000000000000000041838184c000000000000000000001065b305b800000000c32200000000000000000f11890134000000000000780ddc22160a2000070165ce0e00000000293be81760000000073c2800008ebc11725031c000000000000098c349220000000000000000186e7d722000000000000000000000000000000a06680000812c00000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000001c14241070000000018596e66700000000181ea0000000018c6c0000000000000000000000000740e8000000000000000060488000000000000000000000000000007b1800000000000000000080060000000000000000000000000000000000404500000000386080000d3568000000000000f0278000000000000903a0000000000000000000000000000000000601a400000000d43080000c14e0000e158000018df4000070773a3e000012609a32c800000000000000000000180cc000000000000000000000b07f8000000000000000000000000146e100000000081d600000000203a800000000000000000000000000000000035172000000000000141f600000000000000000805400000000000000000102f800000000000000002888c000000000000000034606e8ba704900000000160cca30db03840000e67f0000299d400000000301f43c68000000000000000020116000000001016a50220000d15780000000000000000000000000000000007820c0000000000005a06c000000000000000000000000000000000145200000537e7208b1e37cd0c0000000000000001800002806c000000000000101fc00eba06d00006085400002460307079a9ec4ca)))
def mo511D14 (j : Nat) : Nat := 0x25826a44160a449831a59a90049401a9205a60166105120a6614318ca45980106e4ba9c9c78542a00ffd87ffc87ffd81ffd71ffd21ffd80ffd70ffd10
def mo511H14 (j : Nat) : Nat := 0x622e000000010310000204800000000143c03c0000000000000000002a23000080d68101833c03404a8000798d00000002d1300000000e63000000000000a0f91d3e8230000000000050030001c8c2405800000000000000512b00000000000000000012c8480c000000000100cd2a1ae210a000348d80000000e2dc9cdb217000000020110000d40e0000dce0000000000000000000000000000000000003d20bc0000127f24200000006920913e00008580000d01a00000005a32b05a802000003950001e23c0098000000000000000000000000000004a1f00000003c0e2024d2078e7f1d323b97342a8cc0000a1be162c0b80000825a47a0000000351f341fe47000040934014000200800000000e612c1ff81b0001cee910f7bc00001eec0000000000000000000300053320002c1dd115d940ee798c4b814000000034cd0139134fc0a7c0100001a3c167c0001805113c00028578000b35348880000b89624c00000c2800062806e8c0000000000144e8000022000012010000000010546e800000000000000030d363b20001767a41c2816200c0000852ed200406e6fe81600000000e89c0000000f0232026c1580000000000040b80000000cecd4d19b83977a000000000000001e09fc9188b80000000000000000000000380ad0378350000000032400000f6800005b250001040400000000001ae04000313200000003cdb0000000000004c381a2a04d6e89418601f507a00000000000000000000108000000000000000000370e04cc492800021540000000293d0000000040700000000000000000000000e8e4504800000000003c1c8000000000030d2600c000180670558000072ec0a31008000b65400000002a1c000040d80000a3a503b268281e0000907562440002922520e0002800e909300e0000000000000000001195c834f42a00024190180615542000025005850ae0221174301202300
def mo511D15 (j : Nat) : Nat := 0x1409309ff
def mo511H15 (j : Nat) : Nat := 0xc020000048202000000000000003280000000011e8003908100069910c0020c480000000003bc00000101800216e94000000014556c3942340020280000181c0000054800000000000003dc000740c4f59b3c0
def mo511L : Nat → Packing
  | 8 => (13,7,5,0,0,0,0,mo511D8)
  | 9 => (73,6,5,0,0,8,0,mo511D9)
  | 10 => (278,5,5,0,0,12,0,mo511D10)
  | 11 => (470,4,5,0,0,14,0,mo511D11)
  | 12 => (291,3,5,0,0,14,0,mo511D12)
  | 13 => (65,2,5,0,0,12,0,mo511D13)
  | 14 => (8,1,5,0,0,8,0,mo511D14)
  | 15 => (1,0,5,0,0,0,0,mo511D15)
  | _ => emptyPacking
def mo511I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 4 47 3 12 4 4 mo511H9
  | 10 => lookupWord 26 805 2 15 7 4 mo511H10
  | 11 => lookupWord 102 1033 4 17 9 4 mo511H11
  | 12 => lookupWord 207 6217 4 17 9 4 mo511H12
  | 13 => lookupWord 147 2212 4 17 9 4 mo511H13
  | 14 => lookupWord 36 369 4 15 7 4 mo511H14
  | 15 => lookupWord 5 59 3 11 3 4 mo511H15
  | _ => fun _ => none
def mo511 : Forest := ⟨1535,15,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_0 : CutRow mo511 8 0 13 := mixedCut (pos:=0xc05024108824092088409104411) (neg:=0x221017030948863c1a4b44b1e0b43c0f) (data:=fun _ => 0xbbdc574b87bd462947d985285b7d47649d79875687bc472b87bd442b87bd4428bb7d47485b7d475687bc47685b7d46485b7d464) rfl (by decide +kernel)
theorem mo511B8 : CutRow mo511 8 0 13 := mo511P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_0 : CutRow mo511 9 0 10 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_10 : CutRow mo511 9 10 63 := mixedCut (pos:=0xc05024108824092088409104411) (neg:=0x221017030948863c1a4b44b1e0b43c0f) (data:=fun _ => 0x386bc483386bc483386bc453386bc487386bc48783b6c475386bc482386bc482386bc452386bc45283b6c485386bc451587bd482387bc452407b0573b0dbc552407b0552b86bc481587bd473587bd47385b7d497587bd472587bd472947d986240db0563587bd46385b7d496587bd462587bd462687bc48240db0563b07b0573587bd482b86bc481587bd452b0dbc553587bd452b0dbc55385b7d485b0dbc55285b7d495b87bd452b87bd44185b7d48585b7d484b0dbc593386bc452386bc45283b6c48553cd8030b86bc48153cd803053cd8030b86bc44153c7802053cd80208bb6c48482ad0a53947d9862b86bc481b86bc441b86bc4418bb6c484) rfl (by decide +kernel)
theorem mo511B9 : CutRow mo511 9 0 73 := (@joinRow mo511 9 0 10 63 mo511P9_0 mo511P9_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_0 : CutRow mo511 10 0 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_48 : CutRow mo511 10 48 46 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_94 : CutRow mo511 10 94 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_142 : CutRow mo511 10 142 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_190 : CutRow mo511 10 190 18 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_208 : CutRow mo511 10 208 70 := mixedCut (pos:=0xc05024108824092088409104411) (neg:=0x221017030948863c1a4b44b1e0b43c0f) (data:=fun _ => 0x947d9873b47d987349d7989753cd8040b86bc48353cd803053c78030386bc46383b6c496b47d987349d79897386bc49353cd804053cd8030b0dbc56353cd8030b1bd897553cd804053cd8040b45d887253cd803053cd803053cd8030a79ac252b87bd463a79ac25285b7d496405b0563816d099585b7d4a6947d9883587bd493b0dbc564407b0563b0dbc56385b7d4a6405b0563b87bd46385b7d496b0dbc5a4816d0985824d0a75b0dbc563587bd462b0dbc563587bd451b0dbc552386bc46383b6c496386bc462386bc462386bc4621bdb899781bd0974b1bd8974386bc4a3386bc46383b6c4a6386bc462b1bd8975b45d887253cd8030386bc462386bc462b2ad8a65b86bc45153cd8020b41d8861b86bc451b86bc440) rfl (by decide +kernel)
theorem mo511B10 : CutRow mo511 10 0 278 := (@joinRow mo511 10 0 142 136 (@joinRow mo511 10 0 48 94 mo511P10_0 (@joinRow mo511 10 48 46 48 mo511P10_48 mo511P10_94)) (@joinRow mo511 10 142 48 88 mo511P10_142 (@joinRow mo511 10 190 18 70 mo511P10_190 mo511P10_208)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_0 : CutRow mo511 11 0 22 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_22 : CutRow mo511 11 22 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_70 : CutRow mo511 11 70 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_118 : CutRow mo511 11 118 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_166 : CutRow mo511 11 166 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_214 : CutRow mo511 11 214 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_262 : CutRow mo511 11 262 17 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
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
theorem mo511P11_375 : CutRow mo511 11 375 24 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_399 : CutRow mo511 11 399 71 := mixedCut (pos:=0xc05024108824092088409104411) (neg:=0x221017030948863c1a4b44b1e0b43c0f) (data:=fun _ => 0x53cd804053cd804053cd804053cd804053cd804053cd804053cd804053cd804053cd804053cd804053cd804053cd804053cd804053cd804053cd804053cd803053cd804096abc15196abc151a79bc262a79ac262a79ac262587bd473b0dbc574587bd47396abc151b0dbc57496a9c151b0dbc574b0dbc574b0dbc574b0dbc56396abc15153cd804096a9c15153cd804096abc151a79bc262947d9883b45d8883b1bd8975a79bc26296abc151386bc47396abc151386bc473b19d8975b43d8872a79ac251b45d8872b41d887296a9c15153cd8040386bc473b45d8883b45d8883947d9883b84bc47396abc151b1bd898596a9c151b1bd8985b1bd8975b84bc462b45d8872b2ad8a75a79ac251b86bc462b86bc46253cd804053cd8040) rfl (by decide +kernel)
theorem mo511B11 : CutRow mo511 11 0 470 := (@joinRow mo511 11 0 214 256 (@joinRow mo511 11 0 70 144 (@joinRow mo511 11 0 22 48 mo511P11_0 mo511P11_22) (@joinRow mo511 11 70 48 96 mo511P11_70 (@joinRow mo511 11 118 48 48 mo511P11_118 mo511P11_166))) (@joinRow mo511 11 214 113 143 (@joinRow mo511 11 214 48 65 mo511P11_214 (@joinRow mo511 11 262 17 48 mo511P11_262 mo511P11_279)) (@joinRow mo511 11 327 48 95 mo511P11_327 (@joinRow mo511 11 375 24 71 mo511P11_375 mo511P11_399))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_0 : CutRow mo511 12 0 19 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_19 : CutRow mo511 12 19 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_67 : CutRow mo511 12 67 10 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_77 : CutRow mo511 12 77 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_125 : CutRow mo511 12 125 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_173 : CutRow mo511 12 173 48 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_221 : CutRow mo511 12 221 22 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_243 : CutRow mo511 12 243 48 := by
  apply checkedRow
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B12 : CutRow mo511 12 0 291 := (@joinRow mo511 12 0 125 166 (@joinRow mo511 12 0 67 58 (@joinRow mo511 12 0 19 48 mo511P12_0 mo511P12_19) (@joinRow mo511 12 67 10 48 mo511P12_67 mo511P12_77)) (@joinRow mo511 12 125 96 70 (@joinRow mo511 12 125 48 48 mo511P12_125 mo511P12_173) (@joinRow mo511 12 221 22 48 mo511P12_221 mo511P12_243)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_0 : CutRow mo511 13 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_3 : CutRow mo511 13 3 27 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_30 : CutRow mo511 13 30 35 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B13 : CutRow mo511 13 0 65 := (@joinRow mo511 13 0 3 62 mo511P13_0 (@joinRow mo511 13 3 27 35 mo511P13_3 mo511P13_30))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P14_0 : CutRow mo511 14 0 8 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B14 : CutRow mo511 14 0 8 := mo511P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P15_0 : CutRow mo511 15 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B15 : CutRow mo511 15 0 1 := mo511P15_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511T : mixedTables mo511 15 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo511 0 0)
  · exact (mixedEmpty mo511 1 0)
  · exact (mixedEmpty mo511 2 0)
  · exact (mixedEmpty mo511 3 0)
  · exact (mixedEmpty mo511 4 0)
  · exact (mixedEmpty mo511 5 0)
  · exact (mixedEmpty mo511 6 0)
  · exact (mixedEmpty mo511 7 0)
  · exact mo511B8
  · exact mo511B9
  · exact mo511B10
  · exact mo511B11
  · exact mo511B12
  · exact mo511B13
  · exact mo511B14
  · exact mo511B15
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511G : graphValid mo511 (boundsBefore K503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511R : Impossible false graph 15 nineInputs.toFinset := by
  rw [show graph = targetOf mo511 by decide +kernel]
  exact mixedRoot (g:=mo511) (top:=15) (i:=0) (before_sound K503 (known_down V503)) mo511G mo511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_11042

theorem PEqualNP.Outside.L_meta_11042 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8) || (x 7 && x 8)) t → 16 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact PEqualNP.Outside.L_meta_11042.directSplit PEqualNP.Outside.L_meta_11042.mo511R PEqualNP.Outside.L_meta_11042.g511R ⟨C,hf,by omega,heq⟩
