import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
-- The rectangle argument follows L-meta-8459.
namespace PEqualNP.Outside.L_meta_15012
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 256
def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
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

def bit (i : Fin 256) (a : Sig) : Bool := a.getLsbD i.val
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

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
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


abbrev Row := Fin 256
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


-- Natural-number words, and a search table checked level by level.
def W (a : Nat) : Sig := BitVec.ofNat 256 a
def full : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | _ => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (u : Bool) (o : Nat) (h : (u || Nat.blt o 2) = true) : ∃ e, allowed u e ∧ ∀ a b, bin o a b = bin e a b := by
  cases u
  · refine ⟨o,Or.inl ?_,fun _ _ => rfl⟩
    simpa only [Bool.false_or,Nat.blt_eq] using h
  · by_cases h : o < 4
    · exact ⟨o,Or.inr ⟨rfl,h⟩,fun _ _ => rfl⟩
    · refine ⟨3,Or.inr ⟨rfl,by omega⟩,fun a b => ?_⟩
      have h0 : o ≠ 0 := by omega
      have h1 : o ≠ 1 := by omega
      have h2 : o ≠ 2 := by omega
      simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
set_option maxRecDepth 8192 in
theorem W_inj {a b : Nat} (ha : a < 2^256) (hb : b < 2^256) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (u : Bool) (R : List Nat) (T L : Nat) : Prop := Lower u (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (u : Bool) (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice u (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^256) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 256) && decide (e.2.2 < 256) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

abbrev BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^256 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧ (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
theorem BaseP.lt {T R} (h : BaseP T R) : T < 2^256 := h.1
theorem BaseP.plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
theorem BaseP.nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
theorem BaseP.plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
theorem BaseP.ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
theorem BaseP.prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {u T R E K} (hB : baseOK T R E = true) (h : Impossible u (W T) K (rootsW R).toFinset) :
    LowN u R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {u T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN u R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 256).all (fun r => let q := rowOf vs w r
    Nat.blt q 256 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 256).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 256).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 256).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {u R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN u R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN u R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def opOK (u : Bool) (o : Nat) : Bool := u || Nat.blt o 2
def av (u : Bool) (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || (u && Nat.beq x (Nat.xor d m)))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (u : Bool) (P : List Nat) : List Nat → List Nat
  | [] => P
  | c::cs => mkPool u (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available u bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {u} {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS u f bank P)
    (h : av u d P v = true) : Available u bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | ⟨hu,h⟩⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv hu e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {u} {f : Row → Row} {roots bank p P} (o a b : Nat) (ho : opOK u o = true) (hr : Reach u roots p bank) (hP : PS u f bank P)
    (ha : Available u bank (RF f a)) (hb : Available u bank (RF f b)) :
    ∃ next, Reach u roots (p+1) next ∧ PS u f next P ∧ Available u next (RF f (nb o a b)) ∧
      ∀ v, Available u bank v → Available u next v := by
  obtain ⟨e,he,heq⟩ := bin_four u o ho
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) he ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {u} {f : Row → Row} {bank P} (hP : PS u f bank P) (i : Nat) : Available u bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {u} {f : Row → Row} {roots} (cs : List Nat) {bank p P} (hr : Reach u roots p bank)
    (hP : PS u f bank P) : ∃ next, Reach u roots (p+cs.length) next ∧ PS u f next (mkPool u P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    have big : ∃ next, Reach u roots (p+1) next ∧ PS u f next (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) := by
      cases ho : opOK u (Nat.mod c 4)
      · refine ⟨_,Reach.two false hr (Or.inr (Or.inl ⟨false,rfl⟩)) (Or.inr (Or.inl ⟨false,rfl⟩)),fun v hv => available_cons _ (hP v hv)⟩
      · obtain ⟨next,h1,h2,h3,_⟩ := pay_nb (Nat.mod c 4) _ _ ho hr hP (getD_ps hP (Nat.mod (Nat.div c 4) 32)) (getD_ps hP (Nat.div c 128))
        refine ⟨next,h1,?_⟩
        intro v hv
        rw [cond_true] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact h2 v hv
        · rw [List.mem_singleton.mp hv]
          exact h3
    obtain ⟨next,h1,this⟩ := big
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (u : Bool) (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av u d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (u : Bool) (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av u c.1 c.2.2.2) && keepB u c.1 c.2.2.2 ka a && keepB u c.1 c.2.2.2 kb b &&
  (bif av u c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av u c.1 c.2.2.2 a && av u c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def same (u : Bool) (p : Nat × Nat) (v : Nat) : Bool :=
  bif u then Nat.testBit v p.1 == Nat.testBit v p.2 else !(Nat.testBit v p.1) || Nat.testBit v p.2
def sepEval (u : Bool) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  same u p z && (!ka || same u p a) && (!kb || same u p b) && rest.all (same u p)
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 256 && Nat.blt p.2 256 && T.testBit p.1 && !(T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (u : Bool) (_R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach u (roots.map observe) c.2.2.1 bank ∧ PS u f bank c.2.2.2 ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {u R T c k rest a b o ka kb} (hc : CutP u R T c) (ho : opOK u o = true)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval u k rest a b (nb o a b) ka kb c = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach u (roots.map observe) q bank' ∧ PS u f bank' c.2.2.2 ∧ Available u bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av u c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b ho hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply u bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available u bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem kid_mem {rest : List Nat} {a b z : Nat} {ka kb : Bool} {v : Sig} (hv : v ∈ kidW rest a b z ka kb) :
    ∃ x, v = W x ∧ (x = z ∨ (ka = true ∧ x = a) ∨ (kb = true ∧ x = b) ∨ x ∈ rest) := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ⟨z,rfl,Or.inl rfl⟩
  have low : ∀ v ∈ kept kb (W b) (rest.map W), ∃ x, v = W x ∧ ((kb = true ∧ x = b) ∨ x ∈ rest) := by
    intro v hv
    cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
      exact ⟨x,e.symm,Or.inr hx⟩
    · rcases List.mem_cons.mp hv with e | hv
      · exact ⟨b,e,Or.inl ⟨rfl,rfl⟩⟩
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        exact ⟨x,e.symm,Or.inr hx⟩
  cases ka
  · obtain ⟨x,h1,h2⟩ := low v hv
    exact ⟨x,h1,Or.inr (Or.inr h2)⟩
  · rcases List.mem_cons.mp hv with e | hv
    · exact ⟨a,e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · obtain ⟨x,h1,h2⟩ := low v hv
      exact ⟨x,h1,Or.inr (Or.inr h2)⟩
theorem sep_sound {u T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval u rest a b (nb o a b) ka kb p = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨p1,p2⟩,t1⟩,t2⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have all : ∀ v ∈ kidW rest a b (nb o a b) ka kb, ∃ x, v = W x ∧ same u p x = true := by
    intro v hv
    obtain ⟨x,rfl,hx⟩ := kid_mem hv
    refine ⟨x,rfl,?_⟩
    rcases hx with rfl | ⟨q,rfl⟩ | ⟨q,rfl⟩ | hx
    · exact h1
    · subst q; exact h2.resolve_left (by simp)
    · subst q; exact h3.resolve_left (by simp)
    · exact h4 x hx
  intro k' _ run
  cases u
  · obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W]; exact t1) (by rw [bit_W]; exact t2)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    rw [bit_W] at hp hn
    simp only [same,cond_false,Bool.or_eq_true,Bool.not_eq_true'] at hx
    rcases hx with hx | hx
    · rw [hx] at hp; exact Bool.noConfusion hp
    · rw [hx] at hn; exact Bool.noConfusion hn
  · obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W,t1,t2]; simp)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    apply hne
    rw [bit_W,bit_W]
    simpa only [same,cond_true,beq_iff_eq] using hx

-- A tight live set of a monotone run is a formula over distinct leaves, so its
-- leaves own disjoint rectangles of true rows against false rows.
def KWOwn (S : Finset Sig) (T : Sig) (owns : Sig → Row → Row → Prop) : Prop :=
  (∀ p n, bit p T = true → bit n T = false → ∃ v, owns v p n) ∧
  (∀ v p n, owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false) ∧
  (∀ v w p n, owns v p n → owns w p n → v = w) ∧
  (∀ v p n p' n', owns v p n → owns v p' n' → owns v p n')
abbrev KWRooms (S : Finset Sig) (T : Sig) := {o : Sig → Row → Row → Prop // KWOwn S T o}
def KWRooms.owns {S T} (H : KWRooms S T) : Sig → Row → Row → Prop := H.1
theorem KWRooms.total {S T} (H : KWRooms S T) : ∀ p n, bit p T = true → bit n T = false → ∃ v, H.owns v p n := H.2.1
theorem KWRooms.valid {S T} (H : KWRooms S T) {v p n} : H.owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false := H.2.2.1 v p n
theorem KWRooms.unique {S T} (H : KWRooms S T) {v w p n} : H.owns v p n → H.owns w p n → v = w := H.2.2.2.1 v w p n
theorem KWRooms.rect {S T} (H : KWRooms S T) {v p n p' n'} : H.owns v p n → H.owns v p' n' → H.owns v p n' := H.2.2.2.2 v p n p' n'
theorem kwLeaf (T : Sig) : Nonempty (KWRooms {T} T) := by
  refine ⟨⟨fun v p n => v = T ∧ bit p T = true ∧ bit n T = false,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    exact ⟨T,rfl,hp,hn⟩
  · rintro v p n ⟨rfl,hp,hn⟩
    exact ⟨by simp,hp,hn⟩
  · rintro v w p n ⟨rfl,_⟩ ⟨rfl,_⟩
    rfl
  · rintro v p n p' n' ⟨rfl,hp,_⟩ ⟨_,_,hn⟩
    exact ⟨rfl,hp,hn⟩
theorem kwFork {T : Sig} {U : Finset Sig} {a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1) (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U)
    (hz : bin d a b ∉ U) (H : KWRooms (insert (bin d a b) U) T) : Nonempty (KWRooms (insert a (insert b U)) T) := by
  classical
  let z := bin d a b
  let own : Sig → Row → Row → Prop := fun v p n => (v ∈ U ∧ H.owns v p n) ∨
    (H.owns z p n ∧ v = (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)))
  have pickU : ∀ (p n : Row), (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)) ∉ U := by
    intro p n
    split <;> split <;> assumption
  refine ⟨⟨own,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with e | hm
    · refine ⟨_,Or.inr ⟨?_,rfl⟩⟩
      rw [show v = z from e] at hv
      exact hv
    · exact ⟨v,Or.inl ⟨hm,hv⟩⟩
  · intro v p n h
    rcases h with ⟨hm,hv⟩ | ⟨hv,rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),(H.valid hv).2⟩
    · obtain ⟨_,hp,hn⟩ := H.valid hv
      change bit p (bin d a b) = true at hp
      change bit n (bin d a b) = false at hn
      rw [bit_bin] at hp hn
      rcases d01 with rfl | rfl
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,rfl⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,rfl⟩
    · exact H.unique hv hw
    · exact absurd (show z ∈ U by rw [←H.unique hv hw]; exact vU) hz
    · exact absurd (show z ∈ U by rw [←H.unique hw hv]; exact wU) hz
    · rfl
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,e1⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,e2⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact absurd (e2 ▸ vU) (pickU p' n')
    · exact absurd (e1 ▸ wU) (pickU p n)
    · refine Or.inr ⟨H.rect hv hw,?_⟩
      by_cases h : d=0
      · rw [if_pos h] at e2 ⊢
        exact e2
      · rw [if_neg h] at e1 ⊢
        exact e1
theorem kwTight {T : Sig} {k : Nat} {S : Finset Sig} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact kwLeaf T
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le a (insert b U)
    have le2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by
      rcases hd with h | ⟨h,_⟩
      · omega
      · exact Bool.noConfusion h
    exact kwFork d01 hab ha hb fresh H
def only (l : List Nat) (p n a : Nat) : Bool :=
  Nat.blt p 256 && Nat.blt n 256 && l.all (fun x => !(Nat.testBit x p) || Nat.testBit x n || Nat.beq x a)
abbrev KwD := Nat × Nat × Nat × Nat × Nat × Nat
def findW (l : List Nat) (p n : Nat) : Nat := (l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n))).getD 0
def kwOK (T : Nat) (q : KwD) : Bool :=
  T.testBit q.1 && T.testBit q.2.2.2.1 && T.testBit q.2.2.2.2.2 && !(T.testBit q.2.1) && !(T.testBit q.2.2.1) && !(T.testBit q.2.2.2.2.1)
def kwList (l : List Nat) (q : KwD) : Bool :=
  let a := findW l q.1 q.2.2.1
  let b := findW l q.1 q.2.2.2.2.1
  only l q.1 q.2.2.1 a && only l q.2.2.2.1 q.2.1 a &&
  (bif Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1 then !(Nat.testBit a q.1 && !(Nat.testBit a q.2.1))
   else only l q.1 q.2.2.2.2.1 b && only l q.2.2.2.2.2 q.2.1 b && !(Nat.beq a b))
theorem only_own {l : List Nat} {T p n a : Nat} (H : KWRooms ((l.map W).toFinset) (W T))
    (h : only l p n a = true) (tp : T.testBit p = true) (tn : T.testBit n = false) :
    ∃ (hp : p < 256) (hn : n < 256), H.owns (W a) ⟨p,hp⟩ ⟨n,hn⟩ := by
  simp only [only,Bool.and_eq_true,Nat.blt_eq,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨hp,hn⟩,hl⟩ := h
  refine ⟨hp,hn,?_⟩
  obtain ⟨v,hv⟩ := H.total ⟨p,hp⟩ ⟨n,hn⟩ (by rw [bit_W]; exact tp) (by rw [bit_W]; exact tn)
  obtain ⟨hm,h1,h2⟩ := H.valid hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  rw [bit_W] at h1 h2
  rcases hl x hx with (h | h) | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · rw [h] at h2; exact Bool.noConfusion h2
  · rw [Nat.eq_of_beq_eq_true h] at hv
    exact hv
set_option maxRecDepth 8192 in
theorem kw_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length = k+1) (lt : ∀ x ∈ l, x < 2^256) (q : KwD)
    (hT : kwOK T q = true) (h : kwList l q = true) : Impossible false (W T) k (l.map W).toFinset := by
  intro k' hk run
  have lb := live_size run
  rw [List.toFinset_card_of_nodup nd,List.length_map] at lb
  obtain ⟨H⟩ := kwTight run (by rw [List.toFinset_card_of_nodup nd,List.length_map]; omega)
  simp only [kwOK,Bool.and_eq_true,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨⟨⟨t1,t2⟩,t3⟩,t4⟩,t5⟩,t6⟩ := hT
  simp only [kwList,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  obtain ⟨hp,hna,o1⟩ := only_own H h1 t1 t5
  obtain ⟨hpa,hn,o2⟩ := only_own H h2 t2 t4
  have own := H.rect o1 o2
  cases hc : (Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1)
  · rw [hc,cond_false] at h3
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at h3
    obtain ⟨⟨h4,h5⟩,h6⟩ := h3
    obtain ⟨_,hnb,o3⟩ := only_own H h4 t1 t6
    obtain ⟨hpb,_,o4⟩ := only_own H h5 t3 t4
    have own' := H.rect o3 o4
    have ee := H.unique own own'
    have mem : ∀ {a : Nat}, W a ∈ (l.map W).toFinset → ∃ x ∈ l, W x = W a := by
      intro a ha
      obtain ⟨x,hx,e⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨x,hx,e⟩
    have fw : ∀ p n, findW l p n < 2^256 := by
      intro p n
      unfold findW
      cases hf : l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n)) with
      | none => exact Nat.two_pow_pos 256
      | some x => exact lt x (List.mem_of_find?_eq_some hf)
    have := W_inj (fw _ _) (fw _ _) ee
    rw [this,Nat.beq_refl] at h6
    exact Bool.noConfusion h6
  · rw [hc,cond_true] at h3
    have v := (H.valid own).2
    rw [bit_W,bit_W] at v
    rw [v.1,v.2] at h3
    exact Bool.noConfusion h3

-- Symmetry: exchanging neighbouring input variables.
def hiM : Nat → Nat
  | 0 => 0x2222222222222222222222222222222222222222222222222222222222222222
  | 1 => 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 2 => 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
  | 3 => 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
  | 4 => 0xffff000000000000ffff000000000000ffff000000000000ffff0000
  | 5 => 0xffffffff000000000000000000000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def loM : Nat → Nat
  | 0 => 0x4444444444444444444444444444444444444444444444444444444444444444
  | 1 => 0x3030303030303030303030303030303030303030303030303030303030303030
  | 2 => 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
  | 3 => 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
  | 4 => 0xffff000000000000ffff000000000000ffff000000000000ffff00000000
  | 5 => 0xffffffff000000000000000000000000ffffffff0000000000000000
  | _ => 0xffffffffffffffff00000000000000000000000000000000
def keM : Nat → Nat
  | 0 => 0x9999999999999999999999999999999999999999999999999999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
  | 2 => 0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f
  | 3 => 0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff
  | 4 => 0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff
  | 5 => 0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff
  | _ => 0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff
def shM : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | _ => 64
def swapN (i v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (keM i)) (Nat.shiftLeft (Nat.land v (hiM i)) (shM i))) (Nat.shiftRight (Nat.land v (loM i)) (shM i))
def sig (i : Nat) (r : Row) : Row :=
  if (hiM i).testBit r.val then Fin.ofNat 256 (r.val + shM i) else
    if (loM i).testBit r.val then Fin.ofNat 256 (r.val - shM i) else r
def swapFacts (i : Nat) (r : Row) : Prop :=
  ((keM i).testBit r.val = true ∧ (sig i r).val = r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ shM i ≤ r.val ∧ (sig i r).val = r.val - shM i ∧ (hiM i).testBit (r.val - shM i) = true ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ (sig i r).val = shM i + r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = true)
theorem swap_facts : ∀ (i : Fin 7) (r : Row), swapFacts i.val r ∧ sig i.val (sig i.val r) = r := by
  unfold swapFacts
  decide +kernel
theorem swap_ok (i : Nat) (hi : i < 7) (v : Nat) : W (swapN i v) = rename (sig i) (W v) := by
  apply bit_ext
  intro r
  rw [bit_W,bit_rename,bit_W]
  have e : (swapN i v).testBit r.val = (((v.testBit r.val && (keM i).testBit r.val) ||
      (decide (shM i ≤ r.val) && (v.testBit (r.val - shM i) && (hiM i).testBit (r.val - shM i)))) ||
      (v.testBit (shM i + r.val) && (loM i).testBit (shM i + r.val))) := by
    have s1 : (Nat.shiftLeft (Nat.land v (hiM i)) (shM i)).testBit r.val = (decide (shM i ≤ r.val) && (Nat.land v (hiM i)).testBit (r.val - shM i)) := by
      exact Nat.testBit_shiftLeft ..
    have s2 : (Nat.shiftRight (Nat.land v (loM i)) (shM i)).testBit r.val = (Nat.land v (loM i)).testBit (shM i + r.val) := by
      exact Nat.testBit_shiftRight ..
    unfold swapN
    rw [tb_lor,tb_lor,s1,s2,tb_land,tb_land,tb_land]
  rw [e]
  rcases (swap_facts ⟨i,hi⟩ r).1 with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4⟩
  · change (sig i r).val = r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
  · change (sig i r).val = r.val - shM i at h3
    rw [h3]
    simp only [] at h1 h2 h4 h5
    rw [h1,h4,h5,decide_eq_true h2]
    simp
  · change (sig i r).val = shM i + r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
def permN (l : List Nat) (v : Nat) : Nat := l.foldl (fun v i => swapN i v) v
def symOK (T : Nat) (l : List Nat) : Bool := l.all fun i => Nat.blt i 7 && Nat.beq (swapN i T) T
theorem perm_sound {u T k} (l : List Nat) (hT : symOK T l = true) (s : List Nat)
    (h : Impossible u (W T) k ((s.map (permN l)).map W).toFinset) : Impossible u (W T) k (s.map W).toFinset := by
  induction l generalizing s with
  | nil =>
    simpa [show (permN [] : Nat → Nat) = id from rfl] using h
  | cons i l ih =>
    simp only [symOK,List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hT
    obtain ⟨⟨hi,hs⟩,hl⟩ := hT
    have h' : Impossible u (W T) k ((s.map (swapN i)).map W).toFinset := by
      apply ih hl
      have : (s.map (swapN i)).map (permN l) = s.map (permN (i::l)) := by
        rw [List.map_map]
        rfl
      rw [this]
      exact h
    intro k' hk run
    have onto : Function.Surjective (sig i) := fun r => ⟨sig i r,(swap_facts ⟨i,hi⟩ r).2⟩
    have r2 := live_rename run (sig i) onto
    rw [←swap_ok i hi T,Nat.eq_of_beq_eq_true hs] at r2
    apply h' k' hk
    have : ((s.map (swapN i)).map W).toFinset = (s.map W).toFinset.image (rename (sig i)) := by
      ext v
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,exists_exists_and_eq_and,swap_ok i hi]
    rw [this]
    exact r2

abbrev StD := List Nat × List Nat × List Nat
def pick : List Nat → Nat → List Nat
  | [],_ => []
  | x::xs,m => bif Nat.beq (Nat.mod m 2) 1 then x :: pick xs (Nat.div m 2) else pick xs (Nat.div m 2)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (u : Bool) (Z : List SliceD) (c : Nat × List Nat) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool u (initPool s.1 s.2.2) c.2)
abbrev Tabs := List CutV × List (Nat × Nat) × List KwD × List (List Nat)
def Tabs.cuts (t : Tabs) : List CutV := t.1
def Tabs.seps (t : Tabs) : List (Nat × Nat) := t.2.1
def Tabs.kws (t : Tabs) : List KwD := t.2.2.1
def Tabs.perms (t : Tabs) : List (List Nat) := t.2.2.2
def sortN (l : List Nat) : List Nat := l.foldr ins []
theorem mem_sortN {v : Nat} {l : List Nat} : v ∈ sortN l ↔ v ∈ l := by
  induction l with
  | nil => simp [sortN]
  | cons x xs ih =>
    change v ∈ ins x (sortN xs) ↔ _
    rw [mem_ins,ih]
    simp
def ty (i n : Nat) : Bool := Nat.beq (Nat.mod i 4) n
def hintOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif ty i 0 then (match t.cuts[Nat.div i 4]? with
    | some c => cutEval u k rest a b z ka kb c
    | none => false)
  else bif ty i 1 then (match t.seps[Nat.div i 4]? with
    | some q => sepEval u rest a b z ka kb q
    | none => false)
  else bif ty i 2 then (match t.kws[Nat.div i 4]? with
    | some q => !u && Nat.beq (kidN rest a b z ka kb).length (k+1) && kwList (kidN rest a b z ka kb) q
    | none => false)
  else (match t.perms[Nat.div i 4]? with
    | some l => next.any (beqL (sortN ((kidN rest a b z ka kb).map (permN l))))
    | none => false)
def kidOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK u k next t rest a b z kk.1 kk.2)
def opsOf (u : Bool) : List Nat := bif u then [0,1,2,3] else [0,1]
def pairOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  (opsOf u).all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK u k next t p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^256)
  | x::y::l => Nat.blt x y && asc (y::l)
set_option maxRecDepth 8192 in
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^256 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK u k next t st.1) (pairs st.1) (st.2.2.map (pick st.2.1))
def levelOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK u T t k next)
abbrev TabsP (u : Bool) (R : List Nat) (T : Nat) (t : Tabs) : Prop :=
  (∀ c ∈ t.cuts, CutP u R T c) ∧ t.seps.all (sepOK T) = true ∧ t.kws.all (kwOK T) = true ∧ t.perms.all (symOK T) = true
theorem TabsP.c {u R T t} (h : TabsP u R T t) : ∀ c ∈ t.cuts, CutP u R T c := h.1
theorem TabsP.s {u R T t} (h : TabsP u R T t) : t.seps.all (sepOK T) = true := h.2.1
theorem TabsP.k {u R T t} (h : TabsP u R T t) : t.kws.all (kwOK T) = true := h.2.2.1
theorem TabsP.p {u R T t} (h : TabsP u R T t) : t.perms.all (symOK T) = true := h.2.2.2
def LevelN (u : Bool) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible u (W T) k (st.1.map W).toFinset
theorem cutsGood {u R T} {Z : List SliceD} {C : List (Nat × List Nat)} (hZ : ∀ s ∈ Z, SliceN u R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut u Z), CutP u R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS u f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=u) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

set_option maxRecDepth 8192 in
theorem stStep {u R T E t k next st} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hn : ∀ s ∈ next, Impossible u (W T) k (s.map W).toFinset)
    (h : stOK u T t k next st = true) : Impossible u (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have inOps : ∀ {o : Nat}, allowed u o → o ∈ opsOf u := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · have : o = 0 ∨ o = 1 := by omega
        simpa [opsOf] using this
      · exact Bool.noConfusion h
    · have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by rcases h with h | ⟨_,h⟩ <;> omega
      simpa [opsOf] using this
  have opk : ∀ {o : Nat}, allowed u o → opOK u o = true := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · simpa only [opOK,Bool.false_or,Nat.blt_eq] using h
      · exact Bool.noConfusion h
    · rfl
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  -- one unordered pair serves both orders
  have core : ∀ (o : Nat) (ja jb : Bool), allowed u o → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible u (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (inOps ho4)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with hk | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      have sub : ∀ x ∈ kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb, x < 2^256 := by
        intro x hx
        have hx' : x = nb o p.1 p.2.1 ∨ x ∈ st.1 := by
          unfold kidN at hx
          rw [mem_ins] at hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · right
            rw [pm]
            cases ja <;> cases jb <;> simp only [cond_true,cond_false,mem_ins] at hx <;> tauto
        rcases hx' with rfl | hx'
        · have l1 : p.1 < 2^256 := lt _ ((pm _).mpr (Or.inl rfl))
          have l2 : p.2.1 < 2^256 := lt _ ((pm _).mpr (Or.inr (Or.inl rfl)))
          have la : Nat.land p.1 p.2.1 < 2^256 := Nat.lt_of_le_of_lt (Nat.and_le_left) l1
          unfold nb
          cases Nat.beq o 0 <;> cases Nat.beq o 1 <;> cases Nat.beq o 2 <;>
            first | exact la | exact Nat.or_lt_two_pow l1 l2 | exact Nat.xor_lt_two_pow l1 la | exact Nat.xor_lt_two_pow l2 la
        · exact lt x hx'
      cases h1 : ty i 0
      · rw [h1,cond_false] at hi
        cases h2 : ty i 1
        · rw [h2,cond_false] at hi
          cases h3 : ty i 2
          · rw [h3,cond_false] at hi
            cases hg : t.perms[Nat.div i 4]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some l =>
              rw [hg] at hi
              obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hi
              rw [←kid_fin]
              apply perm_sound l (List.all_eq_true.mp ht.p l (List.mem_of_getElem? hg))
              have : (((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map (permN l)).map W).toFinset = (s.map W).toFinset := by
                rw [←beqL_ok e]
                ext v
                simp only [List.mem_toFinset,List.mem_map,mem_sortN]
              rw [this]
              exact hn s hs'
          · rw [h3,cond_true] at hi
            cases hg : t.kws[Nat.div i 4]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some q =>
              rw [hg] at hi
              simp only [Bool.and_eq_true,Bool.not_eq_true'] at hi
              obtain ⟨⟨hu,hlen⟩,hkw⟩ := hi
              rw [←kid_fin]
              have sz := Nat.eq_of_beq_eq_true hlen
              have nd' : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).Nodup := by
                apply List.dedup_eq_self.mp
                apply (List.dedup_sublist _).eq_of_length
                have c1 : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).toFinset.card = (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).length := by
                  rw [kid_fin,List.toFinset_card_of_nodup nk]
                rw [List.card_toFinset] at c1
                rw [c1,List.length_map]
                have il : ∀ (z : Nat) (l : List Nat), (ins z l).length = l.length + 1 := by
                  intro z l
                  induction l with
                  | nil => rfl
                  | cons x xs ih =>
                    unfold ins
                    cases Nat.ble z x
                    · rw [cond_false,List.length_cons,ih,List.length_cons]
                    · rfl
                unfold kidN kidW
                cases ja <;> cases jb <;> simp [kept,il]
              subst hu
              exact kw_sound nd' sz sub q (List.all_eq_true.mp ht.k q (List.mem_of_getElem? hg)) hkw
        · rw [h2,cond_true] at hi
          cases hg : t.seps[Nat.div i 4]? with
          | none => rw [hg] at hi; exact Bool.noConfusion hi
          | some q =>
            rw [hg] at hi
            exact sep_sound (List.all_eq_true.mp ht.s q (List.mem_of_getElem? hg)) hi
      · rw [h1,cond_true] at hi
        cases hg : t.cuts[Nat.div i 4]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (ht.c q (List.mem_of_getElem? hg)) (opk ho4) nk hi
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have r := core (flipOp d) kb ka hfl.1 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {u R T E t k D' D} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hI : LevelN u T k D') (h : levelOK u T t k (D'.map Prod.fst) D = true) : LevelN u T (k+1) D := by
  intro st hst
  refine stStep hB ht ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {u : Bool} {T : Nat} {t : Tabs} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK u T t k next ((D.drop (i*c)).take c) = true) : levelOK u T t k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : LevelN u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this


def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.or, [3, 12]⟩,
    ⟨.and, [8, 4]⟩,
    ⟨.and, [9, 5]⟩,
    ⟨.and, [10, 6]⟩,
    ⟨.and, [13, 7]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [18, 16]⟩,
    ⟨.or, [19, 17]⟩], 20⟩
theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.gates.length = 13 := rfl
def pw0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def pw1 : Nat := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def pw2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def pw3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def pw4 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def pw5 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def pw6 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def pw7 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def pw8 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def pw9 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def pw10 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def pw11 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def pw12 : Nat := 0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc
def pw13 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
def pw14 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0
def pw15 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc
def pw16 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
def pw17 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def pw18 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def pw19 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def pw20 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def pw21 : Nat := 0x2222222222222222222222222222222222222222222222222222222222222222
def pw22 : Nat := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa
def pw23 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def pw24 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa
def pw25 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
def pw26 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa
def pw27 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa
def pw28 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0
def pw29 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00
def pw30 : Nat := 0xfefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefe
def pw31 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
def pw32 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee
def pw33 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee
def pw34 : Nat := 0xeeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee
def pw35 : Nat := 0xf2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2
def pw36 : Nat := 0x202020202020202020202020202020202020202020202020202020202020202
def pw37 : Nat := 0xff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22
def pw38 : Nat := 0x22002200220022002200220022002200220022002200220022002200220022
def pw39 : Nat := 0x3232323232323232323232323232323232323232323232323232323232323232
def pw40 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa
def pw41 : Nat := 0xfffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafa
def pw42 : Nat := 0xfafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa
def pw43 : Nat := 0xcececececececececececececececececececececececececececececececece
def pw44 : Nat := 0xffff0a0affff0a0affff0a0affff0a0affff0a0affff0a0affff0a0affff0a0a
def pw45 : Nat := 0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a
def pw46 : Nat := 0x3322332233223322332233223322332233223322332233223322332233223322
def pw47 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
def pw48 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaa
def pw49 : Nat := 0xffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa
def pw50 : Nat := 0xcceecceecceecceecceecceecceecceecceecceecceecceecceecceecceeccee
def pw51 : Nat := 0xffff00aaffff00aaffff00aaffff00aaffff00aaffff00aaffff00aaffff00aa
def pw52 : Nat := 0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa
def pw53 : Nat := 0x3333222233332222333322223333222233332222333322223333222233332222
def pw54 : Nat := 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
def pw55 : Nat := 0xff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa
def pw56 : Nat := 0xf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafa
def pw57 : Nat := 0xff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaa
def pw58 : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def pw59 : Nat := 0x5454545454545454545454545454545454545454545454545454545454545454
def pw60 : Nat := 0xaa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88
def pw61 : Nat := 0x5544554455445544554455445544554455445544554455445544554455445544
def pw62 : Nat := 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0
def pw63 : Nat := 0x5555505055555050555550505555505055555050555550505555505055555050
def pw64 : Nat := 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00
def pw65 : Nat := 0x5555550055555500555555005555550055555500555555005555550055555500
def pw66 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe
def pw67 : Nat := 0xfefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe
def pw68 : Nat := 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e
def pw69 : Nat := 0xffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee
def pw70 : Nat := 0xf200f200f200f200f200f200f200f200f200f200f200f200f200f200f200f2
def pw71 : Nat := 0xf020f020f020f020f020f020f020f020f020f020f020f020f020f020f020f02
def pw72 : Nat := 0x3333323233333232333332323333323233333232333332323333323233333232
def pw73 : Nat := 0xff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa
def pw74 : Nat := 0xcece0000cece0000cece0000cece0000cece0000cece0000cece0000cece
def pw75 : Nat := 0x3333020233330202333302023333020233330202333302023333020233330202
def pw76 : Nat := 0x3333332233333322333333223333332233333322333333223333332233333322
def pw77 : Nat := 0xf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a
def pw78 : Nat := 0xccee0000ccee0000ccee0000ccee0000ccee0000ccee0000ccee0000ccee
def pw79 : Nat := 0x3333002233330022333300223333002233330022333300223333002233330022
def pw80 : Nat := 0xf000fa00f000fa00f000fa00f000fa00f000fa00f000fa00f000fa00f000fa
def pw81 : Nat := 0xf000f0a0f000f0a0f000f0a0f000f0a0f000f0a0f000f0a0f000f0a0f000f0a
def pw82 : Nat := 0xffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8
def pw83 : Nat := 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8
def pw84 : Nat := 0xfaf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8
def pw85 : Nat := 0xffffaa88ffffaa88ffffaa88ffffaa88ffffaa88ffffaa88ffffaa88ffffaa88
def pw86 : Nat := 0xeeeeececeeeeececeeeeececeeeeececeeeeececeeeeececeeeeececeeeeecec
def pw87 : Nat := 0xffaaffa0ffaaffa0ffaaffa0ffaaffa0ffaaffa0ffaaffa0ffaaffa0ffaaffa0
def pw88 : Nat := 0xeeeeeecceeeeeecceeeeeecceeeeeecceeeeeecceeeeeecceeeeeecceeeeeecc
def pw89 : Nat := 0xfafafaf0fafafaf0fafafaf0fafafaf0fafafaf0fafafaf0fafafaf0fafafaf0
def pw90 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def pw91 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def pw92 : Nat := 0x1111111100000000111111110000000011111111000000001111111100000000
def pw93 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
def pw94 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def pw95 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
def pw96 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def pw97 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def pw98 : Nat := 0x5050505050505050505050505050505050505050505050505050505050505050
def pw99 : Nat := 0x3030303030303030303030303030303030303030303030303030303030303030
def pw100 : Nat := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc
def pw101 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
def pw102 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def pw103 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0
def pw104 : Nat := 0xeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeee
def pw105 : Nat := 0xdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdc
def pw106 : Nat := 0xffffffff50505050ffffffff50505050ffffffff50505050ffffffff50505050
def pw107 : Nat := 0xbabababababababababababababababababababababababababababababababa
def pw108 : Nat := 0xffffffff30303030ffffffff30303030ffffffff30303030ffffffff30303030
def pw109 : Nat := 0x5555444455554444555544445555444455554444555544445555444455554444
def pw110 : Nat := 0xfff00000fff00000fff00000fff00000fff00000fff00000fff00000fff0
def pw111 : Nat := 0xaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafa
def pw112 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfc
def pw113 : Nat := 0xffffffff00f000f0ffffffff00f000f0ffffffff00f000f0ffffffff00f000f0
def pw114 : Nat := 0xff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f0
def pw115 : Nat := 0xaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafa
def pw116 : Nat := 0xccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfc
def pw117 : Nat := 0xffffffff0000f0f0ffffffff0000f0f0ffffffff0000f0f0ffffffff0000f0f0
def pw118 : Nat := 0xf0f0f0f0fefefefef0f0f0f0fefefefef0f0f0f0fefefefef0f0f0f0fefefefe
def pw119 : Nat := 0xeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefe
def pw120 : Nat := 0xeeeefefeeeeefefeeeeefefeeeeefefeeeeefefeeeeefefeeeeefefeeeeefefe
def pw121 : Nat := 0x2232223222322232223222322232223222322232223222322232223222322232
def pw122 : Nat := 0x4454445444544454445444544454445444544454445444544454445444544454
def pw123 : Nat := 0x2222323222223232222232322222323222223232222232322222323222223232
def pw124 : Nat := 0x4444545444445454444454544444545444445454444454544444545444445454
def pw125 : Nat := 0xf000f0eefeeefe00f000f0eefeeefe00f000f0eefeeefe00f000f0eefeeefe
def pw126 : Nat := 0xf0f0eeeefefe0000f0f0eeeefefe0000f0f0eeeefefe0000f0f0eeeefefe
def pw127 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def pw128 : Nat := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def p1_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def p1_R : List Nat := [0, 1, 2]
def p1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
def p1_Z : List SliceD := []
theorem p1_Y : ∀ s ∈ p1_Z, SliceN true p1_R p1_T s := by
  intro s h
  cases h
def p1_C : List (Nat × List Nat) := []
def p1_t : Tabs := (p1_C.map (mkCut true p1_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1)],[],[[]])
theorem p1_W : TabsP true p1_R p1_T p1_t := ⟨cutsGood p1_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p1_D3 : List StD := [
([pw0,pw1,pw2],[1,5,9,13,17,21],[15,53,58])]
def p1_D2 : List StD := []
theorem p1_I2 : LevelN true p1_T 2 p1_D2 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p1_C3x0 : levelOK true p1_T p1_t 2 (p1_D2.map Prod.fst) ((p1_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p1_I3 : LevelN true p1_T 3 p1_D3 := levelStep p1_B p1_W p1_I2 (chunks 32 p1_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p1_C3x0
  ))
theorem p1_L : LowN true p1_R p1_T 4 := lowSearch p1_B p1_I3 (by decide +kernel)
def p2_T : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8
def p2_R : List Nat := [0, 1, 2, 3]
def p2_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
def p2_Z : List SliceD := []
theorem p2_Y : ∀ s ∈ p2_Z, SliceN true p2_R p2_T s := by
  intro s h
  cases h
def p2_C : List (Nat × List Nat) := []
def p2_t : Tabs := (p2_C.map (mkCut true p2_Z),[(6,4),(3,1),(3,2),(9,12),(6,2),(9,1),(9,0),(6,12),(9,5)],[],[[]])
theorem p2_W : TabsP true p2_R p2_T p2_t := ⟨cutsGood p2_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p2_D3 : List StD := [
([pw0,pw1,pw2,pw3],[1,21,5,9,17,13,25,29,33],[5,56,74,5,131,274])]
def p2_D2 : List StD := []
theorem p2_I2 : LevelN true p2_T 2 p2_D2 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p2_C3x0 : levelOK true p2_T p2_t 2 (p2_D2.map Prod.fst) ((p2_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p2_I3 : LevelN true p2_T 3 p2_D3 := levelStep p2_B p2_W p2_I2 (chunks 32 p2_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p2_C3x0
  ))
theorem p2_L : LowN true p2_R p2_T 4 := lowSearch p2_B p2_I3 (by decide +kernel)
def p3_T : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def p3_R : List Nat := [0, 1, 2, 3]
def p3_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
def p3_Z : List SliceD := [(pw4,4,[1, 2, 3])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN true p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),by simp⟩
def p3_C : List (Nat × List Nat) := [(0,[])]
def p3_t : Tabs := (p3_C.map (mkCut true p3_Z),[(1,0),(6,4),(3,2)],[],[[]])
theorem p3_W : TabsP true p3_R p3_T p3_t := ⟨cutsGood p3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D4 : List StD := [
([pw0,pw1,pw2,pw3],[0,1,5,9],[15,3,3,1,5,1])]
def p3_D3 : List StD := []
theorem p3_I3 : LevelN true p3_T 3 p3_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_C4x0 : levelOK true p3_T p3_t 3 (p3_D3.map Prod.fst) ((p3_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I4 : LevelN true p3_T 4 p3_D4 := levelStep p3_B p3_W p3_I3 (chunks 32 p3_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C4x0
  ))
theorem p3_L : LowN true p3_R p3_T 5 := lowSearch p3_B p3_I4 (by decide +kernel)
def p4_T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8
def p4_R : List Nat := [0, 1, 2, 3]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
def p4_Z : List SliceD := [(pw5,4,[0, 1, 2])]
theorem p4_Y : ∀ s ∈ p4_Z, SliceN true p4_R p4_T s := by
  unfold p4_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p4_B p1_B p1_L (by decide +kernel),by simp⟩
def p4_C : List (Nat × List Nat) := [(0,[])]
def p4_t : Tabs := (p4_C.map (mkCut true p4_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1)],[],[[]])
theorem p4_W : TabsP true p4_R p4_T p4_t := ⟨cutsGood p4_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p4_D4 : List StD := [
([pw0,pw1,pw2,pw3],[0,1,5,17,9,13,21],[54,90,3,108,5,9])]
def p4_D3 : List StD := []
theorem p4_I3 : LevelN true p4_T 3 p4_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_C4x0 : levelOK true p4_T p4_t 3 (p4_D3.map Prod.fst) ((p4_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p4_I4 : LevelN true p4_T 4 p4_D4 := levelStep p4_B p4_W p4_I3 (chunks 32 p4_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_C4x0
  ))
theorem p4_L : LowN true p4_R p4_T 5 := lowSearch p4_B p4_I4 (by decide +kernel)
def p5_T : Nat := 0xfeeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8
def p5_R : List Nat := [0, 1, 2, 3, 4]
def p5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,2,10),(4,1,17)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
def p5_Z : List SliceD := [(pw6,4,[1, 2, 3]),(pw7,4,[0, 1, 3, 4]),(pw5,4,[0, 1, 2, 4]),(pw8,5,[0, 1, 2, 3]),(pw9,5,[1, 2, 3, 0])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN true p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p5_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p5_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p5_B p2_B p2_L (by decide +kernel),mkSlice (w:=16) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel),by simp⟩
def p5_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p5_t : Tabs := (p5_C.map (mkCut true p5_Z),[(3,2),(17,16),(21,20),(25,24),(12,8),(6,4),(6,2),(12,4),(10,8),(10,2),(7,4),(12,5),(3,5),(3,1),(6,20),(17,1),(6,18),(21,5),(17,9),(12,9),(6,0),(17,5),(11,8),(3,9),(10,24),(10,18),(25,9),(10,0),(12,20),(12,0),(12,1),(17,0),(10,16),(22,2),(7,0),(6,16),(12,16)],[],[[]])
theorem p5_W : TabsP true p5_R p5_T p5_t := ⟨cutsGood p5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D6 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[0,1,12,3,4,8,5,17,25,29,9,13,21,33,37],[67,1027,2051,67,4504,25128,5,952,5,5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D5 : List StD := [
([pw0,pw1,pw2,pw10,pw3,pw8],[1,37,21,61,9,25,29,8,5,17,41,45,49,53,57,65,69,73,3],[1029,17,257,2051,17,4132,8192,70,16396,512,66,32808,262274,65544,131082]),
([pw11,pw0,pw1,pw2,pw3,pw8],[5,29,61,1,17,37,21,12,16,25,45,53,57,73,77,81,85],[9,2048,512,34,388,9,16401,1027,9,32848,34,4164,34,65556,8198]),
([pw0,pw1,pw2,pw3,pw12,pw8],[1,25,33,61,13,17,37,4,5,29,53,77,85,89,93,97,101,105,3],[8197,2051,17,257,17,38,16452,1024,32780,34,262274,4106,512,65608,131080]),
([pw13,pw0,pw1,pw2,pw3,pw8],[5,17,61,1,25,29,33,12,16,37,45,53,73,77,85,97,109],[9,2048,18,512,388,9,8195,1057,9,18,65632,32836,18,16390,4132]),
([pw0,pw1,pw2,pw3,pw14,pw8],[21,1,61,29,53,4,9,17,69,25,33,45,57,77,113],[17,8322,2058,66,66,17,1025,17,4101,40,512,388,32,16396,260])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D4 : List StD := [
([pw15,pw0,pw1,pw2,pw8],[1,25,37,69,109,61,117,41,45,53,121,125,129],[261,532,70,44,145,1027,2057,82,4120,42]),
([pw16,pw0,pw1,pw3,pw8],[1,25,37,61,81,117,53,77,121,125,133,137,141,145],[131,82,38,1034,2065,261,521,52,4120,8204])]
def p5_D3 : List StD := []
theorem p5_I3 : LevelN true p5_T 3 p5_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_C4x0 : levelOK true p5_T p5_t 3 (p5_D3.map Prod.fst) ((p5_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I4 : LevelN true p5_T 4 p5_D4 := levelStep p5_B p5_W p5_I3 (chunks 32 p5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_C5x0 : levelOK true p5_T p5_t 4 (p5_D4.map Prod.fst) ((p5_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I5 : LevelN true p5_T 5 p5_D5 := levelStep p5_B p5_W p5_I4 (chunks 32 p5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_C6x0 : levelOK true p5_T p5_t 5 (p5_D5.map Prod.fst) ((p5_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I6 : LevelN true p5_T 6 p5_D6 := levelStep p5_B p5_W p5_I5 (chunks 32 p5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C6x0
  ))
theorem p5_L : LowN true p5_R p5_T 7 := lowSearch p5_B p5_I6 (by decide +kernel)
def p6_T : Nat := 0xfeeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8
def p6_R : List Nat := [0, 1, 2, 3, 4]
def p6_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
def p6_Z : List SliceD := [(pw17,4,[0, 2, 3, 4]),(pw6,4,[1, 2, 3]),(pw7,4,[0, 1, 3, 4]),(pw5,5,[0, 1, 2, 4]),(pw8,5,[0, 1, 2, 3])]
theorem p6_Y : ∀ s ∈ p6_Z, SliceN true p6_R p6_T s := by
  unfold p6_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p6_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p6_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p6_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p6_B p4_B p4_L (by decide +kernel),mkSlice (w:=16) p6_B p3_B p3_L (by decide +kernel),by simp⟩
def p6_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p6_t : Tabs := (p6_C.map (mkCut true p6_Z),[(6,4),(3,2),(3,0),(5,4),(25,24),(3,1),(6,2),(10,2),(10,0),(12,4),(17,16),(17,24),(6,20),(6,18),(17,1),(17,9),(5,1),(26,2),(10,16),(12,16)],[],[[]])
theorem p6_W : TabsP true p6_R p6_T p6_t := ⟨cutsGood p6_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p6_D6 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[4,0,1,5,12,16,8,17,25,29,9,13,21,33,37,3],[1039,2057,137,137,37190,8726,39,17232,33,49])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p6_D5 : List StD := [
([pw0,pw1,pw2,pw10,pw3,pw8],[13,29,0,57,5,25,41,4,12,16,1,21,37,45,49,53,61,3],[17,17,65,8195,65,36,2048,6,17412,4,4098,32808,131330,648,65546])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p6_D4 : List StD := [
([pw15,pw0,pw1,pw2,pw8],[5,29,25,33,41,57,1,13,21,65,69,73,77],[19,266,518,1058,17,129,17,76,2088,4132])]
def p6_D3 : List StD := []
theorem p6_I3 : LevelN true p6_T 3 p6_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_C4x0 : levelOK true p6_T p6_t 3 (p6_D3.map Prod.fst) ((p6_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p6_I4 : LevelN true p6_T 4 p6_D4 := levelStep p6_B p6_W p6_I3 (chunks 32 p6_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_C5x0 : levelOK true p6_T p6_t 4 (p6_D4.map Prod.fst) ((p6_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p6_I5 : LevelN true p6_T 5 p6_D5 := levelStep p6_B p6_W p6_I4 (chunks 32 p6_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_C6x0 : levelOK true p6_T p6_t 5 (p6_D5.map Prod.fst) ((p6_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p6_I6 : LevelN true p6_T 6 p6_D6 := levelStep p6_B p6_W p6_I5 (chunks 32 p6_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_C6x0
  ))
theorem p6_L : LowN true p6_R p6_T 7 := lowSearch p6_B p6_I6 (by decide +kernel)
def p7_T : Nat := 0xfeeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8
def p7_R : List Nat := [0, 1, 2, 3, 4]
def p7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
def p7_Z : List SliceD := [(pw17,5,[0, 2, 3, 4]),(pw7,5,[0, 1, 4, 3]),(pw5,5,[0, 1, 4, 2]),(pw9,5,[0, 2, 3, 1]),(pw18,4,[0, 2, 3]),(pw19,4,[0, 1, 4])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN true p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),by simp⟩
def p7_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(0,[384]),(0,[386]),(0,[389]),(0,[393])]
def p7_t : Tabs := (p7_C.map (mkCut true p7_Z),[(18,16),(3,2),(3,1),(12,8),(5,4),(5,1),(12,4),(9,8),(9,1),(18,2),(17,16),(17,1),(22,20),(14,10),(26,24),(14,6),(28,24),(22,6),(28,20),(26,10),(7,6),(11,10),(21,20),(25,24),(12,6),(18,6),(18,10),(12,10),(18,20),(12,20),(18,24),(12,24),(5,6),(18,0),(3,6),(5,2),(9,10),(11,2),(7,2),(3,10),(9,2),(17,0),(22,4),(26,8),(7,1),(14,8),(14,4),(11,1),(5,0),(12,0),(17,20),(11,6),(7,4),(5,20),(17,4),(28,16),(9,0),(14,2),(7,10),(17,24),(11,8),(21,16),(9,24),(17,8),(3,0),(22,16),(26,16),(12,16),(12,2),(11,0),(18,8),(3,4),(18,4),(7,0),(3,8),(9,16),(5,16),(5,8),(3,16),(9,4),(17,2)],[],[[]])
theorem p7_W : TabsP true p7_R p7_T p7_t := ⟨cutsGood p7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D7 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[3,0,4,1,8,12,13,25,9,21,37,16,20,5,17,29,33,41,45,49,53,57,61,65,69,73,77],[8459,16965,98449,394273,1572879,6291483,3338,4804,25165925,100663473])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D6 : List StD := [
([pw0,pw1,pw20,pw2,pw3,pw8],[3,0,16,37,5,13,25,21,33,20,9,1,45,53,61,69,77,81,85],[19,2,131248,262480,4124,2051,9219,17411,14,673,833,13,480,32812,65612]),
([pw21,pw0,pw1,pw2,pw3,pw8],[0,16,13,25,45,3,5,21,33,37,20,49,1,9,57,69,77,81,85],[1,8225,1188,1320,530,97,131268,262472,530,6145,18433,515,396,32790,65562]),
([pw0,pw1,pw2,pw22,pw3,pw8],[20,3,1,33,17,9,37,45,21,25,0,16,13,49,61,69,73,81,89],[131124,19,1,537,262352,8455,1062,16397,228,4099,521,33027,11,2242,65545]),
([pw23,pw0,pw1,pw2,pw3,pw8],[20,33,3,1,9,17,25,37,45,53,0,16,13,21,61,65,73,81,89],[1,1052,8197,67,2436,131128,37,67,262560,4609,16387,408,67,33281,65539]),
([pw0,pw1,pw2,pw3,pw24,pw8],[20,3,1,13,29,9,37,45,21,33,0,16,25,53,57,65,77,85,93],[131124,281,19,1,262352,8205,16903,1062,228,265,11,32777,4099,66051,2242]),
([pw25,pw0,pw1,pw2,pw3,pw8],[20,21,3,1,9,13,29,37,45,61,0,16,25,33,53,65,73,85,93],[1,1052,35,8197,2436,131160,35,69,262592,16387,4609,408,35,32771,66049]),
([pw0,pw1,pw2,pw3,pw8,pw26],[16,3,1,41,13,21,25,33,20,9,45,37,49,57,65,73,89,93],[525,65592,131272,11,1,4101,8197,517,7,240,17411,306,33795,450,2051]),
([pw27,pw0,pw1,pw2,pw3,pw8],[16,9,3,1,13,21,25,33,41,20,69,37,45,49,57,77,89,93],[1,11,564,708,4101,11,65840,131520,261,8195,16387,11,240,3073,33793]),
([pw0,pw1,pw2,pw10,pw3,pw8],[20,0,17,16,25,33,37,49,53,3,5,45,29,41,97,101,105],[1670,1797,4612,53,10308,3,1,16515,202,2,305,33033,49,2120,65545]),
([pw0,pw1,pw2,pw3,pw12,pw8],[20,0,17,16,13,5,21,37,57,3,45,61,29,41,101,105,109],[806,116,6661,548,9348,65795,3,1,394,81,81,16409,2,34825,1160]),
([pw0,pw1,pw2,pw3,pw8,pw28],[20,16,1,17,5,9,25,33,65,3,41,69,97,113,117],[60,793,201,3594,536,8455,4103,38,38,449,3,2,16387,193,1]),
([pw0,pw1,pw2,pw3,pw8,pw29],[16,20,1,13,17,9,21,3,5,29,73,41,77,109,121,125],[308,344,1682,6289,656,8207,17415,37,37,74,32779,74,3,1,2])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D5 : List StD := [
([pw21,pw0,pw20,pw2,pw3,pw8],[21,45,13,33,9,25,0,37,16,101,105,129,133],[2048,64,21,56,146,64,5,40,130,5,40,4354,5,515,1034]),
([pw0,pw20,pw2,pw10,pw3,pw8],[33,45,5,9,49,25,53,16,37,20,17,101,105,109,137,141,145,149],[1024,49156,65548,131077,262,8272,536,49,146,128,97,2114,41,266,4099]),
([pw0,pw20,pw2,pw3,pw12,pw8],[21,45,5,9,13,57,16,37,61,20,17,97,101,105,129,153,157,161],[1024,32773,196612,16396,134,17,2336,552,98,17,17,4099,64,8450,138]),
([pw0,pw1,pw2,pw30,pw3,pw8],[33,45,9,17,5,21,37,3,16,20,1,13,25,29,97,101,105,109,149],[28,24,8192,262153,74,131108,1024,16389,70,2048,4097,32802,641,386,65539]),
([pw31,pw0,pw1,pw2,pw3,pw8],[17,25,49,69,5,9,33,45,21,97,105],[17,36,256,66,136,17,17,67,137,36,518,36,66,136,1034]),
([pw0,pw1,pw2,pw3,pw32,pw8],[21,45,5,9,33,37,3,16,20,1,13,17,25,29,97,101,105,109,129,153],[262156,524293,8212,2048,38,131081,16408,512,42,1025,321,32771,4096,65554,194]),
([pw33,pw0,pw1,pw2,pw3,pw8],[13,29,57,77,5,9,21,45,33,101,109],[18,36,65,256,136,18,67,18,138,1029,36,36,65,521,136]),
([pw34,pw0,pw1,pw20,pw2,pw3],[21,5,13,33,37,25,45,24,9,53,61,129,133,165],[82,80,128,21,56,2306,8192,7,42,4096,513,1032,5,40,5]),
([pw34,pw0,pw1,pw2,pw3],[13,25,37,133,165,21,33,5,9,45,53,61,69,77,81,85,169,173],[660,780,4133,8262,408,16433,32850,66569,133130,99]),
([pw0,pw1,pw2,pw35,pw3,pw8],[17,33,45,5,37,49,20,1,9,13,21,25,69,97,105,149,177,3],[9,9,9,32771,21,66592,416,8226,20,512,2050,4100,131138,20,16390]),
([pw36,pw0,pw1,pw2,pw3,pw8],[25,37,33,45,5,13,17,9,21,29,97,101,105,109,181,185],[512,128,256,5,10,80,80,5,10,24608,33793,10,5,2082,4099]),
([pw0,pw1,pw2,pw3,pw37,pw8],[21,29,45,5,37,57,20,1,9,13,25,33,77,101,109,153,181,189,3],[10,32771,10,10,22,81921,133152,416,20,513,262209,8197,1024,4100,20]),
([pw38,pw0,pw1,pw2,pw3,pw8],[13,37,21,45,5,25,29,9,17,33,97,101,105,109,181,185],[256,128,5,512,10,80,5,80,10,24577,33824,10,5,2051,4130]),
([pw23,pw0,pw1,pw22,pw3,pw8],[9,33,1,45,21,37,25,0,20,97,105,137,193,197],[2048,21,128,82,56,5,4096,66,40,5,515,5,8450,40,1034]),
([pw0,pw1,pw22,pw10,pw3,pw8],[33,45,17,21,37,53,49,0,20,5,9,25,97,105,109,137,201,205],[32772,512,65548,131077,22,16480,1024,4161,18,168,289,18,2057,26,8195]),
([pw39,pw0,pw1,pw2,pw3,pw8],[5,37,53,61,17,21,33,45,9,101,105],[17,256,36,72,130,17,17,73,131,36,72,130,36,518,1034]),
([pw0,pw1,pw22,pw3,pw8,pw28],[9,33,17,20,1,21,25,65,16,5,69,97,101,117,137,209,213,217,221],[32773,512,70,196612,16420,17,2051,17,17,262154,5248,416,8202,66,8]),
([pw40,pw0,pw1,pw2,pw22,pw8],[9,20,17,25,37,45,33,1,49,69,97,197,209],[76,1033,72,2,56,4101,6,2,52,257,129,49,2048,514,48]),
([pw40,pw0,pw1,pw2,pw8],[1,25,37,197,225,9,45,17,21,33,49,61,69,73,81,89,221,229],[658,2083,778,8262,16433,408,32852,132105,101,69644]),
([pw0,pw1,pw2,pw3,pw8,pw41],[9,33,17,21,45,25,3,0,20,1,5,13,37,41,97,101,113,117,137,209],[524293,262156,38,8212,1024,65545,16387,513,193,42,32792,2048,131090,322,4096]),
([pw42,pw0,pw1,pw2,pw3,pw8],[1,41,65,73,9,17,21,33,45,97,113],[34,17,68,136,256,19,34,138,34,1029,521,17,68,68,136]),
([pw0,pw1,pw43,pw2,pw3,pw8],[17,33,45,9,53,5,37,61,16,1,13,21,25,101,105,149,177,3],[41,33,33,32771,69,512,65560,138,76,3088,4098,131332,146,8212,16390]),
([pw0,pw1,pw2,pw3,pw8,pw44],[9,13,17,33,25,41,65,0,1,37,45,73,97,109,193,209,3],[32773,16390,28,1060,36,8195,4105,257,65665,26,66,66,2056,24,512]),
([pw45,pw0,pw1,pw2,pw3,pw8],[1,25,9,13,33,17,37,5,21,41,45,97,101,105,109,193],[128,5,256,18,1024,5,32808,18,544,16393,2051,5,18,4168,8258]),
([pw25,pw0,pw1,pw2,pw24,pw8],[9,21,1,45,33,37,13,0,20,101,109,157,197,225],[2048,21,82,128,56,5,66,8192,40,1027,5,5,4354,522,40]),
([pw0,pw1,pw2,pw24,pw12,pw8],[21,45,29,37,33,61,0,20,5,9,13,57,97,101,109,157,181,233,237],[32772,131077,256,262164,14,81921,6176,512,10,161,1025,8195,112,10,26]),
([pw46,pw0,pw1,pw2,pw3,pw8],[5,37,53,21,29,45,61,33,9,101,105],[17,256,12,192,34,17,13,17,35,12,192,34,12,518,1090]),
([pw47,pw0,pw1,pw3,pw24,pw8],[9,20,13,37,45,21,29,1,57,77,109,197,241],[36,1029,36,2,28,4161,66,2,24,257,129,25,2048,514,24]),
([pw47,pw0,pw1,pw3,pw8],[1,13,37,193,197,9,45,21,29,33,53,57,65,77,153,221,229,245],[394,1059,658,4166,16425,792,131148,67601,101,40980]),
([pw0,pw1,pw2,pw24,pw8,pw29],[9,21,29,20,1,13,33,73,16,5,77,105,109,125,157,221,241,249,253],[65541,38,512,393220,16452,4099,17,17,17,32778,8202,34,3200,448,8]),
([pw0,pw1,pw2,pw3,pw8,pw48],[9,21,29,33,45,13,3,0,20,1,5,25,37,41,105,109,121,125,157,241],[524293,38,262156,8212,1024,32771,65545,513,193,34,131090,322,16408,2048,4096]),
([pw49,pw0,pw1,pw2,pw3,pw8],[1,41,65,21,9,29,73,33,45,109,121],[34,17,12,192,256,19,14,34,34,517,1089,17,12,12,192]),
([pw0,pw1,pw50,pw2,pw3,pw8],[5,21,45,9,61,29,37,53,16,1,13,25,33,101,105,129,153,189,3],[32777,33,65539,33,69,512,138,131096,76,1026,6160,262404,130,8198,16404]),
([pw0,pw1,pw2,pw3,pw8,pw51],[9,21,29,25,13,41,73,0,1,37,45,65,97,109,225,241,3],[32773,22,16396,1060,36,8195,4105,257,65665,18,2050,18,72,72,512]),
([pw52,pw0,pw1,pw2,pw3,pw8],[1,13,9,21,25,29,37,5,33,41,45,97,101,105,109,225],[128,5,10,256,1024,5,10,32816,544,16387,2065,5,10,4162,8272]),
([pw27,pw0,pw1,pw2,pw3,pw26],[9,21,13,33,25,45,1,0,28,97,109,133,165,213],[8192,97,38,56,128,65,6,24,4096,1027,521,2305,6,6,24]),
([pw53,pw0,pw2,pw3,pw8,pw26],[21,1,13,33,25,9,0,41,45,65,73,133,213,257],[34,7,26,34,64,5,24,4480,8192,5,513,5,1032,24,2048]),
([pw53,pw0,pw2,pw3,pw8],[1,13,25,133,257,21,33,9,41,45,49,57,65,73,169,173,209,241],[401,1059,2117,649,65586,131156,792,102,20490,40972]),
([pw0,pw1,pw2,pw3,pw26,pw28],[9,33,25,41,1,45,69,20,32,5,21,65,97,101,113,169,213,249,261],[25,65544,14,512,131112,278529,4099,33025,17,6,10304,1024,6,6,224]),
([pw54,pw0,pw1,pw2,pw3,pw8],[17,25,49,9,33,41,69,45,21,97,117],[33,12,256,18,192,13,33,19,33,12,518,12,18,192,1090]),
([pw0,pw1,pw2,pw3,pw26,pw29],[9,21,13,41,1,45,77,20,36,5,33,73,105,109,121,173,213,249,265],[25,14,131080,512,65576,8195,278529,33025,17,6,6,6,6208,1024,224]),
([pw55,pw0,pw1,pw2,pw3,pw8],[13,29,57,9,21,41,77,45,33,109,125],[34,12,17,256,192,14,19,34,34,517,12,12,17,1089,192]),
([pw0,pw1,pw2,pw56,pw3,pw8],[9,17,33,21,69,25,37,41,49,20,1,13,97,105,137,209,3],[32771,16394,130,38,130,257,1025,4101,257,2048,44,88,66052,80,8212]),
([pw0,pw1,pw2,pw3,pw57,pw8],[9,21,29,37,20,13,33,41,57,77,1,25,101,109,157,241,3],[32773,38,16452,132,132,8195,257,1025,257,34,65554,4106,2048,584,536]),
([pw58,pw0,pw1,pw2,pw3,pw8],[1,33,45,13,20,29,25,3,0,16,5,9,97,101,105,109,133,145,165,201],[1024,2065,272,146,644,131105,524328,66,262180,32777,4099,65541,74,8204,16390]),
([pw59,pw0,pw1,pw2,pw3,pw8],[9,21,33,45,49,53,25,37,5,97,101,105],[256,17,34,68,136,17,34,68,136,17,517,17,34,1034,2060]),
([pw60,pw0,pw1,pw2,pw3,pw8],[1,21,45,20,17,25,13,3,0,16,5,9,97,101,105,109,129,133,165,237],[1024,2057,138,264,644,65553,66,524336,262164,32771,4129,131077,66,8198,16420]),
([pw61,pw0,pw1,pw2,pw3,pw8],[9,21,45,57,13,33,37,61,5,101,105,109],[256,9,18,160,68,9,18,160,68,2051,9,9,18,518,1060]),
([pw62,pw0,pw1,pw2,pw3,pw8],[9,13,33,29,37,16,20,3,0,5,17,21,97,101,105,109,133,137,197,249,257],[1024,385,2082,196,96,1048585,131082,524,524312,32771,4101,65553,262150,8210,16404]),
([pw63,pw0,pw1,pw2,pw3,pw8],[9,21,33,65,1,45,25,69,17,97,113,117],[256,17,10,68,160,17,10,68,160,1027,517,17,10,10,2084]),
([pw64,pw0,pw1,pw2,pw3,pw8],[9,21,17,25,37,20,16,3,0,5,29,97,101,105,109,133,157,197,213,257],[1024,385,162,96,96,524293,518,65548,262164,16387,2057,32785,131082,4114,8216]),
([pw65,pw0,pw1,pw2,pw3,pw8],[9,21,33,1,13,45,73,77,29,109,121,125],[256,9,18,68,160,9,18,68,160,515,1029,9,18,2082,68])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D4 : List StD := [
([pw66,pw0,pw1,pw2,pw8],[21,45,225,9,33,5,37,197,97,105,109,269],[36,280,145,530,36,133,70,1033,74,2051]),
([pw67,pw0,pw1,pw2,pw3],[21,33,165,9,45,5,13,17,25,97,105,109,133,149],[36,4120,81,1042,36,133,8198,2057,522,259]),
([pw68,pw0,pw1,pw3,pw8],[33,45,193,9,21,5,37,197,97,101,109,269],[36,1048,145,530,36,133,70,265,74,2051]),
([pw69,pw0,pw1,pw2,pw3],[21,165,9,33,45,5,13,25,29,97,101,109,133,153],[34,4116,1041,152,34,8195,266,2053,524,65]),
([pw70,pw0,pw1,pw2,pw8],[5,45,17,21,37,33,9,97,177,197,269,273],[5,192,552,50,5,5,19,2312,18,1034]),
([pw71,pw0,pw1,pw3,pw8],[5,21,45,29,33,37,9,109,189,197,269,273],[11,194,530,38,9,9,37,2320,36,1044]),
([pw72,pw0,pw2,pw3,pw8],[9,33,45,257,21,17,133,13,25,97,101,277,281],[41,145,515,69,40,2058,76,274,1044,4102]),
([pw73,pw0,pw1,pw2,pw8],[9,225,21,33,45,17,1,37,41,97,101,197,209,273],[34,521,2060,152,4099,34,274,8197,65,1044]),
([pw74,pw0,pw1,pw2,pw3],[17,33,5,9,13,25,45,21,53,61,133],[5,1096,208,98,5,5,35,280,522,50]),
([pw75,pw0,pw2,pw3,pw8],[9,13,33,45,257,25,133,21,29,281,285,289],[273,131,37,73,1042,52,88,38,2058,524]),
([pw76,pw0,pw2,pw3,pw8],[9,21,45,257,33,133,13,17,25,29,105,109,289,293],[137,2051,273,37,8202,536,44,66,4102,1044]),
([pw77,pw0,pw1,pw3,pw8],[9,21,33,193,45,197,1,5,37,41,105,109,273,293],[138,2051,38,274,8201,44,536,4101,65,1044]),
([pw78,pw0,pw1,pw2,pw3],[21,29,5,9,13,45,25,33,53,61,133],[6,1064,49,224,6,19,6,265,584,17]),
([pw79,pw0,pw2,pw3,pw8],[9,21,45,257,13,25,133,17,33,281,289,297],[137,19,289,69,26,2088,76,18,1030,548]),
([pw80,pw0,pw1,pw2,pw8],[9,37,225,21,33,17,45,97,133,197,209,269,273,301],[36,145,536,82,1029,36,8198,4105,259,2058]),
([pw81,pw0,pw1,pw3,pw8],[9,21,33,37,193,197,5,45,109,133,269,273,293,305],[82,259,38,138,4113,52,8216,2053,521,1036]),
([pw0,pw1,pw2,pw82,pw8],[25,29,45,13,5,9,33,37,97,101,105,109,157,165,181,201,309],[4098,98306,19,8198,18440,289,132,65,524,1029]),
([pw0,pw1,pw2,pw3,pw83],[29,13,33,45,213,37,97,101,105,109,145,181,185,197,313],[17409,17,17,17,2562,4164,40,8198,138,268]),
([pw0,pw1,pw84,pw3,pw8],[13,17,45,25,5,9,21,37,97,101,105,109,137,165,185,237,317],[4098,19,98306,8198,2081,16648,132,65,517,1036]),
([pw0,pw1,pw2,pw3,pw85],[13,17,45,25,249,21,37,97,101,105,109,129,181,185,193,313],[34818,16387,18,18,5121,8328,68,33,261,524]),
([pw0,pw86,pw2,pw3,pw8],[9,29,33,37,5,13,21,25,45,97,101,105,109,137,141,249,257,321],[65539,24578,18,163842,4161,517,265,132,1064,2060]),
([pw0,pw1,pw2,pw87,pw8],[9,29,13,33,37,5,21,97,101,105,109,133,137,249,253,257,309],[32771,69634,34,24578,1029,137,2065,76,276,536]),
([pw0,pw88,pw2,pw3,pw8],[9,17,21,37,25,5,33,45,97,101,105,109,157,161,197,213,257,321],[65539,34,12290,163842,2053,321,137,16404,524,1048]),
([pw0,pw1,pw89,pw3,pw8],[9,17,21,25,37,5,33,97,101,105,109,133,157,213,217,257,317],[32771,34,69634,24578,1029,137,2065,76,276,536])]
def p7_D3 : List StD := []
theorem p7_I3 : LevelN true p7_T 3 p7_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C4x0 : levelOK true p7_T p7_t 3 (p7_D3.map Prod.fst) ((p7_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I4 : LevelN true p7_T 4 p7_D4 := levelStep p7_B p7_W p7_I3 (chunks 32 p7_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C5x0 : levelOK true p7_T p7_t 4 (p7_D4.map Prod.fst) ((p7_D5.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C5x1 : levelOK true p7_T p7_t 4 (p7_D4.map Prod.fst) ((p7_D5.drop (1*32)).take 32) = true := by decide +kernel
theorem p7_I5 : LevelN true p7_T 5 p7_D5 := levelStep p7_B p7_W p7_I4 (chunks 32 p7_D5 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C5x0
  · exact p7_C5x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C6x0 : levelOK true p7_T p7_t 5 (p7_D5.map Prod.fst) ((p7_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I6 : LevelN true p7_T 6 p7_D6 := levelStep p7_B p7_W p7_I5 (chunks 32 p7_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C7x0 : levelOK true p7_T p7_t 6 (p7_D6.map Prod.fst) ((p7_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I7 : LevelN true p7_T 7 p7_D7 := levelStep p7_B p7_W p7_I6 (chunks 32 p7_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C7x0
  ))
theorem p7_L : LowN true p7_R p7_T 8 := lowSearch p7_B p7_I7 (by decide +kernel)
def p8_T : Nat := 0xfeeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0
def p8_R : List Nat := [0, 1, 2, 3, 4]
def p8_E : List (Nat × Nat × Nat) := [(0,16,17),(1,4,6),(2,2,6),(3,2,10),(4,1,17)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := [(pw0,5,[4, 2, 3, 1])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p8_B p3_B p3_L (by decide +kernel),by simp⟩
def p8_C : List (Nat × List Nat) := [(0,[])]
def p8_t : Tabs := (p8_C.map (mkCut true p8_Z),[(17,16),(6,4),(19,18),(7,5),(6,2),(21,20),(7,3),(10,2),(25,24),(11,3)],[],[[]])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D5 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[0,1,5,17,29,9,13,21,25,33,37],[102,394,1554,1,1,5,5,25,9,17])]
def p8_D4 : List StD := []
theorem p8_I4 : LevelN true p8_T 4 p8_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8_C5x0 : levelOK true p8_T p8_t 4 (p8_D4.map Prod.fst) ((p8_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p8_I5 : LevelN true p8_T 5 p8_D5 := levelStep p8_B p8_W p8_I4 (chunks 32 p8_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C5x0
  ))
theorem p8_L : LowN true p8_R p8_T 6 := lowSearch p8_B p8_I5 (by decide +kernel)
def p9_T : Nat := 0xfffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeee
def p9_R : List Nat := [0, 1, 2, 3, 4]
def p9_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
def p9_Z : List SliceD := [(pw4,5,[1, 2, 3, 4])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN true p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p9_B p3_B p3_L (by decide +kernel),by simp⟩
def p9_C : List (Nat × List Nat) := [(0,[])]
def p9_t : Tabs := (p9_C.map (mkCut true p9_Z),[(1,0),(2,0)],[],[[]])
theorem p9_W : TabsP true p9_R p9_T p9_t := ⟨cutsGood p9_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D5 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[0,1,5],[7,3,3,3,5,5,5,1,1,1])]
def p9_D4 : List StD := []
theorem p9_I4 : LevelN true p9_T 4 p9_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C5x0 : levelOK true p9_T p9_t 4 (p9_D4.map Prod.fst) ((p9_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I5 : LevelN true p9_T 5 p9_D5 := levelStep p9_B p9_W p9_I4 (chunks 32 p9_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C5x0
  ))
theorem p9_L : LowN true p9_R p9_T 6 := lowSearch p9_B p9_I5 (by decide +kernel)
def p10_T : Nat := 0xfffefeeefff8f8e8fffefeeefff8f8e8fffefeeefff8f8e8fffefeeefff8f8e8
def p10_R : List Nat := [0, 1, 2, 3, 4, 5]
def p10_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,4,12),(4,4,20),(5,1,33)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
def p10_Z : List SliceD := [(pw4,7,[1, 2, 3, 4, 5]),(pw17,7,[0, 2, 3, 4, 5]),(pw5,7,[2, 1, 0, 5, 4]),(pw9,7,[2, 1, 0, 5, 3]),(pw90,8,[2, 1, 3, 4, 0]),(pw91,4,[2, 3, 4]),(pw7,6,[3, 1, 0, 5, 4]),(pw3,6,[2, 4, 0, 1, 5]),(pw8,6,[2, 3, 0, 1, 5]),(pw92,4,[2, 3, 4]),(pw93,5,[4, 1, 0, 5]),(pw94,5,[3, 1, 0, 5]),(pw95,5,[2, 1, 0, 5]),(pw96,4,[0, 1, 5])]
theorem p10_Y : ∀ s ∈ p10_Z, SliceN true p10_R p10_T s := by
  unfold p10_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p10_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p10_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p10_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p10_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p10_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p10_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p10_B p8_B p8_L (by decide +kernel),mkSlice (w:=8) p10_B p9_B p9_L (by decide +kernel),mkSlice (w:=16) p10_B p9_B p9_L (by decide +kernel),mkSlice (w:=32) p10_B p1_B p1_L (by decide +kernel),mkSlice (w:=8) p10_B p3_B p3_L (by decide +kernel),mkSlice (w:=16) p10_B p3_B p3_L (by decide +kernel),mkSlice (w:=8) p10_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p10_B p1_B p1_L (by decide +kernel),by simp⟩
def p10_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(4,[517]),(5,[]),(6,[]),(7,[]),(8,[]),(2,[261]),(3,[261]),(9,[]),(10,[]),(11,[]),(1,[129]),(2,[257]),(3,[257]),(4,[513]),(4,[514]),(1,[131]),(1,[257]),(12,[]),(4,[521]),(2,[521]),(4,[525]),(0,[129]),(2,[129]),(3,[129]),(4,[129]),(4,[130]),(0,[131]),(0,[257]),(4,[261]),(0,[385]),(2,[517]),(4,[389]),(1,[261]),(0,[261]),(13,[]),(4,[257]),(0,[262]),(4,[258]),(1,[262]),(1,[389]),(0,[389]),(2,[513]),(4,[385]),(4,[386]),(1,[390]),(0,[390]),(0,[517]),(2,[385]),(3,[385]),(0,[393]),(1,[393]),(4,[393]),(4,[517,513]),(4,[517,129]),(4,[129,534]),(4,[513,150]),(4,[129,533]),(0,[514]),(2,[261,406]),(3,[261,406]),(4,[513,129]),(4,[513,519]),(4,[519]),(4,[130,533]),(4,[130,534]),(4,[516]),(4,[519,21]),(4,[129,535]),(4,[128]),(4,[129,513]),(4,[263,533]),(4,[263,534]),(4,[261,533]),(4,[521,150]),(2,[263]),(4,[391,533]),(4,[391,534]),(4,[389,533]),(4,[525,150]),(2,[521,150]),(4,[129,518]),(4,[518]),(4,[514,149]),(4,[518,21]),(4,[131,534]),(4,[512]),(4,[522,149]),(4,[261,534]),(2,[262]),(4,[526,149]),(4,[389,534]),(2,[517,278]),(0,[261,406]),(1,[261,406]),(2,[514]),(4,[257,406]),(0,[389,278]),(1,[389,278]),(4,[385,278]),(4,[386,533]),(4,[386,149]),(0,[390,533]),(4,[517,513,129])]
def p10_t : Tabs := (p10_C.map (mkCut true p10_Z),[(5,4),(3,2),(3,1),(5,1),(11,10),(25,17),(19,18),(25,9),(33,1),(33,0),(6,4),(6,2),(11,9),(26,18),(19,17),(26,10),(34,2),(12,8),(12,4),(20,16),(20,4),(12,40),(41,9),(49,17),(37,36),(34,32),(13,9),(21,17),(33,9),(33,17),(3,0),(24,9),(41,40),(19,1),(5,17),(49,48),(24,17),(33,32),(11,2),(19,2),(14,10),(22,18),(24,16),(24,10),(50,48),(5,0),(24,18),(5,9),(6,18),(12,0),(20,48),(37,4),(24,8),(38,4),(38,36),(3,18),(3,17),(12,36),(3,10),(3,9),(11,1),(20,36),(20,0),(24,40),(13,1),(21,1),(12,9),(42,40),(6,10),(14,2),(22,2),(5,2),(12,10),(6,0),(52,36),(25,1),(26,2),(20,32),(24,32),(44,40),(56,48),(44,4),(44,36),(12,32),(52,4),(3,4),(35,4),(34,0),(13,4),(14,4),(21,4),(22,4),(26,16),(26,8),(25,16),(25,8)],[],[[]])
theorem p10_W : TabsP true p10_R p10_T p10_t := ⟨cutsGood p10_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D9 : List StD := [
([pw0,pw1,pw2,pw3,pw8,pw97],[3,0,4,8,12,16,1,9,33,21,29,5,73,13,17,25,37,41,45,49,53,57,61,65,69,77,81,85,89,93],[2247,10307,16971,33875,65890,393349,1573005,6291605,8389028,16781833,100664337,134218017,5657,268436264,536872240])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D8 : List StD := [
([pw0,pw1,pw20,pw2,pw3,pw8,pw97],[0,3,4,20,24,48,5,9,21,29,40,44,13,33,73,8,12,28,32,36,17,25,45,49,57,65,69,77,81],[5,5,4163,1048641,2097217,8201,1,4194438,8388740,16777348,33554444,135186,295184,590352,8218,67126530,402655746,40,20226,40,40]),
([pw0,pw1,pw2,pw22,pw3,pw8,pw97],[0,28,52,9,56,60,72,13,21,65,64,68,1,29,3,53,61,73,101,33,41,81,97,105,109,113,117],[20489,131,3,4357,12305,4198401,1065130,278568,34092,75832,262760,1,8519814,18874514,17090,34052,75792,524864,134404,33556292,67119696]),
([pw98,pw0,pw1,pw2,pw3,pw8,pw97],[28,52,56,76,73,0,81,33,3,80,5,41,4,72,13,45,53,61,65,121],[8193,6401,32769,19,69,265,527904,16417,1074,1124,168,2817,65554,131140,262792,19,69,265,22,154,204]),
([pw0,pw1,pw2,pw3,pw24,pw8,pw97],[52,0,88,84,41,92,8,13,9,17,21,45,65,5,33,61,81,85,117,125,129,133,137,3],[794,131,1027,8195,524294,1049090,2329,89,8388633,2129948,20536,133,2177,4194309,131105,2,69,1089,65541,4129,262180]),
([pw0,pw1,pw2,pw3,pw8,pw26,pw97],[56,0,88,13,29,73,96,100,25,65,12,45,141,4,33,41,53,85,113,137,145,3],[4354,11,1048838,19,7,4354,2057,65636,1041,2138113,17024,45,524313,2057,131201,113,101,262884,2,1041,641]),
([pw0,pw1,pw2,pw10,pw3,pw8,pw97],[52,4,104,108,112,116,1,56,21,33,29,3,5,53,61,65,73,149,45,81,113,117,153,157,161,165],[6214,6213,133188,4194637,8389844,131684,262147,3,8203,16530,32802,2,16843017,34079889,2593,8457,17552,33312,65817,1049385,2098864]),
([pw99,pw0,pw1,pw2,pw3,pw8,pw97],[52,120,169,4,56,81,3,124,1,9,33,73,0,116,13,21,29,37,45,65,121],[4417,8193,16385,2053,49,67,1049480,449,32773,65584,132226,262153,525,568,524298,2053,49,67,2053,1031,1074]),
([pw0,pw1,pw2,pw3,pw12,pw8,pw97],[52,4,88,128,1,8,132,13,5,33,29,37,45,49,65,81,85,117,137,157,173,3],[8474,409,57,2097177,525340,2648,4099,35,35,1048582,16450,133,133,262149,65601,2,33,33,32773,577,131140]),
([pw0,pw1,pw2,pw3,pw8,pw100,pw97],[56,4,88,136,12,140,144,5,13,33,57,21,45,177,1,37,73,77,85,113,153,181,185,189,193,3],[9218,2097545,1050796,153,33570825,33480,4099,4195334,19,7,9218,8388869,16908545,4353,262209,49,65573,526948,2,17,577]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw97],[52,156,8,148,152,5,41,160,9,29,33,105,3,12,1,37,61,65,81,85,117,157,161,169],[4472,18481,53,51,2097714,33968,4194633,77,267,66122,132296,2053,5,262147,524417,8388609,5,5,12291,3,1048706]),
([pw101,pw0,pw1,pw2,pw3,pw8,pw97],[52,88,164,168,5,81,172,3,1,33,41,21,4,9,13,29,37,53,61,65,73,85,105,117,161,197],[405,5249,16385,1048577,35,137,8660,4194581,2069,32822,66076,16778305,132161,262178,524872,33556483,35,2097161,35,521,8388618]),
([pw0,pw1,pw2,pw3,pw8,pw28,pw97],[56,12,176,180,5,52,156,184,41,188,9,21,33,109,3,8,1,37,53,65,73,113,153,165,201],[17692,73753,4196536,27,89,135704,8389893,264612,263,1093,529156,1048641,8195,3,16777729,131,49313,2099936,33,3,65]),
([pw102,pw0,pw1,pw2,pw3,pw8,pw97],[52,192,169,12,196,200,41,3,1,33,73,29,109,0,4,188,5,9,13,21,37,53,61,65,117,157,165,201],[8577,16577,262145,1029,32769,131,196848,4385,524293,33556776,1049122,67108945,2097157,4196440,8389138,1029,4105,134217731,1029,519,16777226]),
([pw0,pw1,pw2,pw3,pw8,pw103],[48,52,204,208,212,1,9,21,56,29,5,73,33,41,81,3,16,53,61,65,85,153,157,201],[1125,33830,2097326,4195124,5157,41027,131275,262993,536641,1050762,8405778,65536,2202,2187,17169]),
([pw0,pw1,pw2,pw3,pw8,pw29,pw97],[56,8,216,220,1,9,156,224,13,29,5,21,33,69,17,37,45,53,65,73,77,85,89,3],[8389692,1301,18454,533,85,37012,65833,133162,105,105,266408,8195,1048833,8449,2097281,515,524291,4194434,3,577,65])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D7 : List StD := [
([pw1,pw20,pw2,pw22,pw3,pw8,pw97],[48,60,228,5,9,156,13,73,81,169,209,0,65,3,52,56,17,25,49,57,105,109,205],[2048,8274,8218,262162,524306,4118,35,42,16417,32801,4198405,2048,1049280,2098496,69,66184,132360,13,1920,5,5]),
([pw0,pw20,pw2,pw10,pw3,pw8,pw97],[48,33,5,41,232,9,73,81,169,209,156,45,65,3,52,56,1,17,25,49,57,161,165,213],[65537,8197,8229,131077,262149,4103,1033,1033,16393,32777,8388619,1,2099520,4196992,19,524640,1049248,4099,960,19,19]),
([pw0,pw1,pw2,pw30,pw3,pw8,pw97],[65,73,81,48,1,41,45,244,21,29,156,236,5,9,13,33,3,52,56,240,17,25,49,53,57,61,97,105,109,169,209,217],[12336,20560,67584,1048850,2097684,67141649,24672,589824,12582946,50331684,2147516449,8,134218050,268436036,201,537003010,1074004996,2185,774,139,141]),
([pw104,pw0,pw1,pw2,pw3,pw8],[48,248,37,3,20,33,213,252,256,73,169,209,9,13,17,25,49,57,69,77,81,89,93,205],[22,18,8233,2097185,4194337,22,8388614,16390,32774,4161,65601,131137,263816,1575176,3976]),
([pw0,pw1,pw20,pw2,pw3,pw14,pw8,pw97],[152,33,9,105,29,73,17,81,48,52,156,5,49,3,8,44,160,1,13,65,69,85,89,117,133,161,169,189,221,225,229],[5,131072,9,2113,2113,268435521,3,1,33554444,4100,4100,553648132,524294,1048584,16928,1792,1168,73730,134217768,262144,152,2097162,67108864,176,1073741858,40976,4194562,8388626]),
([pw101,pw0,pw1,pw20,pw2,pw3,pw8,pw97],[33,209,9,164,5,105,48,156,3,21,81,20,168,1,13,29,65,69,73,85,113,117,161,169,197,221,225,233,237,241],[336,324,448,16384,262144,1026,2113,12,8192,56,134217752,33554450,25,8,4194340,805306372,67108870,65541,131232,8389248,32898,4353,16777760,1026,524321,1026,1049089,2097155]),
([pw0,pw1,pw20,pw2,pw3,pw8,pw28,pw97],[180,33,9,109,73,5,21,81,56,156,25,57,3,40,188,1,13,65,77,93,113,137,165,201,209,233,237,241,245],[5,32768,9,33554465,1057,1057,3,1,4194316,201326596,2052,2052,131078,262152,80,896,768,20482,88,2097288,65536,8388618,80,12304,1048594,16777216,268435586,524290]),
([pw102,pw0,pw1,pw20,pw2,pw3,pw8,pw97],[33,169,9,200,5,109,156,3,48,29,73,0,20,192,1,13,21,65,77,81,113,117,133,165,201,209,221,225,233,237,249],[2192,388,448,32768,1026,524288,4353,12,16384,56,268435474,67108888,25,8,8388644,536870918,138412036,131077,262240,65602,33555008,8321,1026,1073742368,16777249,1026,1048579,2097665]),
([pw0,pw1,pw20,pw2,pw3,pw8,pw29,pw97],[216,13,33,9,17,69,209,40,5,49,89,56,156,224,1,21,25,29,45,57,65,73,77,85,169,253,3],[9,16384,3,273,65553,273,5,1,262154,520,524296,520,1048588,34,16809984,131136,6144,67117060,34,4194306,34,8388614,192,2097152,1028,128,33554500,1028]),
([pw0,pw1,pw2,pw22,pw10,pw3,pw8,pw97],[156,48,21,1,29,41,33,65,73,81,3,0,53,61,260],[1064,9,1,3080,268,536,200,33,1058,1,4132,8240,224,2,2,260,528,16387,2050,4101,8209,192,261,529,192,260,7,19]),
([pw0,pw1,pw22,pw10,pw3,pw8,pw97],[48,156,52,56,1,21,41,29,33,65,53,61,3,13,45,73,81],[4177,2,12305,53,153,785,20545,2,1093,2121,833,1,1062,2186,769,1062,2186,769,98340,39,139]),
([pw99,pw0,pw1,pw22,pw3,pw8,pw97],[48,156,13,21,9,29,101,1,33,65,41,73,137,169,189,209,225,237,257,261],[7,1027,1,278534,528390,7,209,2,11,35,897,81,131075,65539,81,8202,32802,769,2058,11,35]),
([pw0,pw1,pw2,pw22,pw30,pw3,pw8,pw97],[48,21,29,1,9,13,33,65,73,41,81,169,209,3,72,5,101,225,237,265],[536,524328,32768,8192,266,1036,200,528,8193,65536,262162,131092,208,1,1,290,1060,33,1,2050,4100,192,2050,4100,16449,258,3,5]),
([pw39,pw0,pw1,pw2,pw22,pw3,pw8,pw97],[48,13,1,73,101,156,81,169,33,65,209,3,264,5,9,21,29,173,185],[4132,16384,35,1,168,1120,4097,2068,3,8192,32773,65541,772,2066,2049,262161,131089,784,1,138,1090,3,136,1088,769,136,9,65]),
([pw39,pw0,pw1,pw2,pw3,pw8,pw97],[48,240,5,45,65,169,209,101,1,13,33,73,81,156,268,272,3,52,56,244,276,280,284,288,292,17,25,105,109,177,269],[3195140,589824,29393416,141344,274496,17426,389,780,33554469,67108933,1046,66185,1073741985,536871105,1042,134219816,268439624,27,6240,51,83]),
([pw0,pw1,pw2,pw22,pw3,pw8,pw103],[48,156,41,21,1,29,9,33,65,73,13,81,101,169,209,225,237],[85,3,2,27,51,401,69,4101,65543,32775,69,1,522,2082,1027,8202,16418,385,522,11,35]),
([pw0,pw1,pw22,pw3,pw8,pw103],[48,156,52,9,56,1,21,29,13,41,65,73,81,101,169,209,225,237,265],[553,3,101,177,262433,8201,131085,65561,521,16454,32914,1281,6214,71,147]),
([pw0,pw1,pw105,pw2,pw3,pw8,pw97],[48,156,149,41,53,13,61,5,33,65,73,137,169,189,209,221,233],[141,133,39,65543,32775,133,2,11,27,75,777,1,4114,16450,769,8242,2146,35,1042,19,67]),
([pw0,pw1,pw2,pw3,pw8,pw106],[48,156,41,205,9,13,5,209,17,25,49,57,73,81,137,169,189,257,261],[21,73,265,521,73,21,1029,2053,21,196642,278562,35,12418,32771,131]),
([pw98,pw0,pw1,pw10,pw3,pw8,pw97],[156,48,53,5,45,61,149,296,33,65,41,73,169,193,209,221,233,273,277,281,285],[129,19,2,393233,532497,131,1048650,74,65539,32771,74,1,7,35,1794,4101,16417,770,2053,7,35]),
([pw98,pw0,pw1,pw3,pw8,pw103],[156,48,41,169,9,73,209,72,5,13,45,81,181,221,225,233,237],[129,7,41,2113,1027,22,32771,8195,4866,65539,16387,22,41,11,67]),
([pw46,pw0,pw1,pw2,pw3,pw8,pw97],[52,5,48,312,13,53,65,81,129,21,33,45,268,300,41,56,156,280,304,308,316,25,77,177,189,209],[405762,524289,2065,8737,33652864,5192,16646,2067,803,2097286,1346,2065,545,8405124,1096,16777265,4194321,13,1048577,105,204]),
([pw53,pw0,pw1,pw2,pw3,pw8,pw97],[56,5,61,48,332,13,65,73,141,29,33,45,268,320,41,52,156,280,324,328,336,17,69,137,169,269],[405762,524289,2081,16875648,8709,5200,16650,2083,2097290,775,1346,2081,33570952,517,1104,4194337,8388645,25,1048709,216,85]),
([pw0,pw1,pw2,pw10,pw30,pw3,pw8,pw97],[48,33,53,1,61,45,65,5,169,209,3,116,9,73,149,193,221,233,273],[136,136,1025,16384,131081,65545,74,33,4096,1024,5,17,66,1,1,262180,32816,35,1,260,528,67,260,528,2049,8196,7,19]),
([pw59,pw0,pw1,pw2,pw10,pw3,pw8,pw97],[48,45,41,73,149,156,81,169,65,209,3,340,33,5,9,37,53,61,125,145],[8192,2084,35,1,168,608,2049,1044,1042,1025,524305,262161,33040,3,16384,65541,131077,4356,1,138,578,3,136,576,4353,136,9,65]),
([pw59,pw0,pw1,pw2,pw3,pw8,pw97],[48,236,9,13,33,169,209,149,41,45,65,73,81,156,244,348,3,52,56,276,280,344,352,356,360,49,57,105,109,129,141],[81920,3703044,29393416,141344,274496,17426,389,66185,536871073,1073742017,1042,780,33554469,67108933,1046,134219816,268439624,27,6240,51,83]),
([pw0,pw1,pw2,pw10,pw3,pw8,pw103],[48,56,52,1,33,41,5,73,65,81,17,25,45,149,169,209],[105,73,8201,1033,2057,73,3,2,37,35,305,1,134,518,4099,16516,33282,273,134,21,19]),
([pw0,pw1,pw10,pw3,pw8,pw103],[48,52,1,45,53,56,156,41,61,5,17,25,33,73,81,149,169,209,289],[517,32773,1029,2053,517,3,147,417,262281,65618,131424,4105,24658,27,297]),
([pw0,pw107,pw1,pw2,pw3,pw8,pw97],[48,56,156,1,101,45,9,21,33,65,73,137,169,189,237,261],[2,89,11,141,11,777,81,3,4228,6,769,35,16405,19,81,8230,34850,35,1030,133,7]),
([pw0,pw1,pw2,pw3,pw8,pw108],[48,156,1,9,45,5,209,213,17,25,49,57,73,81,121,169,193,273,277,281],[16397,37,261,517,37,137,1033,2057,137,393234,589842,19,12354,32771,67]),
([pw99,pw0,pw1,pw3,pw8,pw103],[48,156,1,5,169,73,209,9,13,41,45,81,221,225,233,237,293],[13,515,50,2114,259,13,16387,4099,13,32771,8195,66689,50,19,67]),
([pw61,pw0,pw1,pw2,pw3,pw8,pw97],[52,48,368,21,33,45,9,81,13,53,65,269,308,1,56,156,280,304,344,364,372,57,77,141,189,209],[4097,985152,289,521,33603712,5140,10306,289,521,8396930,1044,289,521,2097346,3152,16777257,4194337,7,1048577,29,150]),
([pw109,pw0,pw1,pw2,pw3,pw8,pw97],[56,29,48,380,33,45,73,9,13,61,65,177,328,1,8,52,280,324,344,376,384,49,69,129,137,169],[4097,985216,289,33603648,515,5144,10372,289,8396868,515,1048,289,2097348,515,3216,4194337,16777251,13,1048643,92,27]),
([pw110,pw0,pw1,pw2,pw3,pw97],[56,29,388,392,396,400,1,9,81,105,33,301,5,17,37,61,65,161,297,305,309,313,3],[259,32771,259,259,262147,4198604,581,10324,17508,131593,526488,66728,529,1048609,2097200]),
([pw0,pw111,pw1,pw2,pw3,pw8,pw97],[56,164,64,1,209,21,41,161,48,33,65,81,101,3,16,9,13,53,61,97,297,317,321],[1,41034,11,46,11,524298,12608,3,38,2065,18176,65665,131172,262161,5696,133,2065,2097281,21,4194340,1048593]),
([pw0,pw1,pw112,pw2,pw3,pw8,pw97],[56,172,1,41,65,81,29,45,108,169,48,5,33,53,105,149,3,16,17,21,25,217,297,317,321],[67598,99332,18564,786948,1048676,36884,1,11,8458,11,2097162,3,8450,97,136208,17025,225,8388753,97,16778000,4194353]),
([pw0,pw1,pw2,pw3,pw8,pw113],[48,1,9,208,56,169,5,41,69,209,325,17,25,49,57,81,121],[65543,67,2051,4099,67,133,8197,16389,133,1064,33552,281,1064,41,529]),
([pw114,pw0,pw1,pw2,pw8,pw97],[52,404,412,5,21,56,408,1,9,33,257,73,301,37,53,65,277,305,329,333,3],[155,16401,2065,2065,262161,1049034,1163,4138,8718,66625,131424,33604,1061,524293,4644]),
([pw0,pw115,pw1,pw2,pw3,pw8,pw97],[56,52,200,416,1,41,65,73,169,13,33,165,3,4,16,9,53,61,97,101,201,209],[1,36916,21,22,21,262164,536608,5,386,5,17480,2561,65826,2228225,1128,131,2563,1048585,131,330,73]),
([pw0,pw1,pw116,pw2,pw3,pw8,pw97],[56,196,1,52,41,65,73,420,21,45,209,5,33,109,149,3,0,16,17,25,29,201,217],[34838,114692,10756,262468,1573892,20516,1,19,26,19,4194322,3,328,3,135328,840,9729,2097825,328,232,1185]),
([pw0,pw1,pw2,pw3,pw8,pw117],[48,56,424,1,9,77,5,41,85,209,17,25,33,49,57,89,121,337],[65565,77,1037,2061,77,145,8209,16401,145,290,290,35,131586,36865,515])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D6 : List StD := [
([pw20,pw2,pw22,pw10,pw3,pw8,pw97],[48,1,21,33,56,73,209,428,81,5,13,153,205,285,341],[16402,18,18,38,18,4106,8192,1024,36,320,137,1,2564,320,137,36,320,137,36,5,73]),
([pw20,pw22,pw10,pw3,pw8,pw97],[48,33,341,56,73,81,169,209,5,9,65,52,17,25,49,57,89,93,345],[13,13,2053,13,262151,1,4432,8608,1027,16976,33440,1027,240,65539,131075]),
([pw39,pw20,pw2,pw22,pw3,pw8,pw97],[48,1,9,13,5,33,73,209,41,81,121,133,137,153,157,173,185,189,221,225,233,237,241,257,261,349],[262,13,1,6291460,526340,5,11,1027,65539,32771,33554466,1,8519688,16781320,9,1056784,278544,17,704,97,161]),
([pw59,pw20,pw2,pw10,pw3,pw8,pw97],[48,41,5,33,45,9,73,209,1,37,81,121,125,133,145,153,157,193,221,225,233,237,241,273,277,281,285],[262,67108869,1,1081348,327684,5,19,2051,16387,4099,522,1,25165840,33685520,17,6291488,532512,41,1216,73,137]),
([pw59,pw1,pw2,pw30,pw3,pw8,pw97],[65,5,9,48,45,169,1,33,73,209,16,236,13,81,121,133,137,153,157,181,189,221,225,233,237,241,257,261],[70,66,1024,8519682,2359298,131,4116,16384,50331652,4227076,133,524288,68157456,134283280,25,288,8704,2057,288,41,521]),
([pw39,pw0,pw2,pw30,pw3,pw8,pw97],[5,9,33,48,13,169,1,65,73,209,16,240,45,81,121,133,137,153,157,189,221,225,233,237,241,257,261,293],[67,4114,1024,25165826,2129922,134,65,16384,4325377,1310721,133,134217728,34078736,67174416,24,288,8704,2060,288,44,524]),
([pw0,pw1,pw2,pw118,pw3,pw8],[1,41,73,81,45,65,21,29,5,9,13,33,48,17,25,37,49,53,57,61,89,93,105,109,169,209,349],[771,1297,34849,8261,16521,1554,67110946,196614,786442,4096,4194388,8388760,17825828,35651624,204]),
([pw104,pw0,pw1,pw2,pw3,pw14,pw8],[29,37,9,33,105,81,5,17,49,69,89,256,13,41,73,161,169,189,225,3],[66,8204,536,1032,1032,41,66,530,130,130,35,32788,260,260,262149,147472,4096,49,65536,33,526337]),
([pw104,pw101,pw0,pw1,pw2,pw3,pw8],[29,33,37,9,21,81,105,48,5,69,169,213,13,41,73,197,205,225,237,3],[524418,262,8202,578,1042,35,65668,2184,4096,16384,33,260,580,1044,37,2056,262168,131081,32848,97,49]),
([pw104,pw0,pw1,pw2,pw3,pw8,pw28],[21,37,9,33,109,73,5,25,57,77,93,252,13,41,81,137,165,209,237,3],[66,8204,536,41,1032,1032,66,530,35,130,130,65556,262149,260,260,49,49168,4096,33,526337,131072]),
([pw104,pw102,pw0,pw1,pw2,pw3,pw8],[21,33,37,9,73,29,109,48,5,77,209,213,13,41,81,205,225,237,249,3],[524418,262,8202,578,19,1058,32900,2184,4096,17,16384,260,580,21,1060,2056,131081,65576,81,262240,17]),
([pw104,pw0,pw1,pw2,pw3,pw8,pw29],[13,37,9,33,69,29,252,5,21,49,169,209,17,41,45,57,73,77,89],[130,8204,25,1288,2088,262152,130,19,1282,2082,4098,16389,516,32772,516,17,131073,17,96,65536,64]),
([pw110,pw0,pw1,pw20,pw2,pw3,pw97],[89,388,9,5,81,105,29,17,33,49,73,301,400,1,65,69,161,309,3],[136,516,80,80,80,273,6,8192,42,136,11,2,65572,516,16389,32800,3072,266241,3074,131105,257]),
([pw111,pw1,pw20,pw2,pw3,pw8,pw97],[48,5,9,65,161,29,1,21,81,13,33,41,69,85,113,117,133,153,157,205,221,225,233,237,241,353],[7,3,3,4325377,1310722,3,2048,532,25165828,2162692,1036,4112,33554624,352,524360,528,304,8216,416,16520,32808]),
([pw0,pw112,pw20,pw2,pw3,pw8,pw97],[48,9,33,105,5,21,29,41,81,1,45,65,69,85,113,117,133,153,157,213,221,225,233,237,241,285,357],[3,512,33554456,4325392,1310736,2068,3,3,25165825,2162690,3,4104,67109024,448,524420,1064,328,8204,352,16420,32836]),
([pw0,pw1,pw119,pw2,pw3,pw8,pw97],[33,1,9,45,209,81,169,5,65,69,16,48,13,21,73,85,101,113,117,133,149,153,157,221,225,233,237,241],[134,1048576,130,35651586,12582914,259,65536,4108,201326596,17301508,261,520,24640,48,3073,520,56,32777,112,131137,262161]),
([pw114,pw0,pw1,pw20,pw2,pw8,pw97],[33,404,9,257,5,73,21,25,57,81,301,412,1,65,197,277,313,325,333,3],[144,260,96,96,96,131105,6,4096,26,144,19,2,32780,260,8197,16392,1536,526337,1034,262153,66049]),
([pw115,pw1,pw20,pw2,pw3,pw8,pw97],[48,5,9,65,165,1,21,73,13,29,33,41,113,117,133,153,157,201,205,221,225,233,237,241,265,361],[7,3,3,2129922,589825,3,2048,276,12582916,1064964,1036,16777264,224,33554976,262184,208,272,131096,192,4168,8712]),
([pw0,pw116,pw20,pw2,pw3,pw8,pw97],[48,9,33,109,5,21,41,29,73,1,45,65,113,117,133,153,157,201,213,221,225,233,237,241,285,289,365],[3,512,16777240,2129936,589840,2068,3,3,12582914,1064961,3,33554504,352,67109056,262212,296,1160,131084,288,4132,8324]),
([pw0,pw1,pw120,pw2,pw3,pw8,pw97],[33,1,9,45,169,73,5,65,77,209,16,48,13,29,81,101,113,117,133,149,153,157,201,221,225,233,237,241],[70,524288,66,34603010,10485762,131,32768,4108,201326596,17039364,133,264,48,25088,3073,56,264,4194313,48,65553,131585]),
([pw59,pw1,pw2,pw22,pw3,pw8,pw97],[9,73,1,81,13,169,48,33,65,209,41,16,5,121,149,181,225,237,265],[1025,262164,6148,38,524,388,1025,24577,131075,65545,385,32768,50,536,80,34,520,384,34,66,72]),
([pw39,pw0,pw2,pw10,pw3,pw8,pw97],[5,73,41,81,45,169,48,33,65,209,1,16,9,13,101,121,221,233,289],[1025,262164,6148,38,524,388,1025,49153,131075,65545,385,8192,50,536,80,34,520,384,34,66,72]),
([pw59,pw1,pw22,pw10,pw3,pw8,pw97],[65,81,1,33,53,209,52,45,41,73,9,13,61,113,117,149,257,265,289,341],[524356,68,131072,68,38,13,262528,1024,784,4098,9,32896,656,34,9,67600,34,9,34,8209,16387]),
([pw39,pw0,pw22,pw10,pw3,pw8,pw97],[33,81,1,21,41,65,209,52,13,73,5,9,29,45,101,113,117,265,277,289,341],[1048708,524288,2192,144,82,49,1024,131332,524,4102,37,16640,270344,66,33,776,66,33,66,32777,65539]),
([pw121,pw0,pw1,pw2,pw3,pw8,pw97],[5,65,169,209,45,1,33,81,13,21,9,73,85,113,117,173,185,189,221,369,373],[33,1024,272,2564,136,66,33,33,517,262153,67,272,589828,1081352,66,131092,152,4114,140,8198,16394]),
([pw122,pw0,pw1,pw2,pw3,pw8,pw97],[9,33,169,209,13,41,65,81,45,53,5,73,85,113,117,125,145,189,225,377,381],[1024,33,272,2564,136,66,33,272,589828,1081352,66,33,517,262153,67,131092,152,4114,140,8198,16394]),
([pw123,pw0,pw1,pw2,pw3,pw8,pw97],[5,65,169,45,209,1,33,73,13,29,9,81,113,117,137,173,185,201,233,369,373],[33,1024,264,132,2576,66,33,33,262149,529,67,264,589828,1081360,66,140,16408,131082,132,4102,8210]),
([pw124,pw0,pw1,pw2,pw3,pw8,pw97],[9,33,169,13,209,41,65,73,45,61,5,81,113,117,125,137,145,201,237,377,381],[1024,33,264,132,2576,66,33,264,589828,1064976,66,33,262149,529,67,140,32792,131082,132,4102,8210])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D5 : List StD := [
([pw104,pw110,pw0,pw1,pw2,pw3],[81,9,29,37,105,33,73,301,5,49,69,41,161],[5,264,2082,1072,224,5,515,5,5,264,1048,200,4114,514,208]),
([pw125,pw0,pw1,pw2,pw3,pw8],[13,37,81,9,33,169,69,209,5,45,73,221,225,233,237,349],[258,32792,81,1072,148,258,67,8226,2054,521,16424,4108,65,133,164]),
([pw104,pw114,pw0,pw1,pw2,pw8],[73,9,21,37,257,33,81,301,5,57,197,41,277],[5,264,2082,1072,224,5,515,5,5,264,1048,200,4114,514,208]),
([pw126,pw0,pw1,pw2,pw3,pw8],[13,37,73,9,33,209,169,5,1,45,69,81,137,221,225,233,237,349],[130,131096,1041,84,2096,130,259,32774,8226,521,65548,16424,69,4129,68])]
def p10_D4 : List StD := []
theorem p10_I4 : LevelN true p10_T 4 p10_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C5x0 : levelOK true p10_T p10_t 4 (p10_D4.map Prod.fst) ((p10_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p10_I5 : LevelN true p10_T 5 p10_D5 := levelStep p10_B p10_W p10_I4 (chunks 32 p10_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C6x0 : levelOK true p10_T p10_t 5 (p10_D5.map Prod.fst) ((p10_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p10_I6 : LevelN true p10_T 6 p10_D6 := levelStep p10_B p10_W p10_I5 (chunks 32 p10_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C7x0 : levelOK true p10_T p10_t 6 (p10_D6.map Prod.fst) ((p10_D7.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C7x1 : levelOK true p10_T p10_t 6 (p10_D6.map Prod.fst) ((p10_D7.drop (1*32)).take 32) = true := by decide +kernel
theorem p10_I7 : LevelN true p10_T 7 p10_D7 := levelStep p10_B p10_W p10_I6 (chunks 32 p10_D7 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C7x0
  · exact p10_C7x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C8x0 : levelOK true p10_T p10_t 7 (p10_D7.map Prod.fst) ((p10_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p10_I8 : LevelN true p10_T 8 p10_D8 := levelStep p10_B p10_W p10_I7 (chunks 32 p10_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C8x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C9x0 : levelOK true p10_T p10_t 8 (p10_D8.map Prod.fst) ((p10_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p10_I9 : LevelN true p10_T 9 p10_D9 := levelStep p10_B p10_W p10_I8 (chunks 32 p10_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C9x0
  ))
theorem p10_L : LowN true p10_R p10_T 10 := lowSearch p10_B p10_I9 (by decide +kernel)
def p11_T : Nat := 0xfffffffffffffcfcffffffeafeeafcc0fffffffffffffcfcffffffeafeeafcc0
def p11_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p11_E : List (Nat × Nat × Nat) := [(0,16,17),(1,4,6),(2,2,6),(3,2,10),(4,1,17),(5,1,33),(6,2,66)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
def p11_Z : List SliceD := [(pw5,10,[4, 5, 6, 1, 2, 0])]
theorem p11_Y : ∀ s ∈ p11_Z, SliceN true p11_R p11_T s := by
  unfold p11_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p11_B p10_B p10_L (by decide +kernel),by simp⟩
def p11_C : List (Nat × List Nat) := [(0,[])]
def p11_t : Tabs := (p11_C.map (mkCut true p11_Z),[],[],[[]])
theorem p11_W : TabsP true p11_R p11_T p11_t := ⟨cutsGood p11_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D10 : List StD := [
([pw0,pw1,pw2,pw3,pw8,pw97,pw127],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p11_D9 : List StD := []
theorem p11_I9 : LevelN true p11_T 9 p11_D9 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C10x0 : levelOK true p11_T p11_t 9 (p11_D9.map Prod.fst) ((p11_D10.drop (0*32)).take 32) = true := by decide +kernel
theorem p11_I10 : LevelN true p11_T 10 p11_D10 := levelStep p11_B p11_W p11_I9 (chunks 32 p11_D10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C10x0
  ))
theorem p11_L : LowN true p11_R p11_T 11 := lowSearch p11_B p11_I10 (by decide +kernel)
def ptopT : Nat := 0xfffffffffffffffefffffffffffefffafffffefeffffeeeefefefefeeeee0000
def ptopR : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def ptopE : List (Nat × Nat × Nat) := [(0,16,17),(1,16,18),(2,32,36),(3,128,136),(4,1,17),(5,1,33),(6,1,65),(7,1,129)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(pw5,11,[2, 4, 6, 1, 7, 5, 0])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) ptopB p11_B p11_L (by decide +kernel),by simp⟩
def ptopC : List (Nat × List Nat) := [(0,[])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
([pw0,pw1,pw2,pw3,pw8,pw97,pw127,pw128],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def ptopD10 : List StD := []
theorem ptopI10 : LevelN true ptopT 10 ptopD10 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC11x0 : levelOK true ptopT ptopt 10 (ptopD10.map Prod.fst) ((ptopD11.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI11 : LevelN true ptopT 11 ptopD11 := levelStep ptopB ptopW ptopI10 (chunks 32 ptopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC11x0
  ))
theorem ptopL : LowN true ptopR ptopT 12 := lowSearch ptopB ptopI11 (by decide +kernel)

def theInputs : List Sig := rootsW [0,1,2,3,4,5,6,7]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
def sample (r : Row) (i : Fin 8) : Bool := bit r (theInputs.getD i.val zero)
theorem theList : List.ofFn (fun i : Fin 8 => theInputs.getD i.val zero) = theInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = theInputs.map (bit r) := by
  rw [←theList,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem theTable : ∀ r : Row, bit r graph = target (sample r) := by decide +kernel
theorem theEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates theInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k theInputs.toFinset := by
  have b := baseOK_ok ptopB
  have goalEq : (execute C.gates theInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (theEval C legal C.output r).trans ((computes (sample r)).trans (theTable r).symm)
  have out := get_rep (u:=true) (execute C.gates theInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W ptopT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates theInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : theInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = theInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run theInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes : Impossible true graph 11 theInputs.toFinset := by
  intro k small run
  have steps := list_run run theInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (theInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega
theorem replaceShort (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · refine ⟨gates,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨ops,arity⟩ := fit g hg
    refine ⟨?_,arity⟩
    rcases ops with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact (mono g hg c).elim
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (excludes k (by omega) run).elim

end PEqualNP.Outside.L_meta_15012

theorem PEqualNP.Outside.L_meta_15012 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_15012.replaceShort gates o fit correct
