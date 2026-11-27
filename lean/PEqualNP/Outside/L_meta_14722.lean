import PEqualNP.Defs





namespace PEqualNP.Outside.L_meta_14722
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def limbs64 (ws : List Nat) : Nat := ws.foldl (fun v w => (v <<< 64) + w) 0
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

def inputs : List Sig := [(BitVec.ofNat _ (limbs64 [0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa])),(BitVec.ofNat _ (limbs64 [0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc])),(BitVec.ofNat _ (limbs64 [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0])),(BitVec.ofNat _ (limbs64 [0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00])),(BitVec.ofNat _ (limbs64 [0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000])),(BitVec.ofNat _ (limbs64 [0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0x0,0x0]))]
def graph : Sig := (BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xfffffefefffffefc,0xfffefffefffefffa,0xfefefefeeeccaa00,0xffffffffffffffff,0xfffffefefffffefc,0xfffefffefffefffa,0xfefefefeeeccaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
 (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 6 && x 7)
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
 (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  | 0 => (limbs64 [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1])
  | 1 => (limbs64 [0x1,0x0,0x1,0x0,0x1,0x0,0x1])
  | 2 => (limbs64 [0x1,0x1,0x0,0x0,0x1,0x1])
  | 3 => (limbs64 [0x1,0x0,0x0,0x0,0x1])
  | 4 => (limbs64 [0x1,0x1,0x1,0x1])
  | 5 => (limbs64 [0x1,0x0,0x1])
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



def paidSliceChoices (d : Sig) (pool : List Sig) : List Choice → List Choice
  | [] => []
  | c :: hist =>
    if availableB true d pool (choiceVal c) then paidSliceChoices d pool hist
    else c :: paidSliceChoices d (choiceVal c :: pool) hist

def zeroSliceOK (m s : Nat) : Bool :=
  let fixed := m - s
  let moves := fixRows fixed 0
  properB (graphGoal s) && (movedWord moves (subcube fixed 0) == one &&
    checkMap moves (vars m) (graphGoal m) (vars s) (graphGoal s))

theorem zeroSlice_sound {m s l} (ok : zeroSliceOK m s = true)
    (prior : Lower true (vars s) (graphGoal s) l) :
    Slice true (vars m) (graphGoal m) (subcube (m - s) 0) l := by
  simp only [zeroSliceOK, Bool.and_eq_true, beq_iff_eq] at ok
  exact slice_correct ok.2.2 ok.2.1 (proper_of _ ok.1) prior


def mixedPairs (support hints : Nat) : List (Sig × Row × Row) :=
  (selected support).map fun (i, w) =>
    let j := (hints >>> (4 * i)) &&& 15
    let r : Nat := if j < 9 then 1 <<< j else 0
    (w, Fin.ofNat 512 r, Fin.ofNat 512 (r ||| (1 <<< i)))

def mixedColumnOK (m z o q support hints L base : Nat) : Bool :=
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (graphGoal m) (vars free) G &&
    (movedWord ms (subcube z o) == one) &&
    (if q = 0 then checkEssential G (vars free) xs && decide (L ≤ count - 1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ base + count))

theorem mixedColumn_sound {m z o q support hints L base : Nat}
    (prior : Lower true (vars q) (graphGoal q) base)
    (ok : mixedColumnOK m z o q support hints L base = true) :
    Slice true (vars m) (graphGoal m) (subcube z o) L := by
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  change (((properB G && checkMap ms (vars m) (graphGoal m) (vars free) G) &&
    (movedWord ms (subcube z o) == one)) && _) = true at ok
  simp only [Bool.and_eq_true, beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have h := ok.2
  by_cases hq : q = 0
  · simp only [hq, if_true, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lower_count (proper_of _ ok.1.1.1) xs h.1 p bank hr ha)
  · simp only [hq, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lift_ok h.1.2 (proper_of _ ok.1.1.1) (proper_of _ h.1.1) prior p bank hr ha)

theorem mixedBaseZero : Lower true (vars 0) (graphGoal 0) 0 :=
  fun _ _ _ _ => Nat.zero_le _

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


abbrev Bits := BitVec 1024
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 1024 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 1024 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 1024 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 1024 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 1024) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
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
 (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 1024) :
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
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
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
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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


def compactNext (path : Nat) (ws : List Decor) (hist : List Choice) :
    List Decor × List Choice :=
  let a := ws.getD (path &&& 31) defaultDecor
  let b := ws.getD ((path >>> 5) &&& 31) defaultDecor
  let d := (path >>> 10) &&& 3
  (ws ++ [dbin d a b], hist ++ [(d, a.1, b.1)])

def walkCompact : Nat → Nat → List Decor → List Choice → List Decor × List Choice
  | 0, _, ws, hist => (ws, hist)
  | depth + 1, path, ws, hist =>
    let next := compactNext path ws hist
    walkCompact depth (path >>> 12) next.1 next.2

theorem walkCompact_faithful (depth path : Nat) (ws : List Decor) (hist : List Choice)
    {r s} (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ (walkCompact depth path ws hist).1, faithful r s v := by
  induction depth generalizing path ws hist with
  | zero => exact base
  | succ depth ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hb | hz
    · exact base _ hb
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def rowWires : List Decor → Nat → List Decor
  | [], _ => []
  | v :: bank, mask =>
    if mask.testBit 0 then v :: rowWires bank (mask >>> 1)
    else rowWires bank (mask >>> 1)

theorem rowWires_faithful (bank : List Decor) (mask : Nat) {r s}
    (base : ∀ v ∈ bank, faithful r s v) :
    ∀ v ∈ rowWires bank mask, faithful r s v := by
  induction bank generalizing mask with
  | nil => simp [rowWires]
  | cons v bank ih =>
    have hv := List.forall_mem_cons.mp base
    unfold rowWires
    split
    · exact List.forall_mem_cons.mpr ⟨hv.1, ih _ hv.2⟩
    · exact ih _ hv.2

def compactPool (m : Nat) (domain : Sig × Nat) (hist : List Choice) : Option BoundPool :=
  materialize true (vars m) (paidSliceChoices domain.1 (vars m) hist) domain.1 domain.2

theorem compactPool_sound {m : Nat} {domain : Sig × Nat} {hist : List Choice} {pool : BoundPool}
    (slice : Slice true (vars m) (graphGoal m) domain.1 domain.2)
    (ok : compactPool m domain hist = some pool) :
    ValidPool true (vars m) (graphGoal m) pool :=
  materialize_sound slice ok

abbrev CompactGrid := Nat × Nat × (Nat → Bits) × (Nat → Bits)
def CompactGrid.mask (g : CompactGrid) := g.1
def CompactGrid.top (g : CompactGrid) := g.2.1
def CompactGrid.pos (g : CompactGrid) := g.2.2.1
def CompactGrid.neg (g : CompactGrid) := g.2.2.2

abbrev CompactTable := (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → List Nat) × (Nat → Nat → List Nat)
def CompactTable.count (t : CompactTable) := t.1
def CompactTable.path (t : CompactTable) := t.2.1
def CompactTable.live (t : CompactTable) := t.2.2.1
def CompactTable.picks (t : CompactTable) := t.2.2.2.1
def CompactTable.bucket (t : CompactTable) := t.2.2.2.2

def chartAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  let bank := walkCompact (g.top-k) (t.path k i) (rawDecor g.mask g.pos g.neg) []
  (rowWires bank.1 (t.live k i), bank.2)

def wordsAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  (chartAt g t k i).1.map Prod.fst

abbrev Domains := Array (Sig × Nat)
abbrev Perms := Array (List Nat)

def selectedHistory : List Choice → Nat → List Choice
  | [], _ => []
  | a :: rest, mask =>
    if mask.testBit 0 then a :: selectedHistory rest (mask >>> 1)
    else selectedHistory rest (mask >>> 1)

def poolList (m : Nat) (dom : Domains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d => compactPool m d (selectedHistory h (j / dom.size))))

theorem poolList_valid {m dom h picks} (valid : ∀ d ∈ dom, Slice true (vars m) (graphGoal m) d.1 d.2) :
    ∀ pool ∈ poolList m dom h picks, ValidPool true (vars m) (graphGoal m) pool := by
  intro pool hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  cases e : dom[j % dom.size]? with
  | none => simp [e] at hj
  | some d =>
    simp only [e,Option.bind_some] at hj
    exact compactPool_sound (valid d (Array.mem_of_getElem? e)) hj

def applySwaps : List Nat → List Sig → List Sig
  | [], xs => xs
  | p::ps,xs => xs.map (movedWord ((p::ps).map swapRows))

theorem applySwaps_valid {T k xs} {p : List Nat}
    (ok : autoOK T (p.map swapRows).reverse = true)
    (ih : Impossible true T k (List.toFinset xs)) :
    Impossible true T k (applySwaps p xs).toFinset := by
  cases p with
  | nil => exact ih
  | cons a p =>
    have := rotate_excluded ih (((a::p).map swapRows).reverse) ok
    simpa only [List.reverse_reverse,applySwaps] using this

def linkedCandidates (g : CompactGrid) (t : CompactTable) (perms : Perms) (k tag : Nat) :=
  (t.bucket k tag).filterMap (fun code =>
    let name := code / perms.size
    if name < t.count k then
      perms[code % perms.size]?.map (fun swaps => applySwaps swaps (wordsAt g t k name))
    else none)

theorem linkedCandidates_valid {g t perms k}
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset) :
    ∀ tag xs, xs ∈ linkedCandidates g t perms k tag → Impossible true (graphGoal g.mask) k xs.toFinset := by
  intro tag xs hx
  obtain ⟨code,_,he⟩ := List.mem_filterMap.mp hx
  dsimp only at he
  split at he
  next small =>
    cases eq : perms[code % perms.size]? with
    | none => simp [eq] at he
    | some p =>
      simp only [eq,Option.map_some,Option.some.injEq] at he
      subst xs
      exact applySwaps_valid (autos p (Array.mem_of_getElem? eq)) (prev _ small)
  next => contradiction

theorem cachedLiveSize {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega


abbrev NodePool := BoundPool × List Sig × List Sig × Nat

def cacheOnePool (u : Bool) (front : List Sig) (p : BoundPool) : NodePool :=
  (p, front.filter (fun a => !(availableB u p.domain p.wires a)),
    p.wires.map (masked p.domain), front.countP (isMaskedConstant p.domain))

def maskedAvailable (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || pool.any (fun v => v==m) ||
    (u && (let c := masked d (neg a); pool.any (fun v => v==c)))

def cachedPoolCut (u : Bool) (a : NodePool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let (c,missing,bank,maxCon) := a
  if c.bound + maxCon + 1 ≤ k + c.paid then false else
  let z := choiceVal op
  let con := c.bound + (z::rest).countP (isMaskedConstant c.domain)
  if con ≤ k+c.paid then false else
  let extra := !(maskedAvailable u c.domain bank z)
  (decide (k+c.paid+extra.toNat < con) &&
   missing.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!missing.contains op.2.1 && !missing.contains op.2.2)))

theorem cachedCut_ok {u p k rest op front}
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedPoolCut u (cacheOnePool u front p) k rest op = true) :
    scalarPoolCut u p k rest op = true := by
  let miss := front.filter (fun a => !(availableB u p.domain p.wires a))
  let extra := !(availableB u p.domain p.wires (choiceVal op))
  have know (w) (hm : w ∈ front) (hn : w ∉ miss) : availableB u p.domain p.wires w = true := by
    by_contra h
    apply hn
    apply List.mem_filter.mpr
    exact ⟨hm, by simpa using h⟩
  dsimp only [cachedPoolCut, cacheOnePool] at ok
  split at ok
  · contradiction
  split at ok
  · contradiction
  change ((_ && miss.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!miss.contains op.2.1 && !miss.contains op.2.2)))) = true at ok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at ok
  change ((_ && rest.all (availableB u p.domain p.wires)) && (!extra || choiceOK u p.domain p.wires op)) = true
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨ok.1.1, ?_⟩, ?_⟩
  · intro w hw
    apply know w (sub w hw)
    intro no
    have contra := ok.1.2 w no
    simpa [hw] using contra
  · rcases ok.2 with h | ⟨allowed, ah, bh⟩
    · exact Or.inl h
    · right
      simp only [choiceOK, Bool.and_eq_true]
      exact ⟨allowed, know _ ha (by simpa using ah), know _ hb (by simpa using bh)⟩

def cachedClose (u : Bool) (pools : List NodePool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  pools.any (fun p => cachedPoolCut u p k rest op) ||
    (let ws := choiceVal op::rest; (links (keySet ws)).any (sameWords ws))

theorem cachedClose_sound {u raw T} {pools : List BoundPool} {links k rest op front}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op::rest).Nodup)
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedClose u (pools.map (cacheOnePool u front)) links k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  simp only [cachedClose,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with ⟨c,hc,cut⟩ | ⟨w,hw,eq⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    exact scalarPoolCut_sound (pValid p hp) nd (cachedCut_ok sub ha hb cut)
  · rw [sameWords_sound eq]
    exact lValid _ _ hw

abbrev cached_NodeContext := Nat × Nat × List Decor × CovPair × List NodePool × (Nat → List (List Sig))
def cached_evalMove (c : cached_NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      cachedClose cov.2 pools links (cap-1) rest (movedChoice op a b)

def cached_moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem cached_evalMove_sound {u raw T r s ws} {pools : List BoundPool} {links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : cached_evalMove (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (cached_moveFront ws op a b ka kb).toFinset := by
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
  have hsz := cachedLiveSize h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold cached_evalMove at test
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact cachedClose_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc (sub.map _).subset (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) test k hk h

def cached_testPair (ctx : cached_NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := cached_evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def cached_opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem cached_opsOf_mem {u d} (h : allowed u d) : d ∈ cached_opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [cached_opsOf]
  · cases u <;> simp [cached_opsOf]
  · simp [cached_opsOf]
  · simp [cached_opsOf]
def cached_testRow (ctx : cached_NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (cached_opsOf ctx.2.2.2.1.2).all (cached_testPair ctx a b))
def cached_testAll (ctx : cached_NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => cached_testRow ctx a bs && cached_testAll ctx bs

theorem cached_all_binary {ctx ws} (h : cached_testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [cached_testAll,Bool.and_eq_true,cached_testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (cached_opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (cached_opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem cached_testPair_at {ctx a b d} (h : cached_testPair ctx a b d = true) (ka kb : Bool) :
    cached_evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [cached_testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem cached_keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem cached_mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem cached_unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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

theorem cached_kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,cached_mem_delone wn,cached_mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem cached_binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (cached_moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [cached_moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_kept_value nd ha hb,cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem cached_childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem cached_node_sound {u raw T r s ws} {pools : List BoundPool} {links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : cached_testAll (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) ws = true) :
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
      (test : cached_testPair (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←cached_binary_front nd aa bb ne']
    exact cached_evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (cached_testPair_at test ka kb)
  rcases cached_all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [cached_childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)



def compactNode (g : CompactGrid) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))

theorem compactNode_sound {g t dom perms k i}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) (wordsAt g t (k-1) j).toFinset)
    (check : compactNode g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  simp only [compactNode,Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ wordsAt g t k i := by simpa [wordsAt] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ (chartAt g t k i).1, faithful (asRow g.pos) (asRow g.neg) v :=
      rowWires_faithful _ (t.live k i) (walkCompact_faithful (g.top-k) (t.path k i)
        (rawDecor g.mask g.pos g.neg) [] (raw_faithful g.mask g.pos g.neg))
    apply cached_node_sound pairs f check.1 out (poolList_valid valid) (linkedCandidates_valid autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2


def chartBlock (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && chartBlock test start n

theorem chartBlock_at {test start n} (ok : chartBlock test start n = true) (i)
    (a : start ≤ i) (b : i < start+n) : test i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [chartBlock,Bool.and_eq_true] at ok
    by_cases h : i=start+n
    · simpa only [h] using ok.1
    · exact ih ok.2 (by omega)

theorem chartBlock_join {test start a b}
    (left : chartBlock test start a = true) (right : chartBlock test (start+a) b = true) :
    chartBlock test start (a+b) = true := by
  induction b with
  | zero => simpa using left
  | succ b ih =>
    simp only [chartBlock,Bool.and_eq_true] at right
    simp only [Nat.add_succ,chartBlock,Bool.and_eq_true]
    constructor
    · change test (start + (a+b)) = true
      rw [← Nat.add_assoc]
      exact right.1
    · exact ih right.2

theorem compactAll {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact compactNode_sound pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact compactNode_sound pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))

theorem compactPairs {g : CompactGrid}
    (yes : liftGoal g.mask g.pos = BitVec.allOnes 1024) (no : liftGoal g.mask g.neg = 0) :
    properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg) := by
  intro i
  constructor
  · rw [bit_liftGoal,yes,BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  · rw [bit_liftGoal,no]
    simp

abbrev SliceSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def specDomain (s : SliceSpec) : Sig × Nat :=
  (subcube s.1 s.2.1, s.2.2.2.2.2.1)

def certifiesSlice (m : Nat) (earlier : List (Nat × Nat)) (s : SliceSpec) : Bool :=
  let (z,o,q,support,hints,L,base) := s
  ((q == 0 && base == 0) || earlier.contains (q,base)) &&
    ((z == m-q && o == 0 && L == base && zeroSliceOK m q) ||
      mixedColumnOK m z o q support hints L base)

theorem certifiesSlice_sound {m earlier s}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : certifiesSlice m earlier s = true) :
    Slice true (vars m) (graphGoal m) (specDomain s).1 (specDomain s).2 := by
  obtain ⟨z,o,q,support,hints,L,base⟩ := s
  simp only [certifiesSlice,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,
    List.contains_eq_mem,decide_eq_true_eq] at ok
  have lower : Lower true (vars q) (graphGoal q) base := by
    rcases ok.1 with ⟨rfl,rfl⟩ | he
    · exact mixedBaseZero
    · exact prior (q,base) he
  rcases ok.2 with ⟨⟨⟨rfl,rfl⟩,rfl⟩,h⟩ | h
  · exact zeroSlice_sound h lower
  · exact mixedColumn_sound lower h

theorem compactDomains_valid {m earlier specs ds}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : List.all specs (certifiesSlice m earlier) = true)
    (matchDs : (specs.map specDomain).toArray = ds) :
    ∀ d ∈ ds, Slice true (vars m) (graphGoal m) d.1 d.2 := by
  subst ds
  intro d hd
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
  exact certifiesSlice_sound prior (List.all_eq_true.mp ok _ hs)

theorem compactAutos_valid {T : Sig} {ps : Perms}
    (ok : ps.toList.all (fun p => autoOK T (p.map swapRows).reverse) = true) :
    ∀ p ∈ ps, autoOK T (p.map swapRows).reverse = true := by
  intro p hp
  exact List.all_eq_true.mp ok _ (Array.mem_toList_iff.mpr hp)

theorem compactRoot {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : wordsAt g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact compactAll pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot

def eightInputs := inputs.take 8
def sample8 (r : Row) (j : Fin 8) := bit r (eightInputs.getD j.val zero)
def edge8 (x : Fin 8 → Bool) : Bool :=
 (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 6 && x 7)
theorem edgeTable8 : ∀ r : Row, bit r graph = edge8 (sample8 r) := by decide +kernel
theorem inputList8 : List.ofFn (fun j : Fin 8 => eightInputs.getD j.val zero) = eightInputs := rfl
theorem sampled8 (r : Row) : List.ofFn (sample8 r) = eightInputs.map (bit r) := by
  rw [←inputList8]
  rw [List.map_ofFn]
  rfl

theorem eval8 (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sample8 r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled8]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 1, 0, 0, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 1, 0, 0, 1] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=edge8 x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eval8 C legal C.output r).trans ((computes (sample8 r)).trans (edgeTable8 r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←inputList8] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩


def readCompactBits (table : Nat → Nat) (start width : Nat) : Nat :=
  let i := start / 4096
  let j := start % 4096
  let low := table i >>> j
  let result := if j + width ≤ 4096 then low else low ||| (table (i+1) <<< (4096-j))
  result &&& ((1 <<< width)-1)

def compactIDsFromBits (bits width : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (bits &&& ((1 <<< width)-1)) :: compactIDsFromBits (bits >>> width) width n

def samplesP146 : Nat → Bits
  | 1 => ~~~(0x2114 : Bits)
  | 4 => 0xef9e
  | 7 => ~~~(0x408a : Bits)
  | _ => 0

def samplesQ146 : Nat → Bits
  | 1 => ~~~(0xdbfc : Bits)
  | 4 => 0x1818
  | 7 => 0x4224
  | _ => 0

def compactPerms146 : Array (List Nat) := ([[], [116], [65], [65, 116], [113, 116], [113]] : List (List Nat)).toArray

def compactDomains146 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords146 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount146 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath146 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive146 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords146 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs146 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords146 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords146 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket146 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP210 : Nat → Bits
  | 1 => ~~~(0xa018a5120b83274 : Bits)
  | 4 => 0x5effc55fb6de8b4e
  | 6 => 0x78f1fa0feba03f30
  | 7 => ~~~(0x100045028206890a : Bits)
  | _ => 0

def samplesQ210 : Nat → Bits
  | 1 => ~~~(0x75ed7dbb3bdf33fc : Bits)
  | 4 => 0x2124182a108a1348
  | 6 => 0x746919c232adf10
  | 7 => 0x10800401084000a4
  | _ => 0

def compactPerms210 : Array (List Nat) := ([[], [65]] : List (List Nat)).toArray

def compactDomains210 : Array (Sig × Nat) := ([(subcube 64 0, 4)] : List (Sig × Nat)).toArray

def compactWords210 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount210 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath210 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive210 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords210 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs210 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords210 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords210 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket210 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP216 : Nat → Bits
  | 3 => ~~~(0x44310ac4811d7236 : Bits)
  | 4 => 0xf3f570ff978d1fa2
  | 6 => ~~~(0x100030c2060d18a2 : Bits)
  | 7 => 0xdffbbafeef1d7af6
  | _ => 0

def samplesQ216 : Nat → Bits
  | 3 => 0x44a942a944139cc8
  | 4 => 0xd289c3201a4b7a0
  | 6 => ~~~(0xedff6faf67dbdcfa : Bits)
  | 7 => 0x2041410c22130852
  | _ => 0

def compactPerms216 : Array (List Nat) := ([[], [67, 118]] : List (List Nat)).toArray

def compactDomains216 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords216 : Nat → Nat
  | 0 => 0xf
  | _ => 0

def compactCount216 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath216 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive216 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords216 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs216 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords216 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords216 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket216 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP218 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x8a0188071,0x81caa01008300830,0xfe0778cf748019e3,0x3108ffa01e11b5ec])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0x5ecfd9ef5f,0x8d601fbdfebc369e,0xd64770891eefc96b,0xb4bfe18010bf7444]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x7daffed769,0xe3ba5fde6ff1cf6d,0xe986f6227ff67d92,0xf9cc067c8335b91a]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7b3fbffcf3,0x74c0bff7b9fe1831,0xffff08cd17fbb7ef,0xf18f9801dc9ace4]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x110000444b,0x64204084208c160d,0xc1c606a90262250a,0x8c9ce1dc91ad2856])) : Bits)
  | _ => 0

def samplesQ218 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x775db57faf,0x7f75d55fbfbf7ef5,0x9b6adfb5ffa4b9f7,0xbf5faef63e31fffc])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0x21312b1420,0x520cf9050422b855,0x4cd2a5045accc140,0x240648e932b75440]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x254210982,0x845940809846a11,0x248988097242810,0x810822441621b910]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x4c840890c,0x11306123004430a,0x220d103025330083,0xa103304c548a824]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1100801401,0x2420414082121044,0x802020108809024,0x104108a020104688]))
  | _ => 0

def compactPerms218 : Array (List Nat) := ([[], [65]] : List (List Nat)).toArray

def compactDomains218 : Array (Sig × Nat) := ([(subcube 8 0, 5), (subcube 0 8, 5), (subcube 2 0, 4), (subcube 16 0, 4), (subcube 64 8, 4)] : List (Sig × Nat)).toArray

def compactWords218 : Nat → Nat
  | 0 => (limbs64 [0x368c,0xfff7fbfc16f28901,0x3fc7f83b658858f1,0x5a79fe092503dfff,0xfc0220220140d41f])
  | _ => 0

def compactCount218 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 3
  | 4 => 1
  | _ => 0

def compactPath218 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords218 (23 + 12*i) 12
  | 4 => let v := readCompactBits compactWords218 (202 + 12*i) 12
    (readCompactBits compactWords218 (190 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive218 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords218 (0 + 5*i) 5
  | 5 => readCompactBits compactWords218 (59 + 6*i) 6
  | 4 => readCompactBits compactWords218 (214 + 7*i) 7
  | _ => 0

def compactPoolIDs218 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords218 (17 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords218 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords218 (85 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords218 (77 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords218 (221 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords218 (221 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket218 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords218 (100 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords218 (102 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 4 => let d := readCompactBits compactWords218 (223 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits compactWords218 (225 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP155 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0xac05001b024,0x77f00820c04e6bd9,0x8014cfae20205206,0x62c752df7c92c4f6])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0xf9dff8fff217,0xbcffcbffdfdef7fb,0x840c3f88e6efcac6,0x1fef024f79cfc2a6]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x213008c20a83,0xb3f0014015cc3494,0x544c3fae04410fc2,0xd9052df7d4123f6])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xbf6fffcbe9ab,0x773fff72fc6d6ed5,0x5756fd263ffb7fa7,0x669452dc45923f74]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xeebfdff79ee4,0xf3cffdedf5ce399c,0xf8fdc2aefd75d75a,0xe9d350933e71e5d2]))
  | _ => 0

def samplesQ155 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0xf5378eeecfff,0xaeaabbbcffae93a5,0x67e4fe7db32c7efe,0x7af79eaf169ad4fe])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x62243400960,0x30302a004842048,0x11235030004ec0c2,0x12400505614e8006]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x21310a624082,0xa2aaa01882a610a5,0x25645a04b32c4030,0x402686a5169ad408]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x409408310614,0xcc08003a524004,0x2c1c00481ea03a04,0x10e24004803e60]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1140b0024009,0xc30d10440211cb3,0x80400401e1110408,0x288100b09a314190]))
  | _ => 0

def compactPerms155 : Array (List Nat) := ([[], [116], [65], [65, 116], [113, 116], [113], [48], [48, 116], [48, 65], [48, 65, 116], [48, 113, 116], [48, 113]] : List (List Nat)).toArray

def compactDomains155 : Array (Sig × Nat) := ([(subcube 0 1, 5)] : List (Sig × Nat)).toArray

def compactWords155 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount155 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath155 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive155 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords155 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs155 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords155 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords155 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket155 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP219 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x152002a,0x20065802a8558e4f,0x70c0204040608204,0xcc10385483d605e1,0x67e44ee706c9361b,0xeb770060a0016480,0xf42c680330016be4,0xcb7c530ec4307f20,0xb9636d72f7e3df25,0x8540e887091133e,0xab86bad5cbee76f,0xdb97b9295c9535ee])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x5fb6ffff,0xf8efd9c76bb13e23,0x49bffe5dfffbce01,0xc3f8f83e7ffeffe7,0xe0cc31e774c3ce01,0x29217ffff577e3cf,0xfefbe9870cffefe7,0xf8fc1f03c07000f0,0x79601d0c76600813,0x44f3ffbdf7908702,0x7a1c1f7f3c000127,0xdb903b9bc40ea046]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x4a10040,0x8c684d003b161f9,0xcd000a0890002451,0x4378b00678852810,0x322930edf0a76bb3,0xaffa11000052c254,0x48011ba504778b8e,0x7596e2d821ee14f8,0xf1681d0cfef9cd60,0x54b343100a37cf93,0x720d0dd882c6e16f,0xdffbea84aa4efee6])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x776bfd6f,0xffd6f5b6b75da15a,0xa47ffffbf377afd4,0xef16b7d5fa95edd7,0x16a34cdc6aab2792,0x8121f779bfff5ebc,0xcda77f67b2f1139a,0xc3f652caa42e7428,0xf68b4e7c6440852d,0xfed72e7b4efd56b3,0x449b68e8d080c16f,0x1200a3253bb65064]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x6ff3fffe,0x6ff75e78dbd143fd,0x71ffeffefdfc35ff,0x7fff78fe8bdf0338,0x273476e5847439e8,0x46dffdeeeaffe751,0xf32d1bfbff20e84c,0xd03e0bc3fe37ff3,0xb961e902899b524c,0xddfddf847877eb7c,0x9aa50b81427e2600,0x46f780c38cd8f88]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7dddfefb,0xbffeaedbace6cccd,0xde3ffbefdeeff27f,0xdc79bf47f5e73cf8,0x7b698a2b938d7233,0xaa539bf7ffdafcf6,0x7c5cfebd75470ba4,0x771ce35c419c9f0c,0x817e35f292a1cd37,0x3b3e43dabba3199f,0x2368e59c8e86e048,0xc9938ce0ce5174a2]))
  | _ => 0

def samplesQ219 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x7eadeddd,0x9efde7fdffbaf5f1,0x8f2dafdf7e7f47fa,0x4fefbf6a77c9f9de,0xbfdff9fafdbefff5,0x9f997a6facb97fde,0xf7fd7dff3fde7bab,0x397fac4efbacffd3,0x7ffd647df9ffbcf5,0xad55eecdf0f9ffbe,0xeffd7fafdf3edf57,0xc3e7fd397d95b7fe])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x20498002,0x13500428840e81c8,0xb40b02144200e2c8,0x3525124520122004,0x150288000024205a,0x90925ccd9003200a,0x400018108420142,0x601019926901324a,0x12452ba40882a000,0xa1da95e5808300,0x6808102400140c82,0x5b087a9b40088006]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x4a14044,0xa648010029061f1,0x8928810028420498,0x45a29a022489090a,0x20120a050800131,0x7994a432c281100,0xa0c04050200a1928,0x1905044488a0a641,0x5a4c442450110415,0x2144a8c990c02028,0x500420219120b52,0x4084953155110110]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x8940630,0x8828024048205c25,0x4ab40c4100041407,0x4098c91814614448,0x280c010280101805,0x2e4522300af40090,0x1050c06009924a8,0x8521606406648134,0x48a214108104084c,0xee52242808781402,0x110080c1894121,0x42581043bb61040]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x100c0810,0x90102085202a9400,0x605200210184242,0xd014810406044,0x80c00008090a4204,0x9800302c80900640,0x4228002003102082,0x2030280263041112,0xa1201100600020,0x8c11460460204810,0x80a40901000c4401,0x321680828848288]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x2222044,0x6001410011112212,0x140c08804210810,0x80020082888c0b22,0x10505024008480,0x4128810265084804,0x1010300814009814,0x1a84060180920401,0x8008c00220081093,0x110c014212010084,0x240240806422258,0x2090046084416420]))
  | _ => 0

def compactPerms219 : Array (List Nat) := ([[], [65], [16, 67, 118], [16, 49, 67, 118], [48], [48, 65], [64, 65, 67, 118], [64, 49, 118]] : List (List Nat)).toArray

def compactDomains219 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 8 0, 7), (subcube 16 0, 7), (subcube 64 0, 6), (subcube 128 0, 6), (subcube 0 1, 6), (subcube 0 2, 6), (subcube 0 8, 6), (subcube 0 16, 6), (subcube 9 0, 5), (subcube 1 8, 5), (subcube 2 16, 5), (subcube 64 1, 5), (subcube 64 8, 5), (subcube 128 2, 5), (subcube 128 16, 5), (subcube 65 8, 4)] : List (Sig × Nat)).toArray

def compactWords219 : Nat → Nat
  | 0 => (limbs64 [0xb5fe3fc3fcff1fe3,0x4f7f80bffe02b3d0,0x3425cc24045388ff,0x4bd046305835bfc,0x337a74e63380820,0xe4ba717ffc1fe0b6,0x3b697fc1fe07996d,0x363270f5ff07f820,0xd5308b87ff806214,0x7a201901114ac73b,0xa7fbbddddd4e6a09,0x6425338f30901209,0x60110950085e2619,0x7ff0082373e68a33,0xd45df0b36558145f,0xf00a0a3fc040beff,0x1d057fc014310e6,0xa381e313909ddf4d,0x6058e56deb75979f,0xe01a07e32a8b5264,0x33c2bf449759ffe0,0x1da5f3afd48f7439,0xf927f80ff01986e6,0xe34a3fd0455a53fc,0x2c9fe9328cebfc0,0x52cad029ed558,0x32a2518710c29351,0xc82942a8038d4844,0xf2432021c118017,0x83b718fe0fda5349,0x1871782432021c11,0x8e02499118756618,0x747937722498a187,0x5661872959861cab,0xfbeb7ffbfffffbbf,0xfffffa9881302261,0xb825698aa095212a,0xcc2304a5094a11c4,0x2c12402202201042,0xc18dff01fe002079,0x82dff00b29c6cce7,0x15365e5e13fc07f8,0x436ffe021416a1f,0xff011e1ffc028062,0x623fe022967f80ff,0x14c9bc1fab45985,0xdfe027d2171d9937,0xad1c789ff802d2f7,0x495b8a40c5022eb0,0x6582ab522070d2b8,0xdb03de0101a4480,0x9ea603a8f9c9a548,0xd02384c0ac28e9c9,0xedab928398620d1e,0x9c9a548903302ac,0x7d24d39523408c07,0x55ec0d1b23946912,0x27aae740122548d,0x71040dad1732194,0x5224670d66d118a4,0x48d0713eab6d0060,0xffffffffffffffff,0x8854850858244248,0x44044024018393f])
  | 1 => 0x4
  | _ => 0

def compactCount219 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 9
  | 7 => 11
  | 6 => 4
  | 5 => 1
  | _ => 0

def compactPath219 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords219 (20 + 12*i) 12
  | 7 => let v := readCompactBits compactWords219 (1671 + 15*i) 15
    (readCompactBits compactWords219 (1599 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords219 (3362 + 14*i) 14
    (readCompactBits compactWords219 (3290 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords219 (3964 + 12*i) 12
    (readCompactBits compactWords219 (3928 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive219 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords219 (0 + 6*i) 6
  | 8 => readCompactBits compactWords219 (128 + 7*i) 7
  | 7 => readCompactBits compactWords219 (1836 + 8*i) 8
  | 6 => readCompactBits compactWords219 (3418 + 9*i) 9
  | 5 => readCompactBits compactWords219 (3976 + 10*i) 10
  | _ => 0

def compactPoolIDs219 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords219 (14 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords219 (6 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 8 => let v := readCompactBits compactWords219 (861 + 13*i) 13
    let n := v >>> 8
    let bits := readCompactBits compactWords219 (191 + 5*(v &&& 255)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords219 (2332 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords219 (1924 + 6*(v &&& 127)) (6*n)
    compactIDsFromBits bits 6 n
  | 6 => let v := readCompactBits compactWords219 (3468 + 3*i) 3
    let n := v >>> 2
    let bits := readCompactBits compactWords219 (3454 + 7*(v &&& 3)) (7*n)
    compactIDsFromBits bits 7 n
  | 5 => let v := readCompactBits compactWords219 (3986 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords219 (3986 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket219 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords219 (978 + 4*(i % 9)) 4
    let off := ((i/9 + d) % 39)
    let v := readCompactBits compactWords219 (1014 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 7 => let d := readCompactBits compactWords219 (2453 + 3*(i % 14)) 3
    let off := ((i/14 + d) % 53)
    let v := readCompactBits compactWords219 (2495 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 6 => let d := readCompactBits compactWords219 (3480 + 4*(i % 8)) 4
    let off := ((i/8 + d) % 32)
    let v := readCompactBits compactWords219 (3512 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits compactWords219 (3988 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords219 (3990 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

def samplesP251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x5ffdc4ffd3afdfe0,0x977ff32c85c19fcf,0xf500faff297ac01e,0x47fca8e857d7f580,0x7101ffef7aa10092,0x37eebc10952026c2,0xbb36d06a3d77fa5e,0x80000d7dc9b92d31,0x9fb033c1dc00bc,0xc006c2539b1b47,0xa492e5bce5297dc1,0x3b6fe113cf6ec03c,0xc3401ff42c05c7e8,0xa88ea0341e80041,0xe04885d45a162121,0xdd9298a5ac56a211]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xf46f16e0fd07fd7f,0xfbf3bff2d86fe438,0xd8c5f486f6c1c477,0x2dbf5506ec914ffc,0xab9e92fdddf457e5,0xccb918a00ec5d03d,0x5cc0199c403c6c80,0x1d0ceec2de42d007,0x9fe440741e222b00,0x2027883c6ca2e84e,0x33fc571b97cfdb6d,0x9ca34866e1902dd0,0x7c54e13882f4021c,0x8e678419a7807184,0x3937a2b8400449c,0xb127c05947d11846]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xfef3bf5fa3f8e5dc,0x6efdffd34ffef90c,0x5e5707b8395ddf93,0xfa23eaf5186df238,0x5eecc7f0605d0781,0xa03c03e943c15401,0xba59853c4fc01287,0x605b111d007d27f8,0xf1011fc84001800f,0x40d820c0fefd9fb8,0x7c6298ff19f691f8,0xb4f5dceb7c6f1127,0x19f020e3fe17a87,0x420d4e1a6278040,0xfc48040001017bc9,0x27634e4631a00119]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xbf0ffbd9efdf27bf,0x179fcd2f75b9617f,0xaaa81d1fe92731fd,0xbfc0a36fb7ae089f,0xeef3046f0501086c,0x73d3401176dea103,0x4962a55b2882559,0xffa402a22e390ace,0x1612fb218200240,0xe015119fb7ec559,0xdf11fb60fad163be,0x7b97be17b6d6be0b,0x5aa025c4107bbd10,0x1d58027e981000b8,0xb742022009bcf0,0xe21533263a4c4064]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x6b9ee9befef7fb7f,0xefedbedd226e1ab7,0x273aeb66dfbe3a68,0xd5bffe96fb694f63,0x2b9f6a92a20aa71a,0x746e74e193a083e,0xe32919e3803c5320,0x1d0ce102d1840007,0x9e1a8047801c2810,0x20260e20fffff6ef,0xcbef56db69cea692,0x475ab78d19e92de0,0x2054d8c3428a05e3,0x6197799a59807105,0x30081cc0811ffe2,0x48cc2c99498a9800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x8ffa7faf7c7bdadf,0xf87a4dfbfa119ef2,0x1bffeaf9d6953f84,0x424b57194796ba7f,0xd461fd1403def803,0x180007efa0002ffc,0x440de6823f438c2d,0x62f31e4d2746d0e8,0x605ee00c21c1d4a3,0xd1182002a757e5b7,0x77d2907de307e7f,0xc1681ff80f91d21c,0xbdab1a1bd1048057,0xf08f15e4004f8e02,0x1c00001053e7963e,0x878171a86302788]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xf1f5ff771ffc3ea3,0xfd8672fcbf9667c1,0xe5ff154106eaefeb,0xb8541dfba87ab5c7,0x957e390a9c22f87c,0xc801f816e83fdbc0,0x1e26601c08381f2,0x82f3f0b03082ff10,0x6ea05f8826025540,0x9f00d1059ded7ab0,0xf88faee4263f8c07,0xee9c63fcf20042c3,0x862be421ed1a7828,0xf3702b047e500e3a,0x243821a4e8cb47,0x1688e1e0d02d44a2]))
  | _ => 0

def samplesQ251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x50084450502c0440,0x9304012880400102,0x110010000010001a,0x8000810400000,0x7100000486800091,0x28114400d5200901,0xc4d0e80208098c,0x33231000221,0xc1504800220000,0x100290000000140,0xa01064a0c5290041,0x1a040113c100c020,0x140041000014040,0xa00000340180046,0x54863406100000,0xd41280a1a444a001]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x441104050029052,0x414128a208000008,0x4000840084000000,0x412000204110004,0x80880080a000423,0x81110410240011,0x304c40b064120004,0x4a10442a92108484,0x4841545101004002,0x880000000000004,0x248441285845864,0x8821484261002090,0x1410012800100200,0x424000001022804,0x524112270204001c,0x9123401105101006]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x28a1a2032310c118,0x6491f01406aca090,0xc49022a304658a1,0x820ac2009249329,0x42242a048199128,0x910c29222088c418,0x28230c0485148602,0x6c3a64010a588d08,0x2280612161488c4,0x902b5240dee99830,0x5062905c10d61130,0xa4c1d0a0346a0105,0x89404626a22884,0x200098a8aa233200,0x64a9108081096bc9,0x23414a4411a00110]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x920e8891a80c2384,0x129a010d42006874,0x2402211f118001e4,0x12a041652b80009b,0x80804863640c289c,0x94544051a9420584,0x4129d0202c82c32,0x10902d009c54200,0x1a22106a041ac4c,0x6201860a6b5ec159,0x41199207a01239a,0x1292841516961503,0x480028c2406a8181,0x1019027c003080d1,0x90c0183149bca0,0x601413263a484040]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x996212c86c16a29,0x2828964462883891,0x261b602b5b8a50a0,0x9ba56421a9805129,0x82a768a02130ca00,0x450a20990888504a,0x4710030311857020,0xa4863084408c1152,0x350ca28482c49c45,0x764b125cfffff68b,0x49a5020928428680,0x415a328c084a1d41,0x805584344a20da3,0x211b48ac0a811589,0x290008c82823ffe2,0x8cc2c08488a0800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x8740188c08431887,0x620cc040110c00,0x208228c101812400,0x5280421160820840,0x80800d1101046606,0xc010c400460086,0x1108001170431010,0x381004cc00140c6,0x6c060100c0400710,0x6200002921164486,0x70c09030200680e,0x1280e400a811408,0xa8200a0051040111,0x8099050400008c10,0x1b00400318469434,0x828151a02100288]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x6030472205b00420,0x8c044210118a0280,0x802d00200022d200,0x2840348000083520,0x72108080a11100,0x68020c2a44009840,0x4aa1024c8000c388,0x8024110120001839,0x120080880a0c0020,0x101e10c094a12a20,0xb88222c400388401,0x6404212880080200,0x203c0008c801808,0x604028801e48030a,0x42c0c4084304343,0x680a0c0c0250420]))
  | _ => 0

def compactPerms251 : Array (List Nat) := ([[], [67, 16, 118]] : List (List Nat)).toArray

def compactDomains251 : Array (Sig × Nat) := ([(subcube 32 0, 10)] : List (Sig × Nat)).toArray

def compactWords251 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount251 (k : Nat) : Nat := match k with
  | 10 => 1
  | _ => 0

def compactPath251 (k : Nat) (i : Nat) : Nat := match k with
  | 10 => 0
  | _ => 0

def compactLive251 (k : Nat) (i : Nat) : Nat := match k with
  | 10 => readCompactBits compactWords251 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs251 (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let v := readCompactBits compactWords251 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords251 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket251 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP214 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0xed7fd9f,0xcd5e60cfe7fbecfd,0xf983c13c10cffde5,0xc39d8007bcdd942c]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x40c0190,0x42556ed082024ce1,0x8643c3bd330c0aad,0x81d03c07bfc215fc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xfabfff8,0xaaf1e60fdee7fbe3,0xe763313103ffcb9c,0xb37a5c0730a77138]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xb01c00,0x8c28e7e0048183e3,0xf980017d57c00554,0x823e1c1ffc258f3c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xdfffff7,0x562dffffbf9fd7e3,0x9edccecd77fc367f,0x8cf63c18cf628fd4]))
  | _ => 0

def samplesQ214 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x1284470,0x30210e2360804c03,0x81c03c818444f0a0,0xc00c20607cd9800c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x40e00d2,0x2144c9a10508c4b,0xa09282822e2a140,0x2803094a6835c202]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x548883,0x410811dc0406216c,0x2a0d420250bb0814,0x2404d8b01267120]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xf4ef3de,0xf3ff5c9af5d7fedb,0x5e3bababfee2aff7,0xea7f5b5eea35cfbe])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x2002000,0x80c2000081011000,0x10008000603,0x30000000000c90]))
  | _ => 0

def compactPerms214 : Array (List Nat) := ([[], [98], [33, 100], [33, 66, 100], [65], [65, 98], [97, 98, 100], [97, 66]] : List (List Nat)).toArray

def compactDomains214 : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 4 0, 5), (subcube 16 0, 5), (subcube 64 0, 5), (subcube 18 0, 4), (subcube 68 0, 4)] : List (Sig × Nat)).toArray

def compactWords214 : Nat → Nat
  | 0 => (limbs64 [0x3a08c42a6,0xff83fc01c9d6791,0xd8717fe0e635dc39,0xa9813ff02cb3fc1f,0xe05d8c41df9bfe0f,0xf0765ffc1fe073aa,0x8ca955ac88b286b8,0xc80fe3d283048202,0x5e6e6dcc3b3084c2,0x4a44014a18040a44,0x1313ea278966c44,0x7ff01fe03fc07f80,0x662460d820504aff,0xf01fe0285aff80be,0x69012b7cbe80fef0,0x54eefa55b3b07b91,0xb2960d1bfcfbb7bf,0xe011477c33ff01fe,0x1dfff803473030,0xc2a67b163318c86b,0xfc02926ff00ed261,0x10f4318c29561ab0,0x27f806d4fbd07cd6,0x944e2496de92b507,0xf801b39fe01e629c,0x374064fca7e917f8,0xe90ffe000302444,0x18288320080c4003,0x66850a5098306490,0xc90a04c8c806ffb,0xb77ff7ebf7efdf92,0x85ca27289ca17280,0x40432908a412900a,0x4804404401063004,0x55de427ff040a6b1,0x65e2ff07f82cc9fe,0x3caff83fc1fe0ff,0x7f823db7171d980,0x4833551008321403,0x124098325401ffff,0xe0110110068ae11f])
  | _ => 0

def compactCount214 (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 3
  | 5 => 10
  | 4 => 3
  | _ => 0

def compactPath214 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits compactWords214 (26 + 12*i) 12
  | 5 => let v := readCompactBits compactWords214 (508 + 14*i) 14
    (readCompactBits compactWords214 (472 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits compactWords214 (2048 + 14*i) 14
    (readCompactBits compactWords214 (1976 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive214 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords214 (0 + 5*i) 5
  | 6 => readCompactBits compactWords214 (62 + 6*i) 6
  | 5 => readCompactBits compactWords214 (648 + 7*i) 7
  | 4 => readCompactBits compactWords214 (2090 + 8*i) 8
  | _ => 0

def compactPoolIDs214 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords214 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords214 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits compactWords214 (156 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords214 (80 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 5 => let v := readCompactBits compactWords214 (766 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits compactWords214 (718 + 4*(v &&& 15)) (4*n)
    compactIDsFromBits bits 4 n
  | 4 => let v := readCompactBits compactWords214 (2114 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords214 (2114 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket214 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits compactWords214 (183 + 4*(i % 4)) 4
    let off := ((i/4 + d) % 21)
    let v := readCompactBits compactWords214 (199 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits compactWords214 (836 + 5*(i % 18)) 5
    let off := ((i/18 + d) % 70)
    let v := readCompactBits compactWords214 (926 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits compactWords214 (2120 + 4*(i % 8)) 4
    let off := ((i/8 + d) % 34)
    let v := readCompactBits compactWords214 (2152 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def samplesP246 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x7ddbfffb,0x9fcf7aed1ff45e67,0x35ffdf9ffeeff875,0xfe37a5f9ffa89f54,0x15b5a85fbf3e0e0e,0x399fdfe9bf3d9e2,0xff3e5bf0bcfdfd07,0xfc6447fc0d09ae06,0x5fe14a2788030f97,0x3f13de79ad4f63f1,0xe150e11f4984c01c,0xf9f0392e752464c]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x10060001,0x902c1811150a538e,0x3100100800439051,0xc037802f00401f17,0x49f0c5f1580de1e,0x779a008019860130,0x6e60538036c01f97,0x817e0723c405fe06,0x5fe00ebf8f070fe6,0x1e520b830147e2d3,0x83e07b8e2e07fc1c,0xf9ffbc7161357ec])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x5facfff7,0xfc7e2ebbf301c9c8,0xe0fffc7bf3ff7e4f,0xc3ffbf1f865c3cc3,0xc1c359f3048c7600,0x7211e3ffffee7778,0xe1f8bf8ceffe387f,0x80be08e3c3c3fb0f,0x70e02060700037d,0xb9fe3bf7f1e785c6,0x886ccf819e407c00,0xe0c8f2b318f1068]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7b36ff3d,0xffbcb5d79caa1196,0x4cff3ffdfd7787fb,0xfc4be5e607f75faf,0x1449365c58d1894c,0x8001ffcd7ffda19d,0xfee167ffb35dc280,0xf5bb7007ef5ac09,0xa7f1492038124c1e,0xfef1fd9f53b77a09,0x6ea012feaa3c807c,0x500e5f0eb10e10]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x1b10330,0x1c20e88a31cdf6,0x4f000011c024682f,0xc04ba5d0078000ef,0x116133ff0a9f2e6e,0xfbf80148020800c0,0x91a02f80895de06f,0x8efe00dc4bfbae09,0xa7e14367bf1b7fe1,0x21b0141d00bf612d,0xec608791da3cfc7c,0x7fff803b21f1fe7c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x77f7ffff,0xf3fdd978ef7be7be,0x1bfef3ffcffff9bf,0xc1ffdaff79c3e23f,0x2a3e07af0383feb2,0x7deb1ffbff9e0ef7,0x1fe7ff835fc387ff,0x83fe001fc03e56f0,0xf8e0b4d9870d30ef,0x47fe078f0e18e03f,0x97e33f8076033c00,0x71a3f8e51071f1a4]))
  | _ => 0

def samplesQ246 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x2240820,0x70200500c0030188,0x480c0a01020207d4,0x431808054000a0,0xa000050000c04010,0xe040d80a81004800,0x4900024004111400,0x9a4000035084008,0x86cca08024802000,0x15018218ac044090,0x405000094002005b,0x2f0190c540040c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x10064000,0xd1080810140a110c,0x1048804028040550,0x9052104a20010802,0x402004805008418,0x4102912b00490400,0x9014000a08001402,0x20a880092410804a,0x8488c00500040841,0x1891058c8001120,0xc0a001011101152,0x242a0030a1c82012]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x20531108,0x81c0d00c08783617,0x17e1009241c0b022,0xda1044723021681c,0x120ca021720508ee,0xd8703b552603141,0x2a09490c2a420b3,0x324aaa690896a262,0x10104d285929011d,0x20ce396551610444,0x80a088a28c505980,0x2650ae2a308f1040]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4c9045a,0x44340282134ea61,0xa3920580c0911820,0x68cc3310aaca40c,0x4a9420a3a00e1023,0x163d26c42e94100d,0x260025b0408ce918,0x86405924c8461a11,0x293218181b60139e,0xea706c8702b32440,0x228002e60409c424,0x90d09e4f0a310a00]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x7e4edecd,0xdf6bbf37fdde3b0d,0xb0d9bf57ab7f5d79,0xb7f671fee8373ff2,0xfcdbcdcadfebddbb,0x470693ef2a5f6dde,0xfdb5fb6a8f7bf65e,0xe2f99dbfae778fde,0xcc99cfb566dfbac3,0x21f93cddcadef1bd,0xff7a9f5ddb7cf752,0x7dfad07ba1f9ff7e])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x8088040,0x400220300840800,0xa010300400280800,0x484010008040540,0x41480008200101,0x200004028120092,0x1480001424008,0x8000110480400810,0x800020000128002,0x30048002088009,0x1100150002088400,0x108010410030c120]))
  | _ => 0

def compactPerms246 : Array (List Nat) := ([[], [100, 33]] : List (List Nat)).toArray

def compactDomains246 : Array (Sig × Nat) := ([(subcube 32 0, 8)] : List (Sig × Nat)).toArray

def compactWords246 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount246 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath246 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive246 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords246 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs246 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords246 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords246 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket246 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP227 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6edfb7fe5b,0xa5737ff9ddde5d66,0xf713bc3039ff9973,0xccbe006b4e766ec4]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x540005842,0x15e380c8008957e6,0x6002bdb800168849,0x94e6c86b7eba22ce])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x776ff9dfea,0xdd897cfff7a9579d,0x9b9ea4177f5765c9,0x97f9366908bbd2b0]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7d3fde7fb7,0x16e2fffebacde6fb,0x6463d9a876bf9e5f,0x3746c80277a9ac4e]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x20301006bb,0x840b0030900c4419,0x9713bc3730011553,0x71b366b4e21cef4])) : Bits)
  | _ => 0

def samplesQ227 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x1124581020,0x4288a640812c2583,0x90420a01cb8111,0x8221818c84668c0]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x7abebee7fd,0xeebe4fdaf7f7b4fc,0xbd778effda5eaddf,0xfdef6be3babeb3de])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x89082a214,0x202648124082802c,0x31258880da142048,0x810862a112b89210]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x2c201a840,0x881519081200ca04,0x630d005136240c02,0x2440c60507298406]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x20381a0289,0x40a4480246624a8,0x10308424485a0084,0x508628a098963108]))
  | _ => 0

def compactPerms227 : Array (List Nat) := ([[], [113, 101], [16, 118], [16, 97, 117, 118], [80, 97], [80, 113, 117, 118], [96, 117], [96, 81, 101, 118], [112, 113, 101, 118], [112, 81]] : List (List Nat)).toArray

def compactDomains227 : Array (Sig × Nat) := ([(subcube 1 0, 4), (subcube 2 0, 4), (subcube 32 0, 4), (subcube 64 0, 4), (subcube 128 0, 4)] : List (Sig × Nat)).toArray

def compactWords227 : Nat → Nat
  | 0 => (limbs64 [0x1fe010c245b2e3,0x71fe03f3fe096f28,0x9005ca5fe0ff07f8,0x1a0ffe00677f83fc,0x120f2946ba692339,0x32237f80205fe006,0xbffd00900688d11f])
  | _ => 0

def compactCount227 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 2
  | 4 => 1
  | _ => 0

def compactPath227 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords227 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords227 (318 + 12*i) 12
    (readCompactBits compactWords227 (306 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive227 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords227 (0 + 5*i) 5
  | 5 => readCompactBits compactWords227 (50 + 6*i) 6
  | 4 => readCompactBits compactWords227 (330 + 7*i) 7
  | _ => 0

def compactPoolIDs227 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords227 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords227 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords227 (64 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords227 (62 + 2*(v &&& 1)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords227 (337 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords227 (337 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket227 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords227 (68 + 1*(i % 4)) 1
    let off := ((i/4 + d) % 18)
    let v := readCompactBits compactWords227 (72 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords227 (339 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords227 (341 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP242 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x408000281220,0xe1c0110401162a1e,0xa00158e040870204,0xa9d16ce00f8d8534])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xeeafbfbe18d6,0xe9abffc6fbe3ce3d,0xf63084e36cfffe35,0x1cf0e1e628e38d0e]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xf8cfd9efb2b9,0x9403f5ff7d543bc7,0x583e21143fd7ddc2,0xa95fb21840cf74c0]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xdd2fe67fcf61,0x6043fffd8fbe21fa,0xa3c358003fbf627c,0xe78f4c0007fce830]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x820000688d1,0x42804c0082001e1,0x5232a5170c107c70,0x40e931e606268ca])) : Bits)
  | _ => 0

def samplesQ242 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0xbf7efef7ffdf,0x3effbf5fbdffdbff,0x7fd7bf7ff5f7eed7,0xeff7f7efcfcfbf7c])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x115268406303,0x1653040a918692a2,0x4483292920b4e411,0x2892c1424ac28d08]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x730a2d22d06,0x22eeb05830aa506e,0x34561963b5d38c90,0xa0564728c9cf3440]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x22d44998311a,0xd9d620c1caca684,0xe0bc0f256f2d4454,0x26134c5a32f4e810]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x828020280c0,0x20890100404048,0x1040801010420202,0x4120222081091224]))
  | _ => 0

def compactPerms242 : Array (List Nat) := ([[], [101, 113]] : List (List Nat)).toArray

def compactDomains242 : Array (Sig × Nat) := ([(subcube 32 0, 5)] : List (Sig × Nat)).toArray

def compactWords242 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount242 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath242 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive242 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords242 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs242 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords242 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords242 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket242 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP241 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6fdfff6eef1f7b,0x37efdefbc7dcaf36,0xb9fdcc577cf7dde3,0xe2e6a0bec6bcbdd4]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x33029400937b1,0x78084801b4546d12,0x41f7fcd004244998,0x7252b1befe5a28de])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x772fefdf39b588,0x27fbfb97f7f34339,0x41f44447bffc01bd,0xf75700b845fb26c0]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7abfbff3c166f7,0x5ffe7d7fb814fcd6,0x577bb896ef6ffb9a,0x5a98b106bbd6c81e]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x2080060221044b,0x3002101203908234,0x117dcc52284091a3,0xc28420bec6b484d4])) : Bits)
  | _ => 0

def samplesQ241 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x10210883104080,0x8a240a004345021,0x130000a16086c040,0x4006616404243950]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x33828e4033311,0x6c648414dd2d1810,0x61ae9156ba8300ae,0x89a844a591a4d620]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x8d47220460175,0xd35184038888075e,0x4c9db30695780199,0xa58812894bdb0680]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x540d0442a8910,0xa5009d0891010b0e,0x2424950c0a691a88,0x83981400d392c006]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x5f7dfdfcbffbf5,0xed77ddbfff6fbb9e,0xe5efb7febaebdbff,0xefbe5cb7f3b6d6f6])) : Bits)
  | _ => 0

def compactPerms241 : Array (List Nat) := ([[], [84, 112]] : List (List Nat)).toArray

def compactDomains241 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords241 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def compactCount241 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath241 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive241 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords241 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs241 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords241 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords241 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket241 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP243 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xdfabfffecefa97f4,0xfbde75a2934fffef,0xdfdfe2cfee57b59d,0x76f37ebd89735835,0xe415e7fa2c404a3f,0x7fcfe7f3df3fc13f,0xe4bec37fab053ebb,0x62b25a6efae04d8c,0x12f6ce80c020b3e6,0x3befc5fb7303c31f,0xc1fa348c6e801043,0x52d1c8fcacdb6a20]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x910016000049e04,0x228091ec03c00001,0x850428a80000415,0xb21b170b8b71a120,0x2c157f6988f24e83,0x24004028db4341a1,0x412086908b516df,0x37f25d7cc7ea044c,0xb4eeacde30e060,0x50c14aef2311829d,0x2af8cd8ef3b3b143,0x53dfe95e7c50ee74])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xfd78fded7ffdde8e,0x8f6d43cc072ff7db,0xfffc7ba7d5c9cb7e,0x9eee9f4fea70a449,0x96e1961d98b1213f,0xfebe7bee7ec6f1ff,0xf7b5ec7941a9f49,0x5e42b55d16ff3650,0x610611021c167a7a,0x77d73bddeef15aa7,0x6e46b85d10783a4,0x9003cc57416c40e]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xefd4ff7fbf37b95f,0x2af098eb60affbfd,0x797ffe7d79a1f5f5,0xab1b77fa7f0d916e,0x2b1378884608427b,0xbffffd28bb7bbfee,0xf3d1abe948a536d5,0xb50f42f3251583ac,0x7cb1c09061683ffd,0xecc96afe98ec2159,0x2a788d7b7c485c43,0x3041395b4bb0a980]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xfa76fffff3c6ee6b,0xf7818d143ccffd3f,0xafffddba8a7e0e9f,0xf35fc3f7f48b67b0,0x189e0f61a8420cb7,0xf7f7defff1fb7e91,0x5cbf3c7a0ef14016,0x3fd9dacc94a685b,0x81fd2e2c8200bddb,0xd3b3fe673f13bc98,0x7995c4f282b02000,0x429eff16334d0270]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x4060000c0202804a,0x8b454d8234200108,0x10c00254841819c,0x24242f46c0b547d,0x929386982e496b50,0x12860002303ab01e,0x40b902428e013e11,0x420f92ef38556b98,0x71f7df92e16e93da,0x238320501ee3791b,0x41f424f14ccc5ee7,0x7ad1dcd5239f2baa])) : Bits)
  | _ => 0

def samplesQ243 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x2054085113004803,0x21884528a25120,0x121000f01a284502,0x8a50c24a0208200a,0x880804008c05c8,0x54c8077011040020,0x440003025a044153,0x61403ac10c402668,0x1308014002500222,0x39ac058353000104,0x4010300061806344,0xd03100e48cca4a00]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0xf6efbf9fefdbebff,0xfd7f7f13fdfcfdfd,0xfff5ef4dfffe9fbd,0xfdecf6f7ffbfffdf,0xf7feaafeff5ffd7b,0xff3aeebfffdfd7f7,0x7ddbeffbf7fef6da,0xd7ffe7777ff7f8df,0xb6f777dfeffffeee,0xd6dd6effef75ebfd,0x7bffffbff7dfb7fb,0x63ef795ffd76fefc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x2878211c40a2130,0x30021c13c8d83441,0x8120a549168c0480,0xb180646400954980,0xa02620a06746c472,0x9a2842a06208c252,0x8584c099036244a,0x846482211984380d,0x225621424a2ba42,0x42d52891ac204829,0xaa0419581051260,0x6184384534168408]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x102b228440580210,0xd40c67109554a0c0,0x88058b08c40292ac,0x51242014a0364681,0xc060226085533831,0xa912e8080a185606,0x214804680550a208,0x8013c13471231084,0xa455460c2c073ccc,0xc440627c80640818,0x286809b0841c9409,0x2142791b4130a080]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x58904a084390094,0x105272aa4319804c,0xa080c6038085b068,0x60870d200914c084,0x872020321630f226,0x22279883028b4282,0xcb240884630c24,0xc26401cc08e0981,0x6c604207640a7999,0x821398642821a888,0x925059280310c20,0xcc4fe1233050030]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x4060100403408048,0x905010034244810,0x4440000048220304,0x8608212a4001050,0x1010800808090909,0x4510240484400101,0x100080904300c210,0x4111214024610040,0x9010108081000424,0x1408460a40100240,0x100282081288a109,0x230108c8605044]))
  | _ => 0

def compactPerms243 : Array (List Nat) := ([[], [101, 113]] : List (List Nat)).toArray

def compactDomains243 : Array (Sig × Nat) := ([(subcube 16 0, 7), (subcube 32 0, 7), (subcube 64 0, 7), (subcube 1 0, 6), (subcube 0 1, 6), (subcube 2 0, 5), (subcube 128 0, 5)] : List (Sig × Nat)).toArray

def compactWords243 : Nat → Nat
  | 0 => (limbs64 [0x28,0xc4ef389306097fc3,0xfc3fc3fc3fc1ecff,0xc2287fc145401e7a,0x498a62c6a80175bf,0xfbbbb7bb9305cc27,0x3084c3130a095094,0x96f6ff8ff03d05c,0xcf3ff05529540529,0x1087436214305986,0x79876210435fffff,0xc12a12812d0a323f])
  | _ => 0

def compactCount243 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 3
  | 6 => 5
  | 5 => 1
  | _ => 0

def compactPath243 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords243 (27 + 12*i) 12
  | 6 => let v := readCompactBits compactWords243 (346 + 14*i) 14
    (readCompactBits compactWords243 (310 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords243 (678 + 12*i) 12
    (readCompactBits compactWords243 (654 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive243 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords243 (0 + 6*i) 6
  | 7 => readCompactBits compactWords243 (63 + 7*i) 7
  | 6 => readCompactBits compactWords243 (416 + 8*i) 8
  | 5 => readCompactBits compactWords243 (690 + 9*i) 9
  | _ => 0

def compactPoolIDs243 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords243 (21 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords243 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 7 => let v := readCompactBits compactWords243 (204 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords243 (84 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords243 (471 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords243 (456 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords243 (699 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords243 (699 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket243 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords243 (231 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 7)
    let v := readCompactBits compactWords243 (233 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 6 => let d := readCompactBits compactWords243 (496 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 13)
    let v := readCompactBits compactWords243 (498 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits compactWords243 (701 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords243 (702 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP230 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0xdebe7fb,0x8e7dc07fdfb9f797,0x962f81821eff9cee,0x327b24706cadd4c4]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x900401,0x8b64284006211c46,0x122f0b861ec00ca8,0x63343c706fd194f4])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xbd7ff9d,0xc9eab23f6e7fe9ee,0x7a57804a9bfe6f9e,0xc1f4e5f00073b1c8]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x10c0098,0x44e8c3c04800e181,0x8e5785cafc063c5e,0x8048e5f1fc207fcc])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xf9ffcff,0x77e469fcffe7dc41,0x8fff7f8467c7fc79,0xef0c1801ffd07e34]))
  | _ => 0

def samplesQ230 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x2161c10,0x61020b3084109140,0x7446686040b38824,0x1028116c1cad4084]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x905400,0x844282209041000,0x5044410410230240,0x884201481828420a]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x429012a,0x121044cc2208649a,0x80991210274c6402,0x40904c92a152b140]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xef3d7e5,0xfb5f7c26ff7cfa2f,0xdbeccb7f76277e7f,0xf9fae749fb687fee])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x608120,0x800914045060200a,0x8088000b02045019,0x21004400a1403c20]))
  | _ => 0

def compactPerms230 : Array (List Nat) := ([[], [81, 114]] : List (List Nat)).toArray

def compactDomains230 : Array (Sig × Nat) := ([(subcube 2 0, 5)] : List (Sig × Nat)).toArray

def compactWords230 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount230 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath230 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive230 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords230 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs230 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords230 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords230 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket230 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP167 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xdcbefeaed742,0xa07fd9fff0f3c773,0x546a2400ffed0946,0xfeaf840322f7ca20]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x8c0b003ce12,0x2d4101051026c51b,0x18ee76b410888a45,0x6aa665736b26d372])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0xf97fb77d6e15,0x6d3f7f9dde2e3d9a,0x99f452b4f5bfce7d,0x4b74617049eab152]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xeffffff3d9bf,0x2efff767ff1ccd7f,0x7e9a37cd9affbbdd,0xa197ff9322ac5e3e]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x410006205105,0x2ec05000c2180d72,0x541a37cd0025095c,0x8115ff9322a80a3e])) : Bits)
  | _ => 0

def samplesQ167 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x234520f0a899,0x1f97c211213c4a91,0xb5854cc5c7e90924,0x8c3a0610aff3c820]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0xf71fc7be7be5,0xd6a675bf77d4bf6d,0x95f7a3da1dd9dfc9,0x7f86fc7f0f27d7f6])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x68318828138,0x90cb960810170a03,0x4b00ec0da10f0465,0x8338059051e8a042]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x101002040240,0x4020012046401120,0x20001218109008,0x2004a82500041614]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x410802345004,0x624208603401120,0x94a203001cd04280,0x508028250e075580]))
  | _ => 0

def compactPerms167 : Array (List Nat) := ([[], [33]] : List (List Nat)).toArray

def compactDomains167 : Array (Sig × Nat) := ([(subcube 2 0, 4)] : List (Sig × Nat)).toArray

def compactWords167 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount167 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath167 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive167 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords167 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs167 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords167 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords167 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket167 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP231 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7766ff7b,0xfebbb36ec3d34625,0x83ffff3ef2ffa734,0xc7fcff7d23dbc337,0x606ef418221dc400,0x3d8ffffeffcd9ff,0x6e3ba79bfe1e322,0x7c433271e8bde20f,0x8f1c2d02cc200077,0xf4fe3dfb8c4945a3,0x8f679d12e7210400,0x6254ef3acc1b8a20]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x7d5cfffd,0x8ffde4c3ece4d892,0x8bfeb9dfff7c7a3a,0x3abe8ddefdbedc0a,0xa5923c73d8a37101,0x241ffef777abb73e,0x7f3be7d1dc5f7595,0xea10cda93552e850,0xfac2008c100a0dfd,0xe7dbeae76eb8b659,0x9584c8e99e124381,0x91880ea471d72184]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x20130000,0x888812436ad8ee62,0x8c00891000192838,0xabc073101180f0e,0x64da3e79b2d5c983,0x27e000964028c159,0x1803c211c4c3fd24,0x7d47f2a1f058e854,0xff402ddedcba0d89,0x874a309084799681,0xb507ec74a73f6781,0xf3dfe0f3459fabf4])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7bbbff9e,0xffd2df733ff8b74b,0x6bf9ffffdfbbbdfd,0x3d3f8abf3e5d2fcd,0x261d3b6ceb428e55,0x219fe9beff4b56f9,0xb9c7dbaffd9e89a9,0x956cf1d73a6ceba0,0xf5222100e84e8ebb,0x9f67db549d36cf9a,0x640326f566d35b82,0x6210895707b48d88]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x1600218,0x10e42081c3d611,0x6000000a12201624,0x52c889e2c064385,0xa105fd64e80b5555,0x7d88c82000481224,0x2162a048bd1f238b,0xd8401d792b6eeb20,0xf0b623adf84edf94,0x54d60b4409b06f5b,0x4421999be6d35b8f,0xfbb89b26cc74fd8c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x6ff3feff,0xf9cc7ebdfbcbee70,0x77ffcffb3ffd5eef,0xcfed77b3cd267b84,0xd9c1cfe5b4dd5982,0x5c3fdfffd87ceb45,0xf97ee45ee7fb3e4e,0x59c71e28c34a1d74,0x70f5c2fd1090515c,0x5fde379cf1f13a45,0x7039f91ea10c200d,0x99ab12e3cc6c7054]))
  | _ => 0

def samplesQ231 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x8998184,0x40c04291182899ca,0x5d18483403055917,0x85300323125804c,0x825108858cc0a14f,0xe030b871e8681d42,0x18124212422c3cc,0x26c423a80c0b0a84,0x80e8128118a622f4,0x20fe0da88e404462,0x84461803a0216402,0x162c9f28cc1a0a00]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x2a31010,0x78420a281a1a2721,0x75c020b82112aacc,0x46a642b082100a4,0x12588204a59084d8,0x51f6d61426c82d14,0x11020531101092a3,0x4b40028e9921c90a,0x6841b8413a2042f5,0x4249a86766281053,0x4c4004b84085360,0x1b844ea431530104]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x20134004,0x288812023890ac60,0xc8c04308923308a,0x431441011000204,0x4650205496818982,0x215464210c5a0d20,0x251014650100110a,0x608021241428818c,0x488110099c300af0,0x6031014e4a042142,0x4c54018390011642,0xd001f0c2840100a]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4440829,0x224200440054014,0x8220104200880000,0x5184190444c85012,0x880440200041020,0xe09018a11000088,0x88408080088c2400,0x8019541060042431,0x130444100100110a,0x9d00521011100088,0x2001022042460894,0xa011205302a48480]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x7e9fdfe6,0xefff7bff7ebcbdee,0xdf9dfcffbbff7dbf,0xfef3cef2f37feeff,0xfefbeedffff5bfef,0xe37cfdf1fcfa7ffe,0xfdf7f5fdbffffbde,0x76efeffd3efb9fdc,0xcdff3fdbbfff7bfc,0x74ff1feedffc7fff,0xfcf7bbfbf7f3f64f,0xff6f9f6eec7effce])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x100c05a0,0x21101400404108e,0x8211800110404111,0x58800800604cc401,0x2022000840200225,0x820809c0d0004200,0x4024400882466044,0x40d441020020610,0x812c010200490008,0x1486168090800a04,0x1020a01001622004,0xa0298042c42c6040]))
  | _ => 0

def compactPerms231 : Array (List Nat) := ([[], [16, 118]] : List (List Nat)).toArray

def compactDomains231 : Array (Sig × Nat) := ([(subcube 4 0, 7), (subcube 1 0, 6), (subcube 2 0, 6), (subcube 32 0, 6), (subcube 64 0, 5), (subcube 128 0, 5), (subcube 3 0, 5), (subcube 33 0, 5), (subcube 34 0, 5), (subcube 66 0, 4), (subcube 68 0, 4), (subcube 129 0, 4)] : List (Sig × Nat)).toArray

def compactWords231 : Nat → Nat
  | 0 => (limbs64 [0xff,0x3fcff03b9142002c,0x3b19409400215195,0x193fc37c7a0e15ff,0xc3fc11200affc175,0x6f68837fc3de6573,0xfc2ddbfc3fc3fc3f,0xc3fc1cc100009eda,0xedb6ee3cee7d6708,0x9c427089c0842f9c,0x5e70262a32261c42,0xa32a32042a324346,0xa2df98847972bbfe,0x3eea3cbff80a048,0x8d9fe0735f19101c,0xa545a19ed60c8633,0xcf2284cd9e801fe0,0x1238ed27f81fe07f,0x81fe008b4deaaa19,0xfe07f8112b3c1043,0x97d226990956033,0x2d6466a6e1fe02fa,0x4ad6be4fc8814a3f,0xe013b3383b11d522,0x8986fef99c14c800,0x184c0008800e190,0x3045db162c58b35a,0x7c082f5cb5669519,0x5223060d12102800,0xa414a14490390,0x30ce6440c0081064,0x90212fefefefefef,0xedeeefbbefef7bfb,0xfdefefffafbbefed,0xfbefffafefe13121,0x30e1305330d33001,0x30c130c13081301e,0x215d315d304e214c,0x214d194f314d314f,0x300f301921593159,0x30c9215531450147,0x3145316216192092,0x112151910910102,0x158e3fe017351889,0x4ee48ae0412f7a1c,0x29da565b7fc0fafa,0x60930cccbfe0ff07,0xf80b09fe002541e0,0x3b98630a650399a1,0xee220021810e5981,0xa2e118648da280c,0x163a72a010c63a80,0xe4327ca9820c6328,0x63b0a29813e237ff,0xfffffffffffff885,0x4850858644648244,0x24804404a21d843f])
  | _ => 0

def compactCount231 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 9
  | 6 => 27
  | 5 => 7
  | 4 => 2
  | _ => 0

def compactPath231 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords231 (32 + 12*i) 12
  | 6 => let v := readCompactBits compactWords231 (998 + 16*i) 16
    (readCompactBits compactWords231 (890 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords231 (2991 + 14*i) 14
    (readCompactBits compactWords231 (2895 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 4 => let v := readCompactBits compactWords231 (3482 + 12*i) 12
    (readCompactBits compactWords231 (3446 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive231 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords231 (0 + 6*i) 6
  | 7 => readCompactBits compactWords231 (140 + 7*i) 7
  | 6 => readCompactBits compactWords231 (1430 + 8*i) 8
  | 5 => readCompactBits compactWords231 (3089 + 9*i) 9
  | 4 => readCompactBits compactWords231 (3506 + 10*i) 10
  | _ => 0

def compactPoolIDs231 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords231 (26 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords231 (6 + 4*(v &&& 7)) (4*n)
    compactIDsFromBits bits 4 n
  | 7 => let v := readCompactBits compactWords231 (487 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords231 (203 + 4*(v &&& 127)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords231 (1784 + 7*i) 7
    let n := v >>> 5
    let bits := readCompactBits compactWords231 (1646 + 6*(v &&& 31)) (6*n)
    compactIDsFromBits bits 6 n
  | 5 => let v := readCompactBits compactWords231 (3152 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords231 (3152 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 4 => let v := readCompactBits compactWords231 (3526 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords231 (3526 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket231 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords231 (586 + 3*(i % 6)) 3
    let off := ((i/6 + d) % 22)
    let v := readCompactBits compactWords231 (604 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 6 => let d := readCompactBits compactWords231 (1973 + 6*(i % 16)) 6
    let off := ((i/16 + d) % 59)
    let v := readCompactBits compactWords231 (2069 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 5 => let d := readCompactBits compactWords231 (3166 + 1*(i % 4)) 1
    let off := ((i/4 + d) % 23)
    let v := readCompactBits compactWords231 (3170 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 4 => let d := readCompactBits compactWords231 (3530 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits compactWords231 (3532 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | _ => []

def samplesP215 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x5f653ffe,0xaebee23c7ed77084,0xc2310ffbcbeffbfb,0x2de9deb1fb73f305,0xe9ee38d136ac2382,0x4f9228000045ff9f,0xcfffeeebcd7f97c9,0x70fbc9ef94027b14,0x740cab8fd5a017b1,0x8a8800852005fdfb,0xe7bf73fe19a7841f,0x6ab22b3a36280400,0x2064bf1f9525c280]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x6fab7f3f,0xffdafecfb399ba3b,0x13c04ffeffb79dff,0xdf3e0fc60f83fe7b,0xfdf9c701c3303cf3,0xa3fc71804c11efef,0xffb3f07c0fbf7cfe,0x7f3e770ff87dbf87,0x81f0f0f00740e87e,0x291cf180401eeee,0x27dcfce7ee4cf8e1,0x71c07c3cc780008f,0xc7881ed8e8c7902c]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x262c020,0x201abcac1045322c,0xfaf2f00081230900,0x28880f868983c421,0xc807689d3a3c3fd3,0xcbf179b6cd7e2200,0x22b0290d9800c1,0x4d2d10ff872bf15,0xfc4fa98f0f88f93a,0x2b9ef9f6d8e0008,0x62dce01215b7ad59,0x71a03cbc263f8ccf,0xe7ef80da9327d7fc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x7bd6bfe9,0x7ffd9dfe2b6f4760,0xb93a8ff5ffff7f67,0xeeb52d6fccffcde5,0xd397a4aca85f1ac9,0x5361dd160111ff7e,0x777f9d73bef8abf1,0xcef5f69f63723467,0xebcbcc4f2a98d048,0x72918c12018b7b9d,0xfe7aae9f9d9ae7d9,0x52c50f5ac5380ce,0x86002db21b9b4438]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x8050000,0xc80401c238871d2,0x1131c0004a001040,0xcf24004004638105,0x61f1a741c08e02a2,0x17f0d5976f900008,0x46110040867ca288,0x722d6409c7727d47,0x83f0f45e00c00465,0xc297df5a15ca67c6,0x532208e0848d6f9,0x41024b7ffe1380ff,0xd7986e398dc17c3c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x7e7ffff7,0xfdff7dbdd5ecf1de,0x7cf7ffffff7bffdc,0xfbcef3deb5ef85bf,0x6e776b5f588ec736,0x9cf1d6b7efabb2f9,0xfeffb38df7dce28f,0xb7cffd78cff2cd59,0x9e77351e08cf2d27,0xc526734a5dcaf746,0x59f7e11a70711f78,0xd1038fcf7a378871,0x519b626987607d54]))
  | _ => 0

def samplesQ215 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x209ac811,0x3347198381040f39,0x358efe440c0b0338,0x3a7a2170869049a0,0xbe190f0c3021de0f,0x906c05d9d333d398,0xdf1a102495b0a80,0x79c404e6548286be,0xa4cf6a122e8156e,0x4847c05c61b1fd3a,0x47b1739a0ba800be,0x2410233916180cc0,0xe81c7f1f85254200]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x1054a0e0,0x108401a00c2441c0,0xe83c907005048740,0x27840031798c0505,0x540130223082020d,0xc801043e0286a187,0xb600c01649242280,0x91214082c007dc1,0x800c595008a0029a,0x3548205aa041a4c4,0x28cb061ea0428a1,0x41502000d6040300,0xd78496d860c4800c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x262c4a2,0x204aad888044202c,0xda62f52c2601430a,0x8124403ad09140d,0x8a23099438286a5f,0x82a445a4894d8855,0x63890b0269099aa4,0x196c242228266a69,0x2011a42440025354,0xa4c28a5d2899fbe5,0x15020b45428850aa,0xc1921131f012614,0x1d007f244cd00802]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x4294113,0x840a4800d010b816,0x6c1638580911008,0x4048758202219a0a,0x20b2494501204922,0x2622416c694c68,0x406e014102090940,0x9445422341350012,0x2c91028673034c20,0xc0a2802414945a19,0xb8720c941488824a,0x42041912051b096,0x202129221b1b0420]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x77fafdbf,0x7b7fffebfd77ef3d,0xffeeff6defffd7fe,0xba7bef7fafdb7dfd,0xbf7fffff3ffbffff,0xfaef6ffddb7fdbdd,0x6ff9fb57ef7ffbed,0xffff7ffefeeeeeff,0x7b7ff6ade6fef77f,0xeeffeafffffdffff,0x57b37bdf4ffcfeff,0xfd7b6bffff7b6efd,0xfd5e7f3fcdf57f3e])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x1801000,0x300024020030601,0x100080040600084,0x10200040001040a0,0x8800006500080,0x2000080010101200,0x810100084004009,0x200091010808004,0x240000100480000,0x810008002000002,0x4001400a00500400,0x9002084400280840,0x18000180207110]))
  | _ => 0

def compactPerms215 : Array (List Nat) := ([[], [65]] : List (List Nat)).toArray

def compactDomains215 : Array (Sig × Nat) := ([(subcube 1 0, 8)] : List (Sig × Nat)).toArray

def compactWords215 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount215 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath215 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive215 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords215 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs215 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords215 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords215 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket215 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP183 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7d933ff5,0x5bfd88fbdd5e7098,0x64103fdff7f9fdb9,0x376fae3bae660ed3,0xff690ea6a1c78096,0x33c0a800051fe7df,0xff7dfd6fe48fff86,0xddbea0e4d067fa54,0x842dd2b070751a93,0x4e0844802007f7f4,0xb7fd7e6be0165233,0xc9bdc858fd810401,0xc10bfb9670b6200]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x20418000,0x1304822ec38049d,0xc175001024090011,0x5782338300e0087,0x1905dee44f81e592,0x2c82b95e17440480,0x4606244245878040,0xc9c0b0a06a6e73f0,0xf405741ff8743e07,0xc2ca56fb3e5104d1,0x42c94c383806e331,0xb3ae2cdc6e797679,0x8d96e2d35752f78c])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x77763ffe,0xff35d7e7b6b80c62,0xc1cc3ff9ef3f7ff7,0xedf8372d377fb1af,0x46fc313d4f806509,0xe426914a105effbf,0xeede7afadbd4c3e7,0xebccff926e4a00a2,0x1dd37c5d88222e2f,0xf0c2121b0647fdbb,0xc5cfe9dafc2fa74c,0xb14e0fad08700238,0x81827fc64cf01484]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x6f4fbfcf,0xfdfa7c8f6f3de617,0x9b73fffffcfb37e,0xc79f6df679bfcfe5,0x3b16ef405834f6d4,0xdb85c14429f5eee,0xfffb65df77ef327d,0x6e71dce32b94f577,0x7a0e252e7f4ca120,0x8d3088601897cfcb,0x6e5b1f7f733865b3,0x26c3b596e208f0c6,0x10242e7299c3c11a]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7eedfffb,0xe7ff7f32fde783dd,0xb36e7ff6bfffdfdd,0x7d77f3fbffc9f07e,0xd985d2e37e791d7a,0xea83a8c90d7ffff3,0x77b79e323d77bc58,0xb9ffbfb816697398,0xe43573df87f1fdc4,0x320b46976149e2dd,0x7aa7efb4bbc69b0d,0xbaa022c36ff70f01,0x8d509297925ea2e4]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x40600c0,0x4001148315042252,0x218e400083001100,0x650724232f618060,0x420423237874145c,0xe3a08cc94de24202,0x2011583a30443204,0x283c8c921641f016,0xc3f73fc0761a9a0,0x3f3bce9761c8c388,0x24072b42f33e170f,0xa8c18383e9f78f87,0x9d709eb688cb22f6])) : Bits)
  | _ => 0

def samplesQ183 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x26cc409,0xe42467000a618764,0x99efe96104c19c41,0x5a906615691840fc,0x4592c3982e3805e0,0xd418365b9afd641b,0xd07d985500db0381,0x9b25089562c0516,0x963ead120056cabc,0x80f45983584ff640,0xb5f55449e0261570,0x880dc409f40908c1,0x9213ffb867094200]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x5fbe5fff,0x7fc797fd57effbe2,0xfeaefe5bfdda7fdf,0xff7fddd52f7fff56,0xdef9e57ffeffba0d,0xf7ff6fabeef79cdf,0x77da7ff77d27d7ef,0xfff7b53fbbfd73ce,0x7ffdf7efffda1abf,0xfdffe43ffbb58edd,0xcffbce7fbd7ffbb5,0x33fffed66efff4ff,0xed47ead3ff57ffbc])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x889c211,0x45a610848469399,0x2a31e4a0404985c4,0x4a22007a92901455,0x282342c822509de0,0x51487e842f1a1727,0xc0f883158d90087,0x290f080128ea821,0x2098c400a2712569,0x1450fd81095feda3,0x50b6182802b0750,0xb8048e0db0212312,0x80a87fc40ce00404]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x10b0411c,0x244813010c098a0,0xf608dc0088402459,0x303a584103201502,0x8c30400da2110001,0x720b21a2a47210cc,0x7490489321210081,0x6490102300e121ca,0x24a06160aa081211,0x94534009a8058a89,0x25a0e5620322191,0x24484922028a493,0x1442a5289438110]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x1121044,0xa0000c400086802,0x4400121201120000,0xa109180000628302,0x8008040000862200,0x240120400088c0,0x2380040000049448,0x40512885110c8,0x4010e419081000,0x4000002002a0001c,0x4a008a3419400004,0xa0200008929408,0x254400039016a0a0]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x4060840,0x6801100105002042,0x86024830004200,0x81010404284ac200,0x408820225000000c,0x80000940858810,0x340230004004020,0x9041001888101004,0x1244108611020884,0x4108001400000054,0xc8a080290400c800,0x112104002121048,0x2403800172145808]))
  | _ => 0

def compactPerms183 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains183 : Array (Sig × Nat) := ([(subcube 4 0, 7)] : List (Sig × Nat)).toArray

def compactWords183 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount183 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath183 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive183 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords183 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs183 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords183 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords183 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket183 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP245 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6f5dbf7f,0xdbde5e6ec7edceb4,0x918cfffeef3fefef,0xf7cb7cb3fabc1fee,0x6b92f5e014aa0be,0xbc9a820661f7fe3f,0x7f9d73fbb33fd4bc,0xab9efa01bf540c4b,0xe3ad81be5c0d5fac,0xd6436c00405f7d87,0x9f7cfe728e3697f0,0x549ec4663c8500a0,0xb551979dad8964a0]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x1884018,0x2005bb0c0602631,0x3b600000204262a,0x48010127e118780,0x26bf2aeac602a0bb,0x9d3283576c304402,0xa063d4a34c1034,0x844c390bfd5ccdb,0x7e3489f8390c4ba0,0x1e4f6f4458e40c11,0x194372e20f30a791,0x8c1f2e47768ff1a8,0xb5dfa259db89e6f8])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x7db43fbb,0x2ffdc9f1e4bed060,0x750ff79d7fffe79,0xc9b89bcb75bfe793,0xe6f628a9ca85bc00,0xc462810101fffdf7,0xbdfabfc7d3fe1b7f,0x2e6d267a3e99cc35,0x1e5679b9b3024023,0x30018bfbebf,0x7babebbeed28e994,0x2f183a5af308f008,0x803f329aa7c208]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x77ea7fdf,0xf7e77f9bf8c72707,0x62e0ffbffbed3fff,0xfe341cfc7f41bffc,0xf93fd0f00cf340df,0x71cc40603fbdfff,0xc7e0c3fdeddfe7c7,0xd3efc383dfe1f381,0xe3f87e401c0fa3d0,0x10627013601ddf78,0x9dcff3cdf0c71e17,0x881f0f8d3e7100c0,0xf8112edb5171a504]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x4448000,0x1850442c087ce46,0xc34900180128004d,0xf9301c8801a42f00,0x1f38b408fbec0c,0x6658d5a782428025,0x401143119e8240,0xa3ab026bffb1c005,0xa3da7fa89c07301e,0x51f2731b7aa83528,0xe2cc310f007d996,0x89ada3ebe79f0cf,0xf8b154b335b1ff0c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x5fcffffc,0xffbdb7f6db73ee5b,0xcb3fffdf3ffef7fe,0x3df7f71e8ff7ef01,0x3fcf3aa6f63aef29,0x7b7111f18dfee7ef,0xfae77d563fccba70,0xfdf3dffce1b7c0de,0x3c128fe8a9f4381e,0x699c034c1aaea579,0x6e7757f31311e18b,0x88e3fa37c68af10f,0xae70617798da58]))
  | _ => 0

def samplesQ245 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x10a24484,0x2260918038021103,0x2a72342610220606,0xa4490d605087091,0x2026c200c0b01311,0x401024c90ac72420,0x66820292000d4130,0x3813806e0ce0094,0xc24308111909d812,0x818208431d1a2481,0x961c4c708e0609e0,0x2004c010340d0128,0xc6215594a5884480]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x1884288,0x42001a9088202411,0x2921202b0888202,0x100110462000a221,0xa2a428a42108112,0x110804544823104,0x1656088010044512,0x408b0802680a9400,0x488202821840c804,0x824c05099a3024,0xc02c0c08048218a6,0x6240403090214422,0x420055a404240806]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x24be04c,0x788234860940679e,0xc8af0f4a160112c4,0x9d51c03026709b3a,0xb425b445412057c,0xa9972b65fa999a6,0x3982a0c906a6495c,0x24c14ab18cb4d638,0x88e122e3c06c1166,0x1aa69929495f98b6,0x7ba2c12ea40a4ab0,0xac0862da51286682,0x8cc43f328aa78200]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x8159061,0x80c00220710c8e8,0x9505c81804040998,0x45802d2990560806,0x40c03d0130080c08,0x98281b10b118c25b,0x812001684e128248,0x404c01902300123,0x243c9048a41624e1,0x760c13a00205cb58,0x8c1b38170080601,0x801a0bc0481210d1,0x1892aa4b5051a100]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x7bbb7edf,0xef7affbdbefab5bb,0xbef6bef7b3bfbf57,0x7f6fb3f67dddfef7,0xfeeee6dfefbe9bf7,0xd7b7bedd7edfb767,0x77f6fbb759bdff36,0xe3ffbf5ffbffbdf6,0xdfeb5fdf9bdddafe,0xcdebcedfdfda3dbd,0xdefdcf79df87ddff,0x6ed7f93ebffdddaf,0xffab55f7b5bdffce])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x20300801,0x68400900881020,0x3440a08101102000,0x42042180110c4084,0x6080001009040080,0x4060c0820540641,0x4000500401003000,0x8030040c02400186,0x608181801110090,0xc041001080000509,0x451025101018008,0x81100402941109,0x1023004131185048]))
  | _ => 0

def compactPerms245 : Array (List Nat) := ([[], [80, 98]] : List (List Nat)).toArray

def compactDomains245 : Array (Sig × Nat) := ([(subcube 1 0, 6)] : List (Sig × Nat)).toArray

def compactWords245 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount245 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath245 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive245 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords245 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs245 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords245 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords245 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket245 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP119 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6f5bbf,0xfbffdafaf26f34f8,0xa96f304ffbff3fef,0x97fdb9d4ebf3f7f3,0xb762dedc31d780cd,0x36080a2bd47e016b,0x5f1fffbfcffd473f,0x7fa2ddbebad8bfa3,0xca636e460b32d3c6,0x8c5dd626c5d06dc1,0x19622016fffd1ff1,0xa7cde1b0c2532bce,0xdd9b7201e3104802,0x28bf5fde4409bd20]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x7b76ff,0xfee3ffbdd5a3fd9f,0x6783a9bffdf3dffd,0xfbf3d1eb75f83f3d,0xfebf13f9c02d1e63,0xfe6f74d0fb953090,0x3fffdaf7f7abebe1,0xf9bfaa7f0fb1de5d,0xf71f9b2134df007c,0xd1a69ec13e81f036,0xa08043cddde4f56f,0x3a77f5e53e1cf038,0x9606e1f71b29071d,0x43407c313ae8f0d4]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x2005c0,0x6202182221d958,0xe7e720d001811000,0x8180c1e061d005e2,0x11220388f0378ae9,0xf66e3e1bd41731fb,0x61001093000840b8,0x722c083c08d0d881,0xde236e463976136c,0x81b69ee537d07df7,0xb9e263d811c87531,0x888400c4fa58e30c,0x951bf2e5c3394f1f,0x6bff213c64c9fdf4])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x7ecd3f,0xfdfe2f0d7f5cfb78,0x6264c60fff8fff17,0xfff27ffcefc5cbee,0x599b255bf818e690,0xd5f62d135a030010,0x1fff7fffbc5d7cb8,0x8e7d7e7b52d779ff,0xf4816ce64ce32325,0x63b229d53a1e6032,0xa00000c77d3bff71,0xddbf3e7efc74d40d,0x217ce21dc408001d,0x4140afb8e6376014]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x77afff,0xdf7ff753aef3cbfe,0xd4fb55fffffff7fa,0xff8feff399fe3cce,0x1f7ceba6fe32197d,0xe970baeca42ebce3,0xbfe9b5ff7fca93df,0xf67c35bced6fff9e,0xbe2f458bb1cfc7b,0x21b91f3931619c0d,0x1ec1f32bf7dae49e,0xff860bda398b2f37,0x10191deee3f17702,0xb288e34da1d90ec8]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x24a00,0xd8000001d44220b8,0x606bd53000020700,0x120339d089e03a0c,0x1e18005018181455,0xfd7028e0fa2fbcf3,0xa209002404090301,0x8c30343a02013f1e,0x63c3fc600e9be077,0x61b91f113801ec3f,0xbec1f3e845308440,0x3707213a3c173c3f,0x101c611fe3f9771f,0xf3c84e59a2392edc])) : Bits)
  | _ => 0

def samplesQ119 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x10a460,0x41123010330c307,0x56104399138030d0,0x18424018023c0812,0x58672104263801f0,0xc29623d005814a80,0xb818f030cc080778,0x818121874008b823,0x8b8003e0033f20a2,0x9212482c0a000231,0x2143cc2ecd0514f0,0x244901b1c40334c2,0xb0836003c0110812,0xcc845eda4008a500]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x48902,0x101e01020a480340,0x80745601c040b404,0x90cd63083898102,0xd110004091041a8,0x10291604200e03,0x48c94a1243282460,0x4808202104888412,0x1921894000250e0a,0x40085d03a60c0b00,0x2452002c84a0442d,0x2242d4a12200902a,0x12820093020126c0,0x41c6543118a89084]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x2005d0,0x42a420822214b12,0xc2c620d490883070,0x4a2a84a9a1151140,0x90064000621089e1,0x425a2758448320ca,0x5a858c20aa1a0569,0x80932281c20c8902,0x9289228a010a4808,0x1498114f0c08a213,0x3162862ecc3408c8,0x162ab90145051c43,0x70c2210350522c84,0x85005ec31234000a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x132c4,0x4221787010a24483,0x1d8b297e0c920953,0x800108c134221e54,0xe0606db842431042,0x4e02d26082dcf16c,0xb71635c43441198a,0x94a14c8850710844,0xe04e242ad2d070b4,0xa6e280600070b45d,0x4384a45379199b10,0xd9352a564c314544,0x210c262c444ac017,0x1a10ab88e6176010]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x85001,0xa8008a450041080,0x2900880028304301,0x48100000c424620,0x208142900c52200,0x1c0140010a0c0114,0x520004d00c00806,0x304414181130028c,0x2442100148401114,0x1021050b214c0,0x28c00c1324aa002,0x4984000a18204310,0x180e6021085120,0x1209a104a1410a40]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x7db5f7,0xa77befdf6bffdf57,0xdfd66bdd9feafef6,0xdfebe5bfe73f3fdb,0xd8e7e76eefbefbfb,0xd2dfbfffcdf36bce,0xfb9dfc74ee7b37fd,0xedff7bb7c7cdbffb,0xbbdb63fe677ff8ff,0x9f9e79ef0f39fbbf,0x757beebecd3d9cf8,0x7f6fb9bdf717beff,0xf3d769dff7ff6c9e,0xffa45edbf23dafde])) : Bits)
  | _ => 0

def compactPerms119 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains119 : Array (Sig × Nat) := ([(subcube 1 0, 5)] : List (Sig × Nat)).toArray

def compactWords119 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount119 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath119 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive119 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords119 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs119 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords119 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords119 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket119 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP55 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xbd8fbff552913b0,0xcffee7df94fcd698,0xe0705443eef7c2e8,0xed83f12091fe07c0]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x114013003105232,0xe0004410919c870c,0xc8125f4820a060cc,0x7411cd30d91a8ae2])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0xf86ff37eed04e62,0x2fdfdcf3fb83af2c,0x4b820b0b77efe5df,0x32744c1048f9b822]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x8b020700680f27,0xf00e000306c0e6a8,0x61935fec024100eb,0x28447f78dd8904fa])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xdffffffbb7eff37,0xffef7f3ff7dce7ef,0xfd935fefbbf978ef,0x7c5dff78dd9bcefa]))
  | _ => 0

def samplesQ55 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x427142499b66c0b,0x356d089c1706f948,0x920c678f8e85c4f4,0x29878144e1fe0540]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0xeebbfc7f4ff8fdd,0xb9df75fdaddbf7f7,0x83efd3f2b5b76fed,0x57d9dfa7dc5aebee])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x790c59112ae49d,0xcb27184495283201,0xeea4f52f65cb055c,0x38c6851942f93802]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x8b8245c0620704,0xb8d5602408cac371,0xa74142b1364644,0x429884a58c52eb04]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x200220040010040,0x80050128c00030,0x1010302801,0x40050a00c00c2a8]))
  | _ => 0

def compactPerms55 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains55 : Array (Sig × Nat) := ([(subcube 1 0, 4)] : List (Sig × Nat)).toArray

def compactWords55 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount55 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath55 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive55 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords55 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs55 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords55 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords55 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket55 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP247 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xbc53b8fff3bffb0b,0xcffff71fcdffd3da,0x95f47b75bffb480a,0x58fdd36f688e4b6c,0xaa730fda7d07e458,0x500d09dbdb22a40c,0x25264543751b7340,0x37c20f3ab00688ec,0x86f1618a63840223,0x15010080013dff65,0xffd8613ecfdd379a,0x5f9e79d816c1a026,0x98289bcda1659374,0xce8602a1f8708400,0x900041908aa395fe,0x1f331580c6d89100]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xdffe2f7f1dfa6fab,0xf8ff11fd76fc9517,0xda25c6c8feb867f7,0x47923f4ff151fef4,0x6dc9fa522dbbfbd,0x1132d6e672807882,0xd9ba4ea0819e62,0x400cb2d4f1181313,0xff4c005a841a25c4,0x48002600f46f1b7e,0x78c3fd138ce7e4e5,0x58e5d83d67945de0,0xe78b2438a45600ce,0xe40f90b23604a04,0xe21ae43704007d1,0x9485683aa3c20c4c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xf3fc7defde7f75fe,0x8f83be86fbfae2ef,0x6b7e84a5c53db487,0xdd47fc917ef21cbb,0xf52723578ffc1200,0x6bc8752400cd1033,0x920d1a08d9e609bb,0xc0f2042706e1e4cc,0x80afff510614018,0xa036994f083fbde7,0x8cfe0768789ac9de,0x14ebdc57ecee4059,0x3951c4f351a2fc80,0xd01b8d32138e001a,0x61ce102c01005df6,0x21c26c4f18052013]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xff93f7f9efdf8df7,0x3ef3ebefbc8f2fa2,0xe9cb7b8b47c54f0d,0xbefe2371176fab53,0x2db4fc3d8ae7e3a0,0x2e72885ba42cbbcc,0x1a29a4b38a1c82bc,0x373de8c948390813,0x9011e0a04180504,0x2c0003032b7efd2,0xcf2ba6fdbf293969,0xaf6d66ff91f99e45,0xa635630c40996388,0x3d650c9dc48103e0,0x31a20144003aed,0x38549a8c1db04068]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xffedef8ee1e59e57,0xf7fcedf17bf36915,0x2425bd36f946d7f8,0xa76dc3ce8ea1f58b,0xd6eb6fbad2dc5842,0x914d20bd8d50c771,0xc0f6404d5f619d9d,0x880cbd20f127e413,0xf0b28050e0052203,0xac023ac0c852def9,0x7737dad34316daee,0xb715a7228f6a1d98,0x584ad8355a480331,0x1b8f64adc6e4c04,0xee0051a280822e2a,0x4aec8175a428ac10]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xcbbfd273bf0ffefd,0x733d5e7aff779eed,0xff9be87e385ebb73,0x68136cb49b9e57cf,0x5b88d0497d2180f7,0x848156001197003f,0xfdd285b4047a6442,0xae342930edc3b6c,0x3f70f259b809828,0x113d4105013a7799,0x326db8acf662fe31,0xe1fa1b87fb15a23f,0x468418c22fa7ec6b,0x209c70440390b01b,0x11c000140a3dab0d,0xc31872705b401383]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x646fdf947ef0f3fc,0xfd4effff870d7c78,0x16da17db02a3b8fc,0xb3a89cbae57da034,0xf95ff0e6f53a4d0f,0xeeb6ab006e7b4fc0,0x6f007bb022846005,0xfd11514c0fc257a0,0x740cf0a50862d8d0,0x42c8c43a068de0be,0x81945fc731fd0717,0xea12a7e878026382,0x1f627029e181c17,0xf36303f42c1131e1,0x1e0c48355c7010,0xe42b8783603742a4]))
  | _ => 0

def samplesQ247 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x241038939330800b,0xcc41161d498d5130,0x134e85142980001,0x15a94005721c0018,0x2230c848d058950,0x51c42a003587b400,0x4a06254fa8868146,0x220098e4904a8a0,0x8d0c9100107a0214,0x54091a35087db964,0xc14821164edd009a,0x4a8a41c806c5a040,0x180947c120c08060,0xce010023e8018405,0x10305254816255f6,0x1d130580c2909000]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x32a280d104a60a1,0x482a00414064c110,0x4310c04024200244,0x158002081011120c,0x2008204021600c4,0x4101016262988c80,0x50480f04520,0x4001040ae120405a,0x63040c2452008014,0xc621000808691064,0x288114120442a481,0x1881980562841120,0x481042980528040,0x492320402004,0x4d800249f0210551,0x9480602a8240080c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x122004ce0a4c41c2,0x8003900229486374,0x11cc840c0890483,0x158a48003a14083a,0x4205041681048084,0x10503948500d0914,0x2082a30440402,0x90440d0082286870,0x4a08283210280696,0x550148118a7db962,0x8cc006206882014a,0x104b901644048050,0x2901c54151c0c840,0x4403803362040488,0x5904900d200055f6,0x21804c0e10010012]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xd8114660cd950d50,0x24c0c28ab4830022,0x2885098449885811,0x8a1c4050232621d0,0x251154019140e300,0x8c1e148904625155,0x1c4588601c028a50,0x9c7680d0028e0280,0x4233012a8a92a08,0x38448c911116ef92,0x460a22a8b3291960,0x866444b291588441,0x8a10694402890180,0x642d148c408502ca,0x8024e03206083aac,0x28541a841da04040]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xc8c4c30060801604,0x139469a002120800,0x800112418049930,0x4481420422a4c0,0x100110850c81229,0x608808480604002,0x9130c21007083a08,0x910606010430505,0x10530281a1801800,0x28d4000234024699,0x1236c8c101004a24,0x25142620082a0c81,0x20018100a000310,0x13c300410221a20,0xa24204a20484aa08,0x426c805124282400]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xc18f002024032830,0x233c086094300089,0x9802010c08421810,0x6004244000a260c1,0x1988100010402021,0x88030427021000c3,0x461400002386030,0x4403c0303081060f,0x3060060520804941,0x2844004050824691,0x302598089020f401,0x81300a01b108040f,0x420408000224250a,0xac104401003042,0x26c020005289aa09,0x8208327009400181]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x244091100020920c,0x1000251402000400,0x440060200002008,0x10a080400000,0x8040206020201818,0x280820081002000,0xc31022110100100c,0x300200408408100,0x8010818004040020,0x2210000000008,0x110414500140214,0x6000214808004200,0x62000204001005,0x1040020004128821,0x12048001460000,0x4023810160160220]))
  | _ => 0

def compactPerms247 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains247 : Array (Sig × Nat) := ([(subcube 1 0, 9), (subcube 4 0, 9), (subcube 16 0, 9), (subcube 32 0, 9), (subcube 64 0, 8), (subcube 2 0, 7), (subcube 0 1, 7), (subcube 128 0, 6), (subcube 18 0, 6), (subcube 34 0, 6), (subcube 64 1, 6), (subcube 6 0, 5), (subcube 66 0, 5), (subcube 80 0, 5), (subcube 132 0, 5), (subcube 192 0, 5), (subcube 196 0, 4)] : List (Sig × Nat)).toArray

def compactWords247 : Nat → Nat
  | 0 => (limbs64 [0xe2a628e28818204,0xc167b6ba0f988985,0xb6ba0e1ec103ae80,0x667a478a89462629,0xe38a78aa88184081,0xb6b9e8288a9fae82,0x8e7ec1840803eb9e,0x822a888182005b69,0x98bac838a64878a2,0x6a388a8a387a8408,0x1b66a89a18aea99e,0x205ba73e7b693ee9,0xeda67a8bb0a985a1,0xfa9fa6a2a218409f,0xb6ba0a06639e3861,0x206da89a0b9aa78,0xfb6ba0b99e4eea6b,0xa0b99e46e9eda0b9,0xee825b6a2e650dba,0x3b6a2e9b6ba6678a,0x1840edae82819893,0xe1840819edae824,0xc28a5a5b6b36628c,0x8edacda1826dae62,0xe878fb6b9e860a60,0xf30932639828866c,0x2e63e826b30bb061,0x2019ae62693183c,0xc185a83a01b663a6,0x78e64c66c1827801,0x67ae866a307b040e,0x82cc20198fffffdf,0xfbf7ffffffffffbf,0xff6ff7ffffffff7f,0xfffdeeffffeff6ff,0x7fafdbeef7bbf7f6,0xff7fbddfbbffdfff,0xfffb7fffdffff7fb,0xfd8e1a9c35385e72,0xbce171c2d387c537,0x4a6e9cb309a272c4,0xe1514c9299672ace,0x549cab38d671ace1,0x59c2109847304e50,0x9ca139027184e209,0xc1909b47364e6c9c,0x59380a531c26304c,0x5098a131ce631cc6,0x398a7314e621cd84,0xd84b14d04c94c84c,0x84a04c5c1fb0e1a8,0x7fe3fc112c7bfe3f,0xc144ff1c1c0f73ae,0x1db8c596870ad0bb,0x3104a025267944,0x6209404a4e4f8906,0x20d4149ca2520c41,0x15f5a4e5120c201,0x54b49ca2fa906208,0x293944a310404a4e,0x512b062080b49c89,0x1fffffffffffffff,0xf8a64a6c26826426,0x26c25425a23447f])
  | 1 => (limbs64 [0x2048912408f2388d,0x2300c22c8a225078,0xd8005abd7804082,0x205e01022635393,0x104fcf9f017c790e,0x17c570be477af2ce,0xb10efe82f94da85f,0xaf2ceb0508102ea0,0x408102040817819e,0x3faf03357a1d7be,0xef3bdbf5fdf77bcf,0xfafcffbbcefafdef,0xbbeeffaeefbbeefb,0xbeefbbfebfaefb3e,0xebbbaef3bd7ebbce,0xf7bdef5eedfb7bfb,0xbeefeb6fdfb3fcff,0x6fdefafeef3bcdf3,0xbcf66d0336819b40,0xeca0305068281134,0xdea0ec4a62e8297,0x40cba0754a65e81d,0x339689cb4d01a453,0x5129a9a0b4505a68,0xcf38e79c61d030e,0x838741d484c94263,0xa131d4007a068426,0x4483214190a0124a,0x672808b40c494c2d,0x51681c54162a031,0x5078a80b7415ba06,0xdd056e81b740c0a0,0x805030281672a536,0x72a13671a13670a1,0x3613212c73212c70,0xa53453613413212a,0x73212a72e13272a1,0x3272813271813271,0x612a71013270c532,0x70c13270a5321361,0x2a13212a13013073,0x212b6025cfa909fe,0x4c9f2894d198918,0xe3976ad2b050b7f8,0x1fe07f81510cec46,0xd67f804419827a4c,0xbb1cb6d2bd3fe005,0xb6f02e6973a11dc9,0x9146c5bfe00a3b0c,0xa76cffe068229f5d,0x74d944ff81fe03c9,0x4b04558d0c6dda17,0xef6901fe04fae9b2,0x9855b03c7c0c44c0,0xbc0630c010054f3a,0x6650227132f59524,0x98a48920b8aac432,0x96f947aa3c51db8,0xe166dbb5199c4cc7,0x62a30716baa8750c,0x266122e8a84131f3,0xe166572f395e09e,0xe4842230fa46b829,0x213d07503360ee00])
  | 2 => (limbs64 [0x3fc0c8a29,0xffc3fc3fc2c199a3,0x78ffc0713fc1e97f,0xc0d64d465b08ed2c,0x2128f10000000135,0xe3be75cebd573af7,0x1ee35e7bc67a8ef1,0xddb48df48eb40eb4,0x8cf48cb4a0348c74,0x8e54851099241a34,0x8d748f41d09809a4,0x1938b09541e39909,0x541e29b099407395,0x2994063990954013,0x8b09509939409909,0x938c09909938b095,0x993880982eb5229,0x525ff006d1ff0382,0x81203fc0982c99b6,0xc27fc0087abf0ff0,0x3c753634a001756,0xea32d66b2504f1e1,0x4e1421a857f72330,0x5ffc0350ffc087b5,0x3c8cd06daf7e8b2a,0x61bb8715ff03dcea,0x3c7fc0a41345c429,0x6140e33fc0200aa,0xd060a7fc0ff01ca7,0xff03fc08b3c599f7,0x592f314b2734604a,0x34d651812183a708,0x4060052008027114,0xc470441300401013,0xe2f43d2f0bb2e938,0xe0b74d4350d4350,0xd4b40d0b30ccb24c,0x1ad8a5a6a8421874,0x9c07316254940511])
  | _ => 0

def compactCount247 (k : Nat) : Nat := match k with
  | 10 => 1
  | 9 => 8
  | 8 => 46
  | 7 => 54
  | 6 => 13
  | _ => 0

def compactPath247 (k : Nat) (i : Nat) : Nat := match k with
  | 10 => 0
  | 9 => readCompactBits compactWords247 (28 + 12*i) 12
  | 8 => let v := readCompactBits compactWords247 (969 + 15*i) 15
    (readCompactBits compactWords247 (873 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 7 => let v := readCompactBits compactWords247 (6107 + 17*i) 17
    (readCompactBits compactWords247 (5555 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 6 => let v := readCompactBits compactWords247 (10026 + 16*i) 16
    (readCompactBits compactWords247 (9630 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive247 (k : Nat) (i : Nat) : Nat := match k with
  | 10 => readCompactBits compactWords247 (0 + 7*i) 7
  | 9 => readCompactBits compactWords247 (124 + 8*i) 8
  | 8 => readCompactBits compactWords247 (1659 + 9*i) 9
  | 7 => readCompactBits compactWords247 (7025 + 10*i) 10
  | 6 => readCompactBits compactWords247 (10234 + 11*i) 11
  | _ => 0

def compactPoolIDs247 (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let v := readCompactBits compactWords247 (22 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords247 (7 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 9 => let v := readCompactBits compactWords247 (633 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords247 (188 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 8 => let v := readCompactBits compactWords247 (4095 + 13*i) 13
    let n := v >>> 9
    let bits := readCompactBits compactWords247 (2073 + 6*(v &&& 511)) (6*n)
    compactIDsFromBits bits 6 n
  | 7 => let v := readCompactBits compactWords247 (8048 + 10*i) 10
    let n := v >>> 7
    let bits := readCompactBits compactWords247 (7565 + 7*(v &&& 127)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords247 (10377 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords247 (10377 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket247 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let d := readCompactBits compactWords247 (721 + 3*(i % 3)) 3
    let off := ((i/3 + d) % 13)
    let v := readCompactBits compactWords247 (730 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 8 => let d := readCompactBits compactWords247 (4693 + 4*(i % 16)) 4
    let off := ((i/16 + d) % 57)
    let v := readCompactBits compactWords247 (4757 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 7 => let d := readCompactBits compactWords247 (8588 + 5*(i % 18)) 5
    let off := ((i/18 + d) % 68)
    let v := readCompactBits compactWords247 (8678 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 6 => let d := readCompactBits compactWords247 (10403 + 3*(i % 5)) 3
    let off := ((i/5 + d) % 20)
    let v := readCompactBits compactWords247 (10418 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP223 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xdbf05ef7fca7ebfe,0xb731fb3a5bec2f12,0xdef9dc4acae74fe0,0x4c6b706e7f69ef40,0x6c69fcfb91aa1005,0xed0e5d320201f7aa,0x407608c1cdb06f1a,0xb57410395d9c64c,0xb0833c0300018626,0x2814df37db5d7c,0xbe2fad2cc6fe7435,0xb3f69de13596c4b6,0x600fadb31d910a9,0x8d3843a1906d0407,0x10801180720a3b5c,0x375d111a98ac2844]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xfcffe0fcffd9fc3f,0xc7fe001fe4002ffd,0xffe200bffd80fff,0xf383ff907ffe03ff,0x903f00fbfe401ffa,0x100ffec003fe000f,0xff800ffe003f9000,0xfe8017c6a000fb0,0x3203c387e1800,0x1000007ffee2f07f,0x47f00e0ff8f83fe9,0xfc37e1fec1e907c3,0xf80702e4072000fe,0xfc07c01ff800000,0x2107e60f840383fb,0x9c67e42500e90118]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xcbbff7ddf7fb7fe7,0xeaa85f74a77fd022,0xf85f7ff51b67d246,0xfff5bdd3b67651db,0x9876af04008fa03a,0x6ff080ac7c202311,0xa38c6106164a901e,0x9b6c0401a4828,0x37fc4380c2806010,0x81c0e1ffffffe5f9,0xdbfbc6da9c27d852,0x1f5a8e8edf49b101,0xb0451d015021bf41,0xd03fa9be06f00070,0x61808700887fffc,0x42086d4da3028003]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xb7de3fbfcf7d3f37,0xfccbae873838f3c5,0xf1a39fffe4b9fc79,0x3c72c0e3c7879de3,0xf7b8d0820db0d0c1,0x68d3037159c53d0e,0x4c147678e86103e0,0xbc2670079164b04f,0xc8789c0204000505,0x222b10a7eefd9ba7,0xeb9cd7a31b35bf5f,0x62ad67331e90b658,0x398203aacce4c84,0x273d5cee964e406,0xd0a011004103dca9,0x29e68a6aec100464]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x26ef9debfb27d7f9,0x3fc5f4dd9bd32cea,0x2f05c38b3526bf9f,0x8c1f8f6df891f2bc,0x6b96e3f861150f05,0x820da10da3fbc855,0xb0698f21320c6ce5,0x4490897b94a629c3,0x4f03203830701040,0xc140aeabdbfaec2,0xb5cf79df25c7ab97,0xcfb11bdd29760b2b,0xc5e6c618c6d6e050,0x7e84225160120380,0x2947840c00117d66,0x589216964f644190]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xff1ffb1613de89db,0x7d765beac6bfd9dd,0xf0beabb46f5a2086,0xb38c0a1c080fbc25,0x6fcb7f343e7260ba,0x92f012c68400c4e0,0x453b003ef9606ff,0xf3c3debc2e0df310,0x83fcc1410501a3bb,0x63c36575c11e0a09,0x74033af56359c7a8,0x3d4bf40ffa2e48b4,0x4bb83d65d931af36,0x200394400699f879,0xc62008a033684287,0x82307a8053d83e23]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7d61ef6b2cfef6cc,0xdb1fa5e17dc7d63f,0x7407474909df139,0x43fc77bf81f86e1e,0x97c51f45c24def44,0x15206c1bfc1e1af0,0x1babd09c11c1f901,0xf03c2e806bf314b7,0x7c04c2c4cb8e48c8,0xdc148a985b657796,0x874f170ff8a40ee,0xc0cc7a70e601784c,0x3c7bc1862a0e530b,0xf1cc0a3e190a1b88,0x85862538cf4a410,0xe58981f13417d288]))
  | _ => 0

def samplesQ223 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x105052c31883e202,0x271000443a2c0912,0x2618080041254d20,0x11385e41100141,0x64142c3050a83085,0x100130a706211054,0x185629c434530604,0x89d280004318d74,0x4808102f8005a0a,0x21470d931ca4d0c,0x1628a10cc6805431,0x91d01960110ec500,0x205d84040c90021,0x8d0401a190030409,0x114016a04e062b54,0x171d011098a42004]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xe859a054a7513024,0x1620004a6042a10,0x49c2091072140142,0x522c8d2d9a8000d,0xc0040a2080490,0x24cc6aa81018200e,0x8942471d41088241,0x21130011084c5355,0x325490303245956,0x18155d6e04071,0x4350040650580688,0xb027c13ec18896c0,0xd80502a0022100a0,0x241382112205002,0x9602264f020b82db,0x9466e00500880018]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x4325131072e00ea7,0x4288c3442b0e4850,0xe28c4f326b14470e,0x1f725c57f3f48059,0xa93406102232420c,0xea8531c0c917a08,0x488ec9210222028,0xc202248c4090a20,0xd2143992526c5a23,0x44a739ffffff2459,0x88cac64a90231840,0xb4206889acab741,0xb0854c0940438620,0xc41f10b536600121,0x429096a4087fffc,0x42004d0da2008002]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x87882d2884281911,0xd8018a020110c0c4,0x4085151aa210821a,0x3522440096a1888a,0x8b0002068152c450,0xa3308550b0020f00,0xc528102242a41140,0x6520515548c22089,0x80210ab402250081,0xda10126ce3592a2,0x891442a109342a4e,0x402c24130ec01250,0x9190041a00060c04,0x4031500c6a244802,0x68a229108191d4a9,0x28c28a6a24100440]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xa6088a400685d8,0x2c00865109884060,0x220c840301026688,0x101416240210d260,0xa912869a4481934a,0x8801800288e04460,0x20b090002e14292e,0x10c4138c92320488,0x5c1820d054002601,0x94a434aa291faa00,0x348719d12487a113,0x4e1012812072010a,0xc24c0844520440,0xe41402c4201625b0,0x2109808011307d24,0x481016924f604100]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x2802800401140048,0x10a840010008,0x1020008404480000,0x8080000000022000,0x500804010102,0x44080000480022,0x2000020909088803,0x1042008012045000,0x908440000920000,0x20000000000,0x6001181020488180,0x2401c00460000024,0x20200099002112,0x840000803090,0x8200800510280002,0x8020308041480a21]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1400442108084000,0x9004200000401401,0x204000801001,0x4008010000000400,0x10c1010411402001,0x1110044122020110,0x5004006000c11400,0x400848000080a000,0x80800800008000,0x2048000000001186,0x2020200b004024,0x88284004010800,0x408010420005008,0x1080000201090808,0x48c010108c000000,0x2189006010171080]))
  | _ => 0

def compactPerms223 : Array (List Nat) := ([[], [65], [16, 67, 118], [16, 49, 67, 118], [48], [48, 65], [64, 65, 67, 118], [64, 49, 118]] : List (List Nat)).toArray

def compactDomains223 : Array (Sig × Nat) := ([(subcube 4 0, 10)] : List (Sig × Nat)).toArray

def compactWords223 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount223 (k : Nat) : Nat := match k with
  | 10 => 1
  | _ => 0

def compactPath223 (k : Nat) (i : Nat) : Nat := match k with
  | 10 => 0
  | _ => 0

def compactLive223 (k : Nat) (i : Nat) : Nat := match k with
  | 10 => readCompactBits compactWords223 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs223 (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let v := readCompactBits compactWords223 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords223 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket223 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0xb7ffdf47f4960dff,0x32e4cd917a90f57f,0xea141773da3f6706,0xfe0906fbd16733e2,0x6faeca2817efe079,0x2002fc5c61feee44,0x7ac330141e867701,0x70cca2e7f0001721,0xf015f8040009e001,0xf85dd7893f424aff,0xd254396b7e1f746f,0xc419ab9a8697c1eb,0x814ec412f2006483,0x607e583073e00e30,0x17007f17c049095,0xf28bb42e88b1188c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xfc50effc19597069,0xff3ff16003ffcfd4,0xc981286affe2abd8,0x1c5fff0d69de003f,0xfaf915036001fff0,0x417d0003bb079e62,0x76eef4200000ff,0x8f5348000837ffda,0xca003803fa003e6,0x176fbd5e6c11fa0,0xfb87ce3c1bf6118f,0xf1823fef6c6032d7,0x6401fb400257d814,0xfe3908d835f0000,0xf807b80e8086a939,0x84e03c53d342a023]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xff97f1fffedbff96,0x83f3e75fcc70fa4,0xf63feb95e43e917d,0x23af385ea157fd9d,0xd01f9045f040e8f,0xb25f781444003183,0x7a880503c02d8d20,0x7a2153a27cbe000,0x300006800460018,0xff7fffb6bfee2c,0xe2ef3fbfe4e3d5f1,0xbebec22c3164cc04,0x19f00ec7e1ae1f03,0x23806b4df0a0f000,0x68040000107be7f,0xa3398b6034780210]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x7e8fd8f1fe43f07,0xefc03f8a2f07f000,0xffe1ffff0042be9f,0xc3f01f8ffea9fe63,0xf01e0007a0fa1010,0x3a07fe80607c03c,0xbd0cfa03ffd20641,0xf8001fc037fc0001,0xc001c401c0005c00,0x36fbe3fefae7f0d0,0xfdf9cfc3817beabe,0x1f43fc33c3988ef8,0x1e0310047df8601d,0xd00381f26c10001f,0x180780620f4fae,0xc7434583278440c8]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4fff3eb7eb69cdf8,0xc2e4f26eb568f57f,0x15ea148c25bdd8e6,0xfdf6e6f42e9933de,0x6fb135d017100066,0xdc0283a399f91184,0x4533cfe81e867080,0x8f3342e7c8001720,0xc14018407898061,0xc0bfad7bfdbab5ff,0x2d5a36977f9c8b53,0xdbe554597a973114,0x614cdbea8c001b62,0x9c7da6300c0f0e20,0x19608005000377de,0x8f6421d48743820]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xfbaf0ffbe6a68269,0xfddb0e9fc3ff3aab,0x367ec06affdd5421,0x1c5ff9f29620cc3d,0x9546eafc8801ff8f,0xbe800003baf86199,0x8075110bc17988fe,0x70acb5180837e8e4,0x34a027a38560398,0x1e8fc27d93c1f5f,0x427f1c09be9ee0c,0x2e7c3ff491083328,0x9ab124bd0257a7e8,0xf9c6f420350f1c0,0xe687400801714dc1,0x781c3b9c23880713]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xf87ff278e13ff296,0x151bc1ffdc380adb,0x9dfff951bc16ffb,0xe3a0c1215ffecfc0,0x92c006fbe8fe0100,0x4dfd87fc44000e7b,0x878800fc2179fb1e,0x5de81dd7c808de,0x30ea3c13c0303c06,0xe871efe4d5de103,0x1fb8c07ce4043ff0,0x61ffc1c40c6b4c03,0xe6be21391da980fc,0xf000148f9ca001cf,0x838729ef8f262,0x1d04c0e0dc0fc544]))
  | _ => 0

def samplesQ254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0xa224800284020021,0x1020102038826218,0x281000200812010a,0x120000005001010a,0x605020014408c4a,0x910044000420502,0x32b1201109082000,0xa214129502310c80,0xc091412000004c,0x8114508100000a4a,0x9200282258012403,0x4410ab880222c061,0x8100840012000803,0x2132500001004500,0x1546022278048011,0x7089b00a8020100c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x8410494011110460,0x60834603206cb50,0x2410016858202018,0x2ca800148404018,0x8415060418205908,0x10a25010500222a,0x2261014084000589,0x9150020401208a08,0x8081b00002500959,0x855472c520400820,0x58848c2010d2100a,0x5082312e0060e0d3,0x801130000c31812,0x360408423040004,0x5104d10a50868831,0x84a02c0392008022]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x5716b15828499da2,0x4a595c3272424734,0x74b94f29c8806048,0x23862a58cb4ac448,0x8c50654c49549192,0x24b6108c856324a5,0x94455254a1d35a1,0x22c449005281451b,0xb584941206cadf48,0x81d77ffdb60dc42c,0xa2cd031be08395e1,0xb8a8c2262024c451,0x38950ac2a58e0c32,0x120e25cf5226640,0x98c228858fba7f,0xa331896014780200]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xc07c0c0281b406,0xe2c8050086480121,0xc580d50c4444a4c5,0x64821f02ae605021,0xa8082811c03c6010,0xc288a9211211d20d,0x400e1c48a484822c,0x11a088003940a22c,0x8f16068c4a606900,0x106ba366fac60080,0x6c61c5c00178c8bc,0x3035412e1140e18,0xc0302886c824118,0x1405817620141016,0x60101185032b4fac,0x8642058127844080]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x494b02a540e09102,0x60454206c1681027,0x40a04c85248c48c1,0xec002b14a23a34c1,0x68aa5060a2020221,0x52059084ea285040,0xc40a422862431a02,0x823244aa88c4162,0x150e04aed882c402,0x38ab8d3addb2b595,0x5121295270c0210,0x896500416995060c,0x205440e8a4080320,0x9c0c8252842322b1,0xa210815021177ce,0x856421448542800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x20a804a3c0800208,0x2100008080090081,0x2440006060410a1,0x441141a020201005,0x2102183106082661,0x8800086030108100,0x1490281001c08004,0x80194d9805420c0,0x22488c48000020,0x5228800248301353,0x2270400a206804,0x6500c9051101308,0x200000d0010a180,0x14840c0200401182,0x2e63008028204580,0x500c129c21800111]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1801021020444110,0x3c00b40100004,0x22281101814200,0x202010008e0e40,0x1060010821020080,0x34210008480800c0,0x8900020400120802,0x2610240080002,0x5000000201878480,0x800c1805096000,0x118000c84040340,0x200c004004080000,0x603c205080280064,0x400002018ca10061,0x88081084103042,0x9004060480b0440]))
  | _ => 0

def compactPerms254 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains254 : Array (Sig × Nat) := ([(subcube 8 0, 9)] : List (Sig × Nat)).toArray

def compactWords254 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount254 (k : Nat) : Nat := match k with
  | 9 => 1
  | _ => 0

def compactPath254 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | _ => 0

def compactLive254 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords254 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs254 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords254 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords254 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket254 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP187 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x94800a80002381,0x1304c1c39708ec0,0x20180600894c04,0x5e6107d602108583,0x42003fe01f00fc08,0x7fddecc1c2002040,0x7e018018f001d60,0x6f0212dc114557f0,0xc31c863fd3008f4f,0x87c799fe4ca0ac2a,0xda0b02183ec7c01,0xfce05c197c7ee16e,0xe8ddac495915a5f6])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0xfcfbffffc7fffeb,0xd4bf8fcd6c79efff,0xff2fffff768363ff,0x7efe0fdfb7f3d5e6,0x43f03e7e1fb56f0d,0x761decfff7d57ddf,0xfe9b747dbf81d1f,0xfffb7bcd3911d1f2,0xc733f23fd3801fc0,0xe7c701f20ee59a78,0xdff3a6b703e2fd21,0xf009ee1b4f3e2126,0xe8d48965f131c4e6]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x2095c0008704032,0xc80f8deb976f2bc0,0x6026000602303bf,0x1c2a0885d08d0841,0x31f27e7388e737da,0xebdffec400804480,0x80032629a0d80c07,0x990e78f5c3fb8e80,0xae8bf57bdbc212c0,0x7fff99ffcc014258,0x2241446403639fe0,0x1c13b8fcb37ef16f,0xefff01a32ab27ff6])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xbf9e7fffbf37373,0x3d6efd9b1b161bbf,0xfefe7e77ffadafa5,0xdd67fef5d26d8ddf,0x302e7bd068e0f4d8,0x9dc0cc3ddbfffff8,0xf67f3fa9efc67e61,0xe93c14d6d34ed690,0x9a9c957a1aba816f,0x7640982c4bb1eceb,0x2c5f7f7dcf0f07d0,0x7ef0d83d3042c16e,0x8096dc948ce7134]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xfbcd3ff8fffe394,0xebdf4e2697618a3f,0xefffff9ee97bdffe,0xbff90f9e4e9c2a79,0x83c03c61914a13f2,0x681612ffeeaeefff,0x8f864eb9a4ff9ffe,0xffc68231c6e32e0d,0x27cbec3fe3401e00,0x983b01c383fbe77e,0xffa8d568f3f0f8c1,0x8c1611dcb33c3001,0x762fc830e33aac0]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xef75bfafffcfcbf,0xcb31fd78b1ee247f,0xf7f3f9effeff5c1f,0x5e2bf1e7f99fff81,0x7c13c7a38e07bc0a,0xebc92037fffbf6e7,0xf1f3f87fbf19ede7,0x1f0e78fc01fd0fe0,0xe80c07c1dd47e2df,0x184981c45fe7f9f,0x23e5f8e7806d1e2e,0x1de33ce0fc40c048,0xe09db63a3b943512]))
  | _ => 0

def samplesQ187 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0xf6b7f7c7f7bde7f,0xffdfbbebdecf7df7,0x4fefdfe7ff754ffb,0x9e9ef7c9faef75fc,0xbfffff9ffeff7ff7,0xffbafbb1fae7ae5f,0xf7efdfff8ffffd7f,0x6ffdeeddeeb957ef,0x3b1f79ffd0ff6f4f,0x7fbbfffdbffeafaa,0xedbcb7e1ffef7dff,0xfcff5ff97fbedf56,0xe759fe4f5d57adfe])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x30402201a00010,0x2300201291040004,0x8409100100909508,0x820403280000808,0x2009010000421020,0x140100b00500094,0x8900000900810,0x4408204001020814,0x404100108b110034,0xa800140000000050,0x9901029302404120,0x1008440002102482,0x48a00124d0210086]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x2095e0429384422,0x4c0b886b964729d6,0x41804724323105ca,0x8e0a6088e225614c,0x5626e04a2852593,0xad9abab1b2630a5e,0xd720434a89272142,0x1d126584c3012c6,0x2a19489cc09b4246,0x35a9a16c93fc29a2,0xcd94a381f484085b,0xa4a4024954980752,0x4211fe4c55458008]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x40618400c0c3c04,0xc090802024e8e478,0x9200060e00f4045,0x224600406980a260,0xe30020d86080300,0xe20b01d019ac6940,0x80644e0180207101,0x35913914492000,0x1f04908414c081c0,0x1003e031829180a1,0x205a75288c8e04c0,0x6c04003800c31121,0x4968c100ce6120]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x432c103411144b,0x440291c8488a55e3,0x304ca202b0440a3,0x414324018a451a0,0x1464ca96aa114d11,0xa6a0e130c886a40b,0x9222429a856a250a,0x235088054a291261,0x1104704a50486503,0x89aa649ffaa608,0x64a8146055a42842,0xa4361148150e5200,0x2348fc030c12a840]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x108a50590014202,0x144602854a111a81,0x6042428207202020,0xc1191a8c16111084,0x80c0580070210455,0x14344e2466019621,0x3281002e03028026,0x9420e06021480a3,0xa0b82e4220023601,0x29800c431665f0e,0x224884410011806,0x806108c03c044058,0x3116961a2b101410]))
  | _ => 0

def compactPerms187 : Array (List Nat) := ([[], [116]] : List (List Nat)).toArray

def compactDomains187 : Array (Sig × Nat) := ([(subcube 8 0, 7)] : List (Sig × Nat)).toArray

def compactWords187 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount187 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath187 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive187 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords187 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs187 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords187 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords187 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket187 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP191 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x1261fc7391b3e7f9,0x346cbd06fe53fbbe,0xb92e06ff8cf9f4a0,0x19c3abcab9e13a08,0x61fffbabb8029101,0x6cb2c86616ec86ce,0x406c00dcb198e8ec,0xc2698641fc022c02,0x9c0c0035404f99e,0xf787a37afa7306b9,0x77c5292f7957738d,0xd27cdf2c80c15028,0x233e33c070f66347,0x18de01e70784142e,0x44042e424241b94d,0xdd92d2aca9458809]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x7f8e1fcd88ff54c6,0xfbd2a0afc78e63e5,0x9cc07d6e4e1fbd4a,0x7ffd507fd76d027b,0x8c028e710009ee0e,0x81ccb393794727dc,0x91ff635b401001,0x7db4003fc07c523d,0x92001e4400e95f3d,0xaeccf9ccab0fd313,0xc3a64ff9ce8788fb,0x40deaa8167b9a30f,0xcce2013e002a07d8,0x7420c93c9981e841,0x9039d115886a132b,0x8b3179124a1c21c6]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x82f26f8e6f3aa73f,0xcb935fd1a4539c45,0x5ef3887d0ee65fff,0xe183ffb5641adda4,0x427d004055f40410,0x4f0f079ca1b8a833,0xb7120010446f1706,0xc7075e038181c0,0x240f21808310ef5f,0xfbf5fd93e87dfbcc,0x60bff00f9fec5273,0xaf10ecd39810ffd0,0x74c5cc000089f807,0xe72f3e0206780010,0x9c200a814fcbf8f,0xe02c81c774205210]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xedff91e2f6c41a39,0xf5d8b75607ed9e7b,0xe17fcf8ff1181e0b,0x6619e3ce81827158,0x8f80f009b7c781b,0xf4f0d444ca071024,0x608810652487eab8,0xab09f8a00c020000,0x180c0005404fef9,0xfffb5e6727b5e5ae,0x7f3adedc6afa9f3c,0xe567733c9cee0406,0xf6fc7f31848e,0x180c36389e04040e,0x44002040407f6ef2,0x92d46a54a5b80009]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xea9de271694bfbc6,0x34b75afef9ade43f,0x46adf6f073266b54,0x9e2655b2b81c2487,0x9580f4d4a682eee5,0x124d20691d125909,0x9867e8a28960e853,0x1987981e070500c,0x503002382822b5ff,0xcb7fcc9dd5a8f8f6,0x8cf82626f25b6fcd,0x3bfb1ccc6037a830,0x5b39300fef481bb0,0x8711c1d860020b80,0xb23810042131edbe,0x2e49250b81c70464]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7d701fbe76fca8c6,0xcf2d40a9387063da,0x63107b91b1dfc2b5,0x9ffeae7d6e92c274,0x7202718e400b11f0,0x1334c0366b8c7d3,0xff01ff9c1abf0701,0x7e42003e30002db2,0xc4f1d8780d17ee2,0x5d3ef62c54ce2c53,0xbb599fd1b524f4f6,0xbca1b57267405ccf,0xb0ddcd3180558420,0x6bc0c8c361f9f071,0x8060e92021752f4,0x442f06211a7a8b90]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x950fe01d9f055d39,0xa6fef795bbe1d80,0xbfdfb102ffe1a1ff,0xe07c1c015a658d83,0xbf05003f6ff503ee,0xba003bb880417820,0xffe070be61015fe,0x9436ffc0038d8241,0xe23020782b0a83e7,0x34fb33f31fd21f6d,0x9c47f1f205b9ad02,0x5f8f40031b0e03f1,0x8f020ac39f867879,0x80f33605f8020380,0x23c1c129bd8ec451,0x31c29cf856837422]))
  | _ => 0

def samplesQ191 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x10938c0201894000,0x1d875a000404,0x18220e82820054a0,0x1840540022041a2c,0x2380041412029511,0x2242300637542922,0x88000ccee080014,0x42ae81200003d202,0x324001842815890e,0x384a11a12010299,0x1485292119432101,0x826c8c0080d05008,0x5704010070006340,0x800e09e500021440,0x520631025ac0990d,0x4d80d0a829050801]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x10a21142a2d61402,0x20208814400c921,0x8062ac2244100040,0x510102130220861,0x24803014420300,0x40d411008b012202,0x82109a224421,0x1008a02894020044,0xb660800082514e04,0xa2c0a100a8019111,0x42220c810005006a,0x40462a00caa82104,0x44a6010200208488,0x2422090403008055,0x4010912700681209,0x8930680248100106]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x30f2d60266fc4116,0x5a000983c8819c68,0x8c238cf65e000572,0x8037c0020128244,0x8314a0208c282251,0x79800088b8610804,0x22040f914e13401,0x12c412044d22904f,0xba440090c8d7cf1f,0xe3e5e090c834588c,0x40b6000a9b841242,0xa510a28098b8bb00,0x750559002401b503,0xe007194c06201111,0x88a006544f8bf0f,0xe024018764001010]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xec24520432542273,0xf354621881c48a3a,0xa414813c7442885a,0xa004a2cc8130e111,0x1829134388d80826,0x1d158929000a4284,0xe118b32101c2596a,0x451280aa7ec24d4,0xc08d1639c44076f1,0xfc7b5a412534a526,0x2b08c6cc42b8983c,0x640353b40c2a2940,0x8008f6748d109406,0x31407218aa14c006,0xac108448853f66f2,0x92542a5484b80008]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xa21cc6201808e8d0,0x5091412a88c00608,0x4c1c419412262432,0x8006586898c1108,0xf812254460213440,0x304e340301118,0x222a500221112016,0x1311304612091b2,0x418422d34804b17b,0x49274c8c40086822,0x4502026e04a6e85,0x9b1049c04171810,0x1918500da4183102,0x8314d04800260d20,0x908c00902111eda6,0x2609010981c60440]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x8804009410002041,0x51c601820742282,0x2141101004a8201,0xa28c029cc4890080,0x440a128260150822,0x80004450400890d8,0x9106290200100a08,0x890008c200840490,0x40914609052830e0,0x1c1a162404ca0040,0xa148925024004490,0x1880107625020442,0x8048045481540020,0x9404202289868a2,0x404690200740f0,0xb0600126a8280]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x900200d00000009,0x124a050000e0002,0x180000001c18004,0xe024020806016090,0x481008102848004,0x8600e8140406c060,0x5894080440080340,0xcc0200c000940c00,0x30c0814000080,0x1418106313c20640,0x9801511004308100,0x12084021000000e1,0x800004d003820810,0xc0060078082080,0x264062089a060050,0x10c2947012016020]))
  | _ => 0

def compactPerms191 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains191 : Array (Sig × Nat) := ([(subcube 4 0, 8)] : List (Sig × Nat)).toArray

def compactWords191 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount191 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath191 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive191 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords191 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs191 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords191 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords191 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket191 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP252 : Nat → Bits
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x210140001801,0xc18702a06099307,0x628007010000404,0xb8087d00858003d,0x3f100177c0077a0,0x2440a757c05863c6,0x204381800491002,0xf8067b2811740031,0xe023c986f07822fe,0x47bf0021df008dc,0xfc0bf0b8247b04c0,0x90e4ce8054c1bc0b,0xfd41eb03d260ff87,0x206f669a770a32f4])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0xbead2fff79ef,0x6ce7b03f6f51b0a6,0x940fff979fffe7e,0xeffa8fd572fb5f47,0x6fdf9034d18107aa,0x34e7171300500080,0xffbffc7f7fd7f27f,0x5a7e3fee33f59d85,0xfc34452eab802622,0x1439720f1df780c0,0xa009808ffeff51f3,0xf79fd78cd8c99c6c,0xcd738032dd80e006,0x2020def2ce8e6044]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xfdd48fffbed3,0xf4fb6e6697a54105,0xd280fffebf1f9fff,0x7b83f3f2fd3ba1f9,0xbbafe8472e1c1ef0,0x47006e0cc2082100,0xffdfffff99f87f86,0xac67e7f87cfe0ffb,0xe7407ac0347839df,0xe83e841039f80004,0xc00703f7fcf9fdf,0x9bede9eb14f1e280,0xbfc01f0c72700781,0x41ef77132b9210]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xf74b4ff1dffd,0xfb3cffb91e0a8649,0x1c00ffffffe7ef8f,0x9ffcfc3c7fcc01fe,0xc3f07fb80c1fe000,0x781981f0fc810008,0xffe77fbffeff8c07,0xff87f83fbf3ff1fe,0x187f8087c07fce0c,0xffc0081fc2000301,0xf0010ff7f3fe63,0xecf5fef3e31e00ff,0x3003e3cf806f0008,0x4100f7b9f4705108]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x48820310000,0x302700141e056489,0x1905000020060a08,0x1780781077a801c2,0xe80288c1f88a0,0x5ba15ea8c0a9ad28,0xd02402010b6e005,0x80184e82eb401ce,0x5c36810ff82d0e,0xfb84001de1f03725,0xcf4717250871b43,0x601d3183a8de40f4,0x3d42170c2def0789,0x5dd1927790b65f18])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xefbb7fffff3f,0x9f1f51defefd7f9b,0x272dfff7f6fe7ffd,0xf7857fdb8ffcfebf,0x147f87cbfc62f9a5,0x8be0feefc128ef66,0xff7efbf8f72ff1f9,0xf999dfe9cff4627f,0xe38bbf915ff821fe,0x3c7f1e0e5f07c3c,0x5c06707afd3f2fcc,0x707e3f942cc67d13,0x7d4c7f012fe01f81,0x1cdf32de31963eb0]))
  | _ => 0

def samplesQ252 : Nat → Bits
  | 2 => (BitVec.ofNat _ (limbs64 [0x210148000809,0x840850a804088203,0x208412404414008,0x4120852800881091,0x1100021108009101,0x440054050404104,0x28b0424400220125,0x5200100098c040,0x9248415002222140,0x510088400821000,0x4a24a14800090a,0x601114c0a1082b0,0x61a102024040220,0x6a1088448825040a]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x4152d0848311,0xc1581bc030a60751,0xb6bea36489c808d0,0x9805acad090928cd,0x982431032096ab45,0x802ae921f60dd94b,0xb4a6e44a53972668,0x2206b55082319453,0xa2ed45d855112b25,0x5488ca0068413544,0x50d8fc0bfa1e5151,0x549b948c8053966c,0x1c7030069ca24803,0x62b1daf2ca866040]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x22b7210c90e,0xb0990d0681abc3a,0xd3dd0a4605a1582,0x95b3190128e41414,0xc11312e911a1e923,0x21b821a353e086dd,0xea5d172511436c20,0x1a83831a66508ef0,0x86209c83322a9c63,0x315422c622a29bcf,0x254c24076f881c9e,0x8bcc61e190f0c229,0x3410994c56142330,0x965ef65032b9200]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x8b4b1076242,0x1430242a97559a4,0xe1772c89c10e1095,0x840a20d094758b0a,0x6485a94c72e52aaa,0x832a3825063e2ab2,0xd74128b2ec19240a,0x7780a16e8e401796,0x24110a21a191541a,0x48ce50339659455d,0xbf10904eb7e3e621,0xe824ae13b06a040f,0x1041a3c492a3508c,0x854277b974505100]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xfb77dbeedffb,0xefdafffbf5ee9f77,0xf7feebffadfd4fff,0xdf6fefefdbef7afd,0xdbedff776bdeffdd,0xb6fefdf7ff7fdbdf,0xbff7eeee73ffef7f,0xef57bff5eabddd7f,0xf3ef6fddfff77ff7,0xdffddfaf6bd73fd6,0xdafffeebfa9f5f5b,0xfebfb7deaedfdffe,0x3f7b7eaefdffcee3,0x7ffbdaffdab77fda])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x104480420050,0x60c0260100200044,0x50c20a1281200230,0x80c004491002240,0x8a08800200c0610,0x900608100c131000,0x1102888822108018,0xa00028c18004100a,0x61840208c4804214,0x800902148100400,0x1031920890150240,0x3032021004060d04,0x140640081e10883,0x482109a10902890]))
  | _ => 0

def compactPerms252 : Array (List Nat) := ([[], [84, 114], [67, 118], [67, 84, 98, 118], [83, 84, 114, 118], [83, 98]] : List (List Nat)).toArray

def compactDomains252 : Array (Sig × Nat) := ([(subcube 8 0, 6), (subcube 16 0, 6), (subcube 32 0, 6), (subcube 0 8, 5), (subcube 0 16, 5), (subcube 0 32, 5), (subcube 4 32, 4), (subcube 64 8, 4), (subcube 128 16, 4)] : List (Sig × Nat)).toArray

def compactWords252 : Nat → Nat
  | 0 => (limbs64 [0x5b8217fc,0x283ff1fe226a9cd0,0x49807ce53cbff803,0x1fe0ff04b89394c,0xc7ff07f81e5e055f,0xf07f80d9dfe0b434,0xb5906272b241be26,0x9198307c23107fc1,0xb8dff03ca0200024,0x80807adbfcdee092,0x988845662e01a00e,0x185aa1fe0157f9a8,0x9a3fe0ff07f8340b,0x32bd91a881108648,0xff0378bfc1fe0614,0x8529540ca428e615,0x24cb416edffbfd40,0x4c03401c21d8843f])
  | _ => 0

def compactCount252 (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 3
  | 5 => 4
  | 4 => 1
  | _ => 0

def compactPath252 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits compactWords252 (36 + 12*i) 12
  | 5 => let v := readCompactBits compactWords252 (475 + 13*i) 13
    (readCompactBits compactWords252 (451 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits compactWords252 (1029 + 12*i) 12
    (readCompactBits compactWords252 (1005 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive252 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords252 (0 + 6*i) 6
  | 6 => readCompactBits compactWords252 (72 + 7*i) 7
  | 5 => readCompactBits compactWords252 (527 + 8*i) 8
  | 4 => readCompactBits compactWords252 (1041 + 9*i) 9
  | _ => 0

def compactPoolIDs252 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords252 (30 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords252 (6 + 4*(v &&& 7)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords252 (165 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords252 (93 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 5 => let v := readCompactBits compactWords252 (559 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords252 (559 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 4 => let v := readCompactBits compactWords252 (1050 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords252 (1050 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket252 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits compactWords252 (192 + 3*(i % 4)) 3
    let off := ((i/4 + d) % 19)
    let v := readCompactBits compactWords252 (204 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits compactWords252 (567 + 5*(i % 7)) 5
    let off := ((i/7 + d) % 31)
    let v := readCompactBits compactWords252 (602 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords252 (1052 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits compactWords252 (1054 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

def samplesP189 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x2,0x13002108004f0202,0x200ec0d0d0a66400,0x80400a50058192,0x7084be1120a8880e,0x9016043b0f221f00,0xf980d739daa0e080,0x4080805e4d028801,0x96111520e13c20e7,0x980049fbc92484fd,0xf84231922e63e347,0xdf8aa219098c926a,0x510b50a6cf50e63,0x1e138b07c37a71bd,0xaef2691c91359bc])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x77,0x3defeffcffeff3e6,0x3dc27cf4987a77ff,0xf8cfffffdf83be7e,0xf3fdae14fcfffe0f,0xd6021bbb0fd21fb8,0x3ee0c329d0bffbfe,0xeafef6fe4f32f7e1,0xff2f15261ffffcef,0xc9e008f84764df3d,0xb842718671d3e303,0xdc009bfb3c7db87f,0xbda9bcaa63f70e60,0x11f7b1fc8f8009d,0xa675e70d3371194]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x10,0x64700810c1005199,0x1dc2538e9fce3c00,0x200d90000c0b1a7c,0x68290404b68c21c1,0x4351fbbdf1d1038,0x2e9ffcf9ffa10210,0x21801100034720b,0x81c804041ef662c5,0xfc3dec438569bfac,0xfef0c0a661dbffe7,0xdfeaa10026448094,0xb0c0682843bff843,0x1af9be43f7b79bf,0x7afc4074bad22ffc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x5f,0x678ffffbcd7cd67b,0x9c6fd182458723ff,0xeffdf8eb7fed7b97,0x6c9fb5fd36ab29df,0x8f95043cdc21d002,0xe99e34900a1feef7,0x7ffff959bdfe7e1b,0xd7d5f4fce7362e95,0x961d5543a923a4ec,0xc6e00e320e680044,0x38a3fbf2fadd3e5,0xebdeef698c8df983,0xde838b2433027120,0x8afed58858ec28]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7e,0xf35fff1fffdf099d,0xffbee24f96e62bff,0x77ffff3ffc7f9ff9,0xffe3fe0fe3ec81e1,0xf1fe3f7b070e0304,0x61fdcc8a5bff7bb,0xf7bbbffe430fb81f,0x81f8ff1ffbfff3e0,0xf81fe807c0fc3f8f,0xf839f180e0081fa3,0xcc600ffdc7ce8efa,0x74f3f37e53f33e63,0xf087c03f790883,0x7813a3e4ec923a54]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7b,0xde7ff9fff3f37f9b,0x63dfdf98fb8cd7ff,0xbfbfd7deffdfc1fe,0x782c5ff3bf9cfffe,0x3c35c483fb3d3c79,0xf981ff315a1fffdd,0xdfddcf17fcf5cbef,0xbedb0fe1fcfc6247,0x3c20effb9d0980f0,0x7fd680ff2ff3e044,0x138ab75efbd6f79e,0x97547d806c3cc05f,0x3f2f98e7c702713c,0x2ed659b3bc34da8]))
  | _ => 0

def samplesQ189 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x7d,0xecfdecf7efb8fffd,0xfdf3bfafafdbdf7a,0x7fcf7fcbbff9dfed,0x737aeff5dfa777ff,0x47ebdffff8fffcbf,0x3f7ff4ff3ddafcbd,0x6dbdb75ffe3fbfff,0x973effe6fd3fdff7,0x51ffbefb8ebf9bcf,0xbfc1bfeb5fbf9f7f,0xf3f5aedfcdfedaeb,0xc7baf5dfecfe3fff,0x1ff3f7e7cbfc7fdc,0x7eabb799ed3b7bbe])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x8,0xc211180900910409,0x42b4810946848843,0xa181205d00000a0,0x906428f80881090,0x9ce42c4141012153,0x41080dc40e14822e,0xc014603283628280,0x847402c4062e0c0,0x8c8812217c008820,0x12331400c48520a1,0x51271b224353040,0xb029940021834ac0,0x4816380d10a12089,0x5265c7042350084]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x10,0x64780c50611050b8,0x55c2078687ca1d2a,0x16092e4806890c09,0x302a4445caa12475,0x640592bd8446438,0x2a3b7459399a58a9,0x4c25954f942115a2,0x9220e944c82594f2,0x106632508e298287,0x90102aa520b954b,0x43b10ede893a5a29,0x72291d6849017b5,0x1a426143411403c0,0x262bb78945295002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x20,0x9870801530e1098c,0x62c40e1db838cfc0,0x529802c46c07c4b4,0x919802900b1418a1,0x60c6e88149cc2d54,0x4608ed2564f68c55,0x32b2a1228d693881,0x886151cc4460af0a,0x708a4c2500670c41,0x1344941614c923d9,0x15725bb7040c41c5,0xc9da27238d857283,0x48462b291026a80a,0x88afe548058e820]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x1,0xca040644420b2a0,0x44114a029115630,0x3043484004e0ca0c,0x2050207005050646,0x4001410c38745488,0x1a226032104a6410,0x2588170814051036,0x83382542090c1501,0x40452c1880160344,0x88c083090230854c,0x60a18e4dc1c088aa,0x4090604ec4501025,0x2e0854049181a04,0x3881a380ac023a10]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x4,0x2184072005081060,0x8c0020620043201c,0x105090201a82203,0x46134206460a202,0x20803181002c008,0x866000a81093180,0x9490a087010006a,0x600220038141031,0x221014803186192,0xc08841a120308c00,0xc08504485ac28612,0x60448840038002c,0x70100c0c3081164,0x9251018b39820508]))
  | _ => 0

def compactPerms189 : Array (List Nat) := ([[], [67, 112, 82]] : List (List Nat)).toArray

def compactDomains189 : Array (Sig × Nat) := ([(subcube 8 0, 5), (subcube 16 0, 5), (subcube 0 8, 5), (subcube 0 16, 5)] : List (Sig × Nat)).toArray

def compactWords189 : Nat → Nat
  | 0 => 0x81e3f
  | _ => 0

def compactCount189 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath189 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive189 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords189 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs189 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords189 (14 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords189 (6 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket189 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP63 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x4014a00,0x1244008ecac0804,0x8b0887770c004480,0x400c01204015111,0x63c40fda18942106,0xf51a65428fe78279,0x1022e38bc0103810,0x8034691c6903c68,0x86c00653043839,0xa0024b729b3a9147,0xf927c363e035fd46,0x7cbd0843a1b90762,0x101c21071cd5bb87,0x1c1e4ce70c1dd51b,0xecb18590dd5838fa])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0xee6feff,0xdfffe6f1ff6ebe60,0xfb5ca07ecfffefdf,0xddf3dfff1efd7d07,0xe8fe5fbe3fbf478e,0x953e0707f707da78,0x7c7243837fff7b7f,0xbd9f1f8fe1f8ff6f,0x47cce6deefd47e93,0xc0c74b63987e87f0,0xfb740363fc353d00,0x6439bf6f75f3bcf7,0x363e97541ef479c0,0x3c53ce879c61d41a,0xe43316dae7511c72]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xfd570ff,0xefaff97e27cfcf85,0x8820c7a303fff7e7,0xe67defff7f03d7f8,0xe73ee7cfd8cff900,0xe1d8607808f98237,0x28a008beffffbf,0xdee7e1f7ce7f3c79,0xf88f47e7f0ffb93c,0xbf0050361f08f84f,0x87c035e000c046,0x1884dfff9ffccf1e,0x7ddce767205f8f8f,0x1c3cf9039c0101,0x883bf7c587a2088]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x549503,0x8008807026030761,0x63b6f622fc000303,0x410c0360f20604,0xc03ec72c000b8500,0xc9fc4767ce85f236,0x6f2febfbc0a40024,0x41107007ef009,0x860807070ce03132,0xb0f844221e6cffee,0xf4f60231ff37ffce,0x7fbd000c59020806,0x45308666187f4ffc,0x20918ce7e27df71b,0xffb81267545947fa])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xf7999ff,0xb1ffdf1efeb3197f,0xe786961043ff7fff,0x7fcffcd2e4f74f1d,0x5bc5cf7fc7d3adf6,0xcd065d42ce847388,0x8f2601013ffcbdfd,0xefff5791369ff3ff,0x9e7fbf075f25b730,0x207a67689aa69126,0xf5363e681e350d00,0x20086ffffb3f0f6b,0xdb73bce6d8f50a74,0xcf91c0e6ec00100a,0xe411ebf3955cc412]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xdffcfff,0xff7cffe9ecbd67ff,0x7bbb7f67bfffdfbb,0xbfffff3be1fab2f7,0xf7ffbff8383cb771,0x7af9e7e78fe7a477,0x738deafaffb7fef6,0x7b7efe7fdff6fc88,0xa7b2d93f1fea796b,0xb0b88c9267797fcf,0xfcebc393e302f2ce,0x5fb5f8dee98b73e6,0xc5bd6bab1d0bf7bf,0x30ae0d67627de711,0x1ba8d5a55c897be8]))
  | _ => 0

def samplesQ63 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0xbfeb5f7,0xf6ebbe773b53fffd,0x7ef7fcacfb6ebf7b,0xfc7ecfd17bfd46ee,0x7bfaf7d5ff9bdff9,0xf4fdfd3d7f19ffce,0x6feddf7f34d7bbd7,0xe8fb4769f6efffe1,0xfff687fe53fbfef9,0x1ffdeb477bb26ef7,0xf9dfff55fff2fcf7,0xe3f8edc3bfb9f77b,0x95ff259fdcb5b5f7,0xdcfe7fe60fffd3f9,0xe3f1e598fdfc7afe])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x1190141,0x3004090400b1008f,0x24824e0112092092,0x26b40080420344,0x5103a58804508a0,0x4802b0a10a942081,0x9488a45007266211,0x49010a8aba81008,0x4c45621002802109,0x84401405a8038208,0x40e2920a89480549,0x9599241462a4c4,0x41a115032842948,0x2046448180c08554,0x441b144a63111042]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x2a8f04,0x325842a148a4103b,0x774f3814bf84c480,0x48ce3d0a08241e24,0x1049b0722a38299b,0xe4383a58fa491d1,0x9d5756b11ecc9632,0x98c132fb0ff0350b,0x18d16f402436012b,0x2250291f000e2010,0x27ce4ab044d90f8a,0x8f79fbe1a948e12,0x74d0671422d70e0d,0x610e9c09a5882111,0x2857be7c487a0008]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x549511,0xc049887020420369,0x32b4d420f92a0140,0xb8460750235c4440,0x51128384e119c521,0x80ecc5291b01d282,0x27418b4b3453a903,0x6838462902a35f21,0x297003c2400acaa0,0x509e8422a200a93,0x591c9414aa725416,0x61d0edc306a97179,0x108f209d44850013,0xd42636220c86c069,0x4141e598a9a43804]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x866680,0x4b80a2b041446620,0x187121ee2c745b00,0x8cc001cd0d28a039,0xe84c40840a80d613,0x325c0318b1209616,0x6150582ef89011cc,0xe34623131016c563,0x2112894624078ed4,0x5292c1a007f03161,0x281048444611f232,0x2b4266dbe919020b,0x8b618c25c4630231,0x4d30906e240a1a0a,0x30a0ebb1944cc410]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x2003020,0x8081201212408a00,0x808840420129,0x8010404122104008,0x2802410041801200,0xc080850080a0a,0x20200104200108c4,0x2a0000400240a0,0xa300002a11409a50,0x11890040019008e2,0x1000044020005010,0xa1086040a1005120,0x812400834c009090,0x4a0012202245220,0x1a0418014806aa0]))
  | _ => 0

def compactPerms63 : Array (List Nat) := ([[], [67, 16]] : List (List Nat)).toArray

def compactDomains63 : Array (Sig × Nat) := ([(subcube 4 0, 5), (subcube 8 0, 5), (subcube 16 0, 5), (subcube 1 8, 4), (subcube 2 16, 4)] : List (Sig × Nat)).toArray

def compactWords63 : Nat → Nat
  | 0 => 0x3ae3dc22d0888ff
  | _ => 0

def compactCount63 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | _ => 0

def compactPath63 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords63 (27 + 12*i) 12
  | _ => 0

def compactLive63 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords63 (0 + 6*i) 6
  | 5 => readCompactBits compactWords63 (39 + 7*i) 7
  | _ => 0

def compactPoolIDs63 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords63 (21 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords63 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords63 (46 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords63 (46 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket63 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords63 (48 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords63 (49 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6874245b93a40273,0xf164c0a0064fc00f,0x16000428c702801c,0x32a000a1f58e,0x30e7f786ed5681af,0x45fec33425032fa5,0xf26970a4a511eb93,0xe4862ef71f8d6c44,0x59f0899c7c4a6c00,0xc8ca50062009be37,0x4606780b6421ee80,0x61a83c018926801e,0x700dc2800a009e02,0x40209cc10d505a0,0x14d2a37c1de49342,0x8950a54615891044]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x80885120041e7dbc,0x8c000002be5001f0,0x29015bc110080000,0x4e4080007d04adfa,0xfadc8ec321c3fce0,0x49cae443ffe94217,0x8463c9b939ffa81d,0x3e750f0b617b2541,0x837a56172a841297,0xbc03aae02a7240e1,0x501045e880009992,0x3e6003f44c01893,0xc9f180071404005c,0x101d7220af020032,0x406396e38b0c25ec,0x408e44837420c218]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x1f098a81a12000c0,0xac0ddfdf8a03a00,0xc0ca000628001be1,0x1834c078209fedb,0x7feebbee74ef9ac5,0x66a8fde817d75c0,0xe5950e8fc02a96fa,0x789258a16cf3d470,0x1c4376f9b3349860,0x1304f5d8401c47ca,0xa942900086be1060,0x7400f7f07086c6e0,0x21ae3c00001a6000,0xe8e084134008407a,0xa5d7c7ec204b020d,0x4a33721880520083]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x7f6284e4ac3a300,0x207f225f0101c008,0x30000006d0001a,0x300802b80083cbf7,0xbf9faffddab55b3a,0xbe0975e4997268d8,0xdfea8f4b7ec4a661,0xaf53752e8a3cf393,0xad9c98a9cc5b0964,0xe47001038f800800,0x3ec52fc33958a07c,0x24231c1864f2663,0x885c027802001da2,0x50008080080803e,0xfa9d7ca1123561a1,0xb290aa60e8000864]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x907424146c58018c,0x211b3f00064801c0,0x28001a1100016000,0x23401400c537b6d,0xecef5b7dff6f6a53,0x5a753933447cbf7b,0xa957f509a1152ed,0xcb6ab6d8ef4d1ba8,0x57ef692273aa6398,0x30b6ae05d0163134,0x860180f75bc15100,0x1dd50a007021791d,0x8602010005e00005,0x121d02002820021d,0x3fb4db9a2e121492,0x5443887d13040310]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7f038a80041e7e43,0x52800002b81e0000,0x16c14400e80a01e0,0x4d80bc007206d3f5,0xc5336d3bafbbf71c,0xe9b51a8bfa969216,0x7962b64679ee551c,0xd188c9f491765abe,0x2285a05755718297,0x430155182a6d80d6,0xa9e845140001666d,0x8219c03ebb18188c,0x3601bc071804e058,0x80281d09004040d,0xdb697914448bcc10,0xa12d1484e28ac080]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xc082d520db61801b,0xd7040ddd41b01407,0x34a02a01f49e06,0xb00b401a802a3e22,0x5f115016d7f86416,0xb1908cf95e808529,0x259ee170062b7d66,0x76d8017748087cf,0xe803ffe680856508,0xbcd0a2395818f08,0x50bb9208c69e0d1f,0x8808c9ce06592100,0x1a240f8e01b03a0,0xe10004050051b985,0x292a041bc0c0780f,0x342c091b0c013c23]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x200953ff3081dc24,0xcbbf22041a02e30,0xc10ea1d410256401,0x807401450153041d,0x8378f4f91a1cb5e9,0xb607720c228fd8ee,0x1a1c10bfc7d40982,0x10bdf3489282a83f,0xf63c07488000946b,0x43800fc55e27009,0x13c2a3439660283,0xfc37060009b0c760,0x5e504100e1e10001,0x2e07022472a7a43,0xc60c2840f1308a70,0xfc053a00b742508]))
  | _ => 0

def samplesQ255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x48008405120402a8,0x2ca0108201001008,0xe900040511020404,0x188814282853488,0x10e0138260428083,0x4404c010050122a4,0x320160a4a5100012,0x6486064106814004,0x51b0009430046c00,0xd000500220147602,0x4000c00324000c00,0x61a002000006809e,0x500001800a050202,0x12028a25108b0460,0x452834c0d601340,0x940254211090004]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x2211008c5115018,0x24280c126284900c,0xc088530831014,0x80c220ca4d2,0x1a4482c200828080,0x14a044113484204,0x8042482830a92810,0x6210a03006a2541,0x11a560528040a22,0xac002860081040a3,0x1000402084008820,0x242009844808090,0x4085002280044952,0xc00822223e010132,0x430663890c21ac,0xa440244008018]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x81198400940042d0,0x806480850419888,0x48081d8591028086,0x80910a58e2cdbcda,0x3eee93e670c78041,0x628504802c24c0,0xa4110c88002084c8,0x689008204cc25410,0xc4304b18a042860,0xb600b4c0801c5302,0x8b02c0010e0c0860,0x328017b00402c294,0xc18c100008884240,0x8944840b2480407a,0x24d787ec20490009,0x4813621000100082]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x2ac109a20400445,0x4d00142a08abb0,0x125848b0022401a2,0x56371a28200ac957,0xaf1fac7d18b55920,0x3209218498524850,0x4ce803031ac0a601,0xb11712c003cb212,0x880c1828ce520024,0x2450244984a00104,0x2ec40d4418582030,0x9200309117082e21,0x8a940a3320000c25,0xd0824884100c21e,0xf28d7ca1121540a1,0x92908220e8000840]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xe192210520000124,0x43427009105a0c81,0x48f164120f182283,0x2d1324084a15b29,0xe4ab5934ff6d6a42,0x5830003204348d19,0x2943550801052ed,0x814a14c8e90500a0,0x46c5290212ba2114,0x10361600c0069314,0xa8880d548087004,0x38815a0230233b04,0x8002130806ca8004,0x104700148030920d,0x3fb4d19826021402,0x5441887d12040200]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x30060a2208a8a901,0x9301032408320213,0x250e0100a5c6a28,0x160410210d024325,0xc1116c198f38771c,0x88911a8a68809002,0x4120924248461104,0x9000809491100a2a,0x2200804041728195,0x14030802a18044,0xe809440041620c,0x8011c80691082920,0x22108c115420a488,0x202010d080240885,0xdb2878104082cc10,0xa0241084a2824000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x1000230049399800,0xc000250100a24001,0x2224048182200,0x40014100220,0x4000400087082014,0x8180086942800109,0x1068010000b4820,0x680012300001c9,0xe30200210110,0x18d020010008800,0x9120800824106,0x9484200500100,0x200008c0422198,0x600100000a141181,0x920001280802806,0x242c080904001421]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x80008b002c42400,0x108002a001000250,0x600000800040060,0x3c0440a000020004,0x110240900101428,0x2604720020031022,0x1808000547040102,0x1004e10002008804,0xb020004800401008,0x1c01e00008,0x50290001600081,0x8404000009080060,0x650448030210021,0x6201840410a0c00,0xc008280050308250,0x380118009602100]))
  | _ => 0

def compactPerms255 : Array (List Nat) := ([[], [67, 16, 118]] : List (List Nat)).toArray

def compactDomains255 : Array (Sig × Nat) := ([(subcube 4 0, 11), (subcube 8 0, 11), (subcube 16 0, 11), (subcube 32 0, 11), (subcube 1 0, 10), (subcube 2 0, 10), (subcube 64 0, 9), (subcube 128 0, 9), (subcube 0 8, 8), (subcube 0 16, 8), (subcube 0 1, 8), (subcube 0 2, 8), (subcube 3 0, 8), (subcube 68 0, 8), (subcube 72 0, 8), (subcube 66 0, 7), (subcube 129 0, 7), (subcube 192 0, 7), (subcube 128 16, 7), (subcube 8 1, 7), (subcube 64 1, 7), (subcube 128 2, 7), (subcube 130 0, 6), (subcube 65 8, 6), (subcube 160 2, 6), (subcube 193 0, 4)] : List (Sig × Nat)).toArray

def compactWords255 : Nat → Nat
  | 0 => (limbs64 [0x5439e080c1010051,0xd05a3427ce722818,0x20200585a21284fa,0x739c112a10383040,0x4005174684f9c19c,0x1f2edceb6386cd1f,0xf41a157345a8a9c,0x18a4f08e10976e75,0xb1c36d0d157229a9,0xfa3427ce421c2117,0x50e9c326cd386ed,0x9a0522d681f742a7,0x512e1e7a16e75b1b,0x6868e3542e859f70,0x28b4fa33a817a654,0x207281a8d042ea7c,0xe148450304005850,0x9468539ce0ba12e0,0xc1001614094a34e8,0x4f9c28bbb1eddb34,0x162909d38d4d9aa3,0x4274f0815c1f2864,0xd1a06e753745c9b,0xa36209d1a7427380,0xa0c1010028215167,0xe8d09f39c144074e,0x1b342a8cfa138615,0x80302862a128d041,0x3e738161c1820030,0x95a3427ce722aff,0xbfeffbffffb7ef7b,0xeeffbfbbfbfedfbb,0xeffeffffeffffbfe,0xffbfefffffffffff,0xfffaffbfffffdef7,0xbffffff6ffea0dd4,0x7a804d008a00141,0x428185020a001403,0x263e507ca0b94132,0x803cc7698ed31da0,0x3bd077a01541ea80,0xa8c7498ea09d213a,0x4075a0e941d2132d,0x35a06b404a63942,0x62a0d18f04d00c98,0xe84c80c80218f931,0xfe1caffe0bc7fe10,0x57fe037ffe1fe1fe,0x1becca58a3fe0b69,0xfe1b132ddb2a69a6,0x13f43ecbe539e416,0x38f3c7bc00c41014,0xc4ef3f5dfb471882,0x290c7effdcdea23,0x1040521fbcfd37ed,0x18e1050622779bf6,0x8a6a9c62080862f7,0x9ede96f89c62080b,0xdff37a218e3100a1,0x2779bf9b4abd4f43,0xc41033bcde885ff,0xffffffffffffffff,0x8c74c70c78264268,0x6406401c1d888ff])
  | 1 => (limbs64 [0x283a03283200a824,0x13280c63a80263a6,0x3a13213203203a13,0x4b9dff001b0e5807,0xf80d40dfe03fc04a,0x8daa2434d3fc0258,0x5084ffe03fc06f99,0xff005e9bfc016b62,0x21ffe025861688ff,0x1cc63e087f80ff0,0x22247dc7f800a2f,0xfe03fc04cad2e458,0x9082d909bcb840d2,0x610e0923b66ffe0,0x159723c7ff000b19,0x167f80dd638a45a,0xd4ef8a1b4ad2af1e,0x27f80673dfe034d8,0x640264501e0f6978,0xa95bb161b0134d5a,0xbd16558a6db83f1b,0x9a382c24e40b6f45,0xe27f0e38d24e6213,0x377aacd4cffab508,0x46b01863108a2040,0x5a80040001183e0,0xffc1ef83bf17392e,0x2a5bc436906912cd,0xa1938306a5e56b73,0x9603ab38505a9a55,0x1f7a210401c7940e,0x2b99772d2c4f508a,0x68fae1bde305c495,0x7e90d9e13b81960,0x1ad000f03040400b,0xa28251a74294f9c,0x54a0302002821411,0xd1f0f468529f3858,0x40608080165429ea,0x3429cf9c1c503040,0x4005164421e29469,0xd09f385172074e1a,0x2a7c21ba74684f9c,0x788940e768539f4a,0x715281e8d3a13845,0x22a383d1a7427d22,0xa34203040400b0a1,0xa8d03d3e9ce0e28f,0x6a3405539f38a94,0xb4684f9ce48940a,0xc10100e45040d46,0x84fa538a863054ed,0x9f4a73928483153,0x8e6889a53e7142e1,0xc182020028aa3427,0xce7219cd1a13e706,0x2a3dbb66ad0586a4,0x74e1b34e0f210f46,0x8059f38a15721838,0x5a2fe8119f490ce2,0xae4e9c36682076ed,0x9ab47ee4595a07a7,0x519e3ca05720c101,0x2820fa3427d29c])
  | 2 => (limbs64 [0xc194b1920d1ad2ee,0xdfb62ff07f83fc1f,0xe0ff07f80e913808,0x58cebbfc14ade50a,0x22aa497f5ff02127,0xfc116780a7f83fc0,0x18423c5ed5a12639,0x46120b8db6da5028,0x14caa50cf7bb79ef,0x9efaf7af7ee7ae7e,0xb7ef5af75a46f50e,0x6a25d44ca827518e,0xa21d44098e109c2a,0x3c63e81a03293a13,0x203290c63a032902,0x63a13280a80263a1,0x3e81a03213681a03,0x5bb186d53adfe07f,0x80d928a94033732a,0xecffbc3fe07f80f8,0xbac0dfe00c20901b,0x782f0581babc17f8,0xb48c8c9ad3843d7,0x3d711649ff8022a,0x7f81244ea1dfe06c,0x9e4c86366e7fb46,0xda07f81c297f80e4,0x6c799862d1401400,0x228438609001014,0x51c4dcc95442c1e3,0xbe35ab32b0cac3a8,0x9a72a4a22e9c596e,0x10e0ad855005137d,0xcdbdd5b4384915cd,0xddc5b27c33ca8418,0x5850f0282298f8aa,0xac25cb8dd5b8a5b5,0x8ba7d09f9cdc5b9,0x83835cdb1d0ad0c,0x30a5c81dc015b80d,0xb00508a02430e4ea,0x5062805a98502c,0x48a5ca7dddc045b5,0xa0bceb99c0fb6c,0xe908b8e4ed005022,0x834850bb828dca85,0xc27099d5b299c502,0xab828dca82729dc5,0xb1c5022a8a8275b1,0xc0422dcdc2989aa9,0xd28a71c04285cdb2,0xa89a9dc2aa8a8273,0x85cdc5b1c5021ba0,0xac40427dcdc5b50d,0x4efbefbff57fbfe,0x7f3feffeff9efeff,0xfedfffefbdf7bef7,0xdefbde7ba6921e91,0x9a80aa6392900263,0xca93c290da13be91,0x8a638a138a93d213,0xd463d263d413d213,0xd2133691e83a0368,0x1a03680213463a03])
  | 3 => (limbs64 [0x48a70ffc328ff1,0xfe1b8bdaff1fe203,0x1cf2e7973da886b2,0x3ac9a46a02a0098e,0xa8e84da0680ca831,0x8fa0680cfec3f9d9])
  | _ => 0

def compactCount255 (k : Nat) : Nat := match k with
  | 12 => 1
  | 11 => 8
  | 10 => 37
  | 9 => 20
  | 8 => 11
  | 7 => 3
  | _ => 0

def compactPath255 (k : Nat) (i : Nat) : Nat := match k with
  | 12 => 0
  | 11 => readCompactBits compactWords255 (32 + 12*i) 12
  | 10 => let v := readCompactBits compactWords255 (1261 + 15*i) 15
    (readCompactBits compactWords255 (1165 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 9 => let v := readCompactBits compactWords255 (8287 + 16*i) 16
    (readCompactBits compactWords255 (7999 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 8 => let v := readCompactBits compactWords255 (11451 + 15*i) 15
    (readCompactBits compactWords255 (11199 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 7 => let v := readCompactBits compactWords255 (12465 + 14*i) 14
    (readCompactBits compactWords255 (12321 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | _ => 0

def compactLive255 (k : Nat) (i : Nat) : Nat := match k with
  | 12 => readCompactBits compactWords255 (0 + 8*i) 8
  | 11 => readCompactBits compactWords255 (128 + 9*i) 9
  | 10 => readCompactBits compactWords255 (1816 + 10*i) 10
  | 9 => readCompactBits compactWords255 (8607 + 11*i) 11
  | 8 => readCompactBits compactWords255 (11616 + 12*i) 12
  | 7 => readCompactBits compactWords255 (12507 + 13*i) 13
  | _ => 0

def compactPoolIDs255 (k : Nat) (i : Nat) : List Nat := match k with
  | 12 => let v := readCompactBits compactWords255 (26 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords255 (8 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 11 => let v := readCompactBits compactWords255 (795 + 12*i) 12
    let n := v >>> 7
    let bits := readCompactBits compactWords255 (200 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 10 => let v := readCompactBits compactWords255 (5994 + 15*i) 15
    let n := v >>> 10
    let bits := readCompactBits compactWords255 (2186 + 7*(v &&& 1023)) (7*n)
    compactIDsFromBits bits 7 n
  | 9 => let v := readCompactBits compactWords255 (10195 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords255 (8827 + 8*(v &&& 255)) (8*n)
    compactIDsFromBits bits 8 n
  | 8 => let v := readCompactBits compactWords255 (11829 + 5*i) 5
    let n := v >>> 4
    let bits := readCompactBits compactWords255 (11748 + 9*(v &&& 15)) (9*n)
    compactIDsFromBits bits 9 n
  | 7 => let v := readCompactBits compactWords255 (12546 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords255 (12546 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket255 (k : Nat) (i : Nat) : List Nat := match k with
  | 11 => let d := readCompactBits compactWords255 (891 + 2*(i % 5)) 2
    let off := ((i/5 + d) % 22)
    let v := readCompactBits compactWords255 (901 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 10 => let d := readCompactBits compactWords255 (6549 + 5*(i % 23)) 5
    let off := ((i/23 + d) % 89)
    let v := readCompactBits compactWords255 (6664 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 9 => let d := readCompactBits compactWords255 (10435 + 6*(i % 13)) 6
    let off := ((i/13 + d) % 49)
    let v := readCompactBits compactWords255 (10513 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 8 => let d := readCompactBits compactWords255 (11884 + 3*(i % 7)) 3
    let off := ((i/7 + d) % 32)
    let v := readCompactBits compactWords255 (11905 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits compactWords255 (12552 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords255 (12554 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid146 : CompactGrid := (146, 3, samplesP146, samplesQ146)
def tab146 : CompactTable := (compactCount146, compactPath146, compactLive146, compactPoolIDs146, compactBucket146)
def check146 (k : Nat) := compactNode grid146 tab146 compactDomains146 compactPerms146 k
def sliceSpecs146 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains146 : ∀ d ∈ compactDomains146, Slice true (vars 146) (graphGoal 146) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs146)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs146 : properPairs (graphGoal 146) (asRow samplesP146) (asRow samplesQ146) :=
  compactPairs (g := grid146) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos146 : ∀ p ∈ compactPerms146, autoOK (graphGoal 146) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c146k3p0 : chartBlock (check146 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev146k3 : chartBlock (check146 3) 0 1 = true :=
  c146k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded146 : Impossible true (graphGoal 146) 3 (vars 146).toFinset := by
  apply compactRoot (g := grid146) (t := tab146) (dom := compactDomains146) (perms := compactPerms146) pairs146 domains146 autos146
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev146k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound146 : Lower true (vars 146) (graphGoal 146) 4 :=
  plain_low (hints := 268501056) (by decide +kernel) excluded146

def grid210 : CompactGrid := (210, 4, samplesP210, samplesQ210)
def tab210 : CompactTable := (compactCount210, compactPath210, compactLive210, compactPoolIDs210, compactBucket210)
def check210 (k : Nat) := compactNode grid210 tab210 compactDomains210 compactPerms210 k
def sliceSpecs210 : List SliceSpec := [(64, 0, 146, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains210 : ∀ d ∈ compactDomains210, Slice true (vars 210) (graphGoal 210) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(146, 4)]) (specs := sliceSpecs210)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound146
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs210 : properPairs (graphGoal 210) (asRow samplesP210) (asRow samplesQ210) :=
  compactPairs (g := grid210) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos210 : ∀ p ∈ compactPerms210, autoOK (graphGoal 210) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c210k4p0 : chartBlock (check210 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev210k4 : chartBlock (check210 4) 0 1 = true :=
  c210k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded210 : Impossible true (graphGoal 210) 4 (vars 210).toFinset := by
  apply compactRoot (g := grid210) (t := tab210) (dom := compactDomains210) (perms := compactPerms210) pairs210 domains210 autos210
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev210k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound210 : Lower true (vars 210) (graphGoal 210) 5 :=
  plain_low (hints := 385941568) (by decide +kernel) excluded210

def grid216 : CompactGrid := (216, 3, samplesP216, samplesQ216)
def tab216 : CompactTable := (compactCount216, compactPath216, compactLive216, compactPoolIDs216, compactBucket216)
def check216 (k : Nat) := compactNode grid216 tab216 compactDomains216 compactPerms216 k
def sliceSpecs216 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains216 : ∀ d ∈ compactDomains216, Slice true (vars 216) (graphGoal 216) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs216)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs216 : properPairs (graphGoal 216) (asRow samplesP216) (asRow samplesQ216) :=
  compactPairs (g := grid216) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos216 : ∀ p ∈ compactPerms216, autoOK (graphGoal 216) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c216k3p0 : chartBlock (check216 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev216k3 : chartBlock (check216 3) 0 1 = true :=
  c216k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded216 : Impossible true (graphGoal 216) 3 (vars 216).toFinset := by
  apply compactRoot (g := grid216) (t := tab216) (dom := compactDomains216) (perms := compactPerms216) pairs216 domains216 autos216
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev216k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound216 : Lower true (vars 216) (graphGoal 216) 4 :=
  plain_low (hints := 1124556800) (by decide +kernel) excluded216

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound202 : Lower true (vars 202) (graphGoal 202) 4 :=
  carry_of (old := 202) (rep := 216) (swaps := [65]) (by decide +kernel) bound216

def grid218 : CompactGrid := (218, 6, samplesP218, samplesQ218)
def tab218 : CompactTable := (compactCount218, compactPath218, compactLive218, compactPoolIDs218, compactBucket218)
def check218 (k : Nat) := compactNode grid218 tab218 compactDomains218 compactPerms218 k
def sliceSpecs218 : List SliceSpec := [(8, 0, 210, 0, 0, 5, 5), (0, 8, 146, 64, 251658240, 5, 4), (2, 0, 216, 0, 0, 4, 4), (16, 0, 202, 0, 0, 4, 4), (64, 8, 146, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains218 : ∀ d ∈ compactDomains218, Slice true (vars 218) (graphGoal 218) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(210, 5), (146, 4), (216, 4), (202, 4)]) (specs := sliceSpecs218)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound210
    · exact bound146
    · exact bound216
    · exact bound202
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs218 : properPairs (graphGoal 218) (asRow samplesP218) (asRow samplesQ218) :=
  compactPairs (g := grid218) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos218 : ∀ p ∈ compactPerms218, autoOK (graphGoal 218) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c218k4p0 : chartBlock (check218 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev218k4 : chartBlock (check218 4) 0 1 = true :=
  c218k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c218k5p0 : chartBlock (check218 5) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev218k5 : chartBlock (check218 5) 0 3 = true :=
  c218k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c218k6p0 : chartBlock (check218 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev218k6 : chartBlock (check218 6) 0 1 = true :=
  c218k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded218 : Impossible true (graphGoal 218) 6 (vars 218).toFinset := by
  apply compactRoot (g := grid218) (t := tab218) (dom := compactDomains218) (perms := compactPerms218) pairs218 domains218 autos218
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev218k4
    · exact lev218k5
    · exact lev218k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound218 : Lower true (vars 218) (graphGoal 218) 7 :=
  plain_low (hints := 318857280) (by decide +kernel) excluded218

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound217 : Lower true (vars 217) (graphGoal 217) 7 :=
  carry_of (old := 217) (rep := 218) (swaps := [16, 67, 118]) (by decide +kernel) bound218

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound211 : Lower true (vars 211) (graphGoal 211) 7 :=
  carry_of (old := 211) (rep := 218) (swaps := [48]) (by decide +kernel) bound218

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound203 : Lower true (vars 203) (graphGoal 203) 7 :=
  carry_of (old := 203) (rep := 218) (swaps := [64, 49, 118]) (by decide +kernel) bound218

def grid155 : CompactGrid := (155, 5, samplesP155, samplesQ155)
def tab155 : CompactTable := (compactCount155, compactPath155, compactLive155, compactPoolIDs155, compactBucket155)
def check155 (k : Nat) := compactNode grid155 tab155 compactDomains155 compactPerms155 k
def sliceSpecs155 : List SliceSpec := [(0, 1, 146, 8, 61440, 5, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains155 : ∀ d ∈ compactDomains155, Slice true (vars 155) (graphGoal 155) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(146, 4)]) (specs := sliceSpecs155)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound146
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs155 : properPairs (graphGoal 155) (asRow samplesP155) (asRow samplesQ155) :=
  compactPairs (g := grid155) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos155 : ∀ p ∈ compactPerms155, autoOK (graphGoal 155) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c155k5p0 : chartBlock (check155 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev155k5 : chartBlock (check155 5) 0 1 = true :=
  c155k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded155 : Impossible true (graphGoal 155) 5 (vars 155).toFinset := by
  apply compactRoot (g := grid155) (t := tab155) (dom := compactDomains155) (perms := compactPerms155) pairs155 domains155 autos155
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev155k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound155 : Lower true (vars 155) (graphGoal 155) 6 :=
  plain_low (hints := 268501059) (by decide +kernel) excluded155

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound91 : Lower true (vars 91) (graphGoal 91) 6 :=
  carry_of (old := 91) (rep := 155) (swaps := [16, 67, 118]) (by decide +kernel) bound155

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound73 : Lower true (vars 73) (graphGoal 73) 4 :=
  carry_of (old := 73) (rep := 146) (swaps := [16, 67, 118]) (by decide +kernel) bound146

def grid219 : CompactGrid := (219, 9, samplesP219, samplesQ219)
def tab219 : CompactTable := (compactCount219, compactPath219, compactLive219, compactPoolIDs219, compactBucket219)
def check219 (k : Nat) := compactNode grid219 tab219 compactDomains219 compactPerms219 k
def sliceSpecs219 : List SliceSpec := [(1, 0, 218, 0, 0, 7, 7), (2, 0, 217, 0, 0, 7, 7), (8, 0, 211, 0, 0, 7, 7), (16, 0, 203, 0, 0, 7, 7), (64, 0, 155, 0, 0, 6, 6), (128, 0, 91, 0, 0, 6, 6), (0, 1, 146, 72, 251719680, 6, 4), (0, 2, 73, 144, 4027514880, 6, 4), (0, 8, 146, 65, 251658255, 6, 4), (0, 16, 73, 130, 4026532080, 6, 4), (9, 0, 210, 0, 0, 5, 5), (1, 8, 146, 64, 251658240, 5, 4), (2, 16, 73, 128, 4026531840, 5, 4), (64, 1, 146, 8, 61440, 5, 4), (64, 8, 146, 1, 15, 5, 4), (128, 2, 73, 16, 983040, 5, 4), (128, 16, 73, 2, 240, 5, 4), (65, 8, 146, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains219 : ∀ d ∈ compactDomains219, Slice true (vars 219) (graphGoal 219) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(218, 7), (217, 7), (211, 7), (203, 7), (155, 6), (91, 6), (146, 4), (73, 4), (210, 5)]) (specs := sliceSpecs219)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound218
    · exact bound217
    · exact bound211
    · exact bound203
    · exact bound155
    · exact bound91
    · exact bound146
    · exact bound73
    · exact bound210
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs219 : properPairs (graphGoal 219) (asRow samplesP219) (asRow samplesQ219) :=
  compactPairs (g := grid219) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos219 : ∀ p ∈ compactPerms219, autoOK (graphGoal 219) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k5p0 : chartBlock (check219 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k5 : chartBlock (check219 5) 0 1 = true :=
  c219k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k6p0 : chartBlock (check219 6) 0 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k6 : chartBlock (check219 6) 0 4 = true :=
  c219k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k7p0 : chartBlock (check219 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k7p1 : chartBlock (check219 7) 8 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k7 : chartBlock (check219 7) 0 11 = true :=
  (chartBlock_join (a := 8) (b := 3) c219k7p0 c219k7p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k8p0 : chartBlock (check219 8) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k8p1 : chartBlock (check219 8) 8 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k8 : chartBlock (check219 8) 0 9 = true :=
  (chartBlock_join (a := 8) (b := 1) c219k8p0 c219k8p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k9p0 : chartBlock (check219 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k9 : chartBlock (check219 9) 0 1 = true :=
  c219k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded219 : Impossible true (graphGoal 219) 9 (vars 219).toFinset := by
  apply compactRoot (g := grid219) (t := tab219) (dom := compactDomains219) (perms := compactPerms219) pairs219 domains219 autos219
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev219k5
    · exact lev219k6
    · exact lev219k7
    · exact lev219k8
    · exact lev219k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound219 : Lower true (vars 219) (graphGoal 219) 10 :=
  plain_low (hints := 268501059) (by decide +kernel) excluded219

def grid251 : CompactGrid := (251, 10, samplesP251, samplesQ251)
def tab251 : CompactTable := (compactCount251, compactPath251, compactLive251, compactPoolIDs251, compactBucket251)
def check251 (k : Nat) := compactNode grid251 tab251 compactDomains251 compactPerms251 k
def sliceSpecs251 : List SliceSpec := [(32, 0, 219, 0, 0, 10, 10)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains251 : ∀ d ∈ compactDomains251, Slice true (vars 251) (graphGoal 251) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(219, 10)]) (specs := sliceSpecs251)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound219
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs251 : properPairs (graphGoal 251) (asRow samplesP251) (asRow samplesQ251) :=
  compactPairs (g := grid251) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos251 : ∀ p ∈ compactPerms251, autoOK (graphGoal 251) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c251k10p0 : chartBlock (check251 10) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev251k10 : chartBlock (check251 10) 0 1 = true :=
  c251k10p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded251 : Impossible true (graphGoal 251) 10 (vars 251).toFinset := by
  apply compactRoot (g := grid251) (t := tab251) (dom := compactDomains251) (perms := compactPerms251) pairs251 domains251 autos251
  · intro k hk
    change k ≤ 10 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev251k10
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound251 : Lower true (vars 251) (graphGoal 251) 11 :=
  plain_low (hints := 268501059) (by decide +kernel) excluded251

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound212 : Lower true (vars 212) (graphGoal 212) 5 :=
  carry_of (old := 212) (rep := 210) (swaps := [33, 100]) (by decide +kernel) bound210

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound198 : Lower true (vars 198) (graphGoal 198) 5 :=
  carry_of (old := 198) (rep := 210) (swaps := [97, 66]) (by decide +kernel) bound210

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound150 : Lower true (vars 150) (graphGoal 150) 5 :=
  carry_of (old := 150) (rep := 210) (swaps := [98]) (by decide +kernel) bound210

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound196 : Lower true (vars 196) (graphGoal 196) 4 :=
  carry_of (old := 196) (rep := 146) (swaps := [33, 100]) (by decide +kernel) bound146

def grid214 : CompactGrid := (214, 7, samplesP214, samplesQ214)
def tab214 : CompactTable := (compactCount214, compactPath214, compactLive214, compactPoolIDs214, compactBucket214)
def check214 (k : Nat) := compactNode grid214 tab214 compactDomains214 compactPerms214 k
def sliceSpecs214 : List SliceSpec := [(2, 0, 212, 0, 0, 5, 5), (4, 0, 210, 0, 0, 5, 5), (16, 0, 198, 0, 0, 5, 5), (64, 0, 150, 0, 0, 5, 5), (18, 0, 196, 0, 0, 4, 4), (68, 0, 146, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains214 : ∀ d ∈ compactDomains214, Slice true (vars 214) (graphGoal 214) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(212, 5), (210, 5), (198, 5), (150, 5), (196, 4), (146, 4)]) (specs := sliceSpecs214)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound212
    · exact bound210
    · exact bound198
    · exact bound150
    · exact bound196
    · exact bound146
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs214 : properPairs (graphGoal 214) (asRow samplesP214) (asRow samplesQ214) :=
  compactPairs (g := grid214) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos214 : ∀ p ∈ compactPerms214, autoOK (graphGoal 214) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c214k4p0 : chartBlock (check214 4) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev214k4 : chartBlock (check214 4) 0 3 = true :=
  c214k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c214k5p0 : chartBlock (check214 5) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c214k5p1 : chartBlock (check214 5) 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev214k5 : chartBlock (check214 5) 0 10 = true :=
  (chartBlock_join (a := 8) (b := 2) c214k5p0 c214k5p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c214k6p0 : chartBlock (check214 6) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev214k6 : chartBlock (check214 6) 0 3 = true :=
  c214k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c214k7p0 : chartBlock (check214 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev214k7 : chartBlock (check214 7) 0 1 = true :=
  c214k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded214 : Impossible true (graphGoal 214) 7 (vars 214).toFinset := by
  apply compactRoot (g := grid214) (t := tab214) (dom := compactDomains214) (perms := compactPerms214) pairs214 domains214 autos214
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev214k4
    · exact lev214k5
    · exact lev214k6
    · exact lev214k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound214 : Lower true (vars 214) (graphGoal 214) 8 :=
  plain_low (hints := 302057024) (by decide +kernel) excluded214

def grid246 : CompactGrid := (246, 8, samplesP246, samplesQ246)
def tab246 : CompactTable := (compactCount246, compactPath246, compactLive246, compactPoolIDs246, compactBucket246)
def check246 (k : Nat) := compactNode grid246 tab246 compactDomains246 compactPerms246 k
def sliceSpecs246 : List SliceSpec := [(32, 0, 214, 0, 0, 8, 8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains246 : ∀ d ∈ compactDomains246, Slice true (vars 246) (graphGoal 246) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(214, 8)]) (specs := sliceSpecs246)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound214
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs246 : properPairs (graphGoal 246) (asRow samplesP246) (asRow samplesQ246) :=
  compactPairs (g := grid246) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos246 : ∀ p ∈ compactPerms246, autoOK (graphGoal 246) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c246k8p0 : chartBlock (check246 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev246k8 : chartBlock (check246 8) 0 1 = true :=
  c246k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded246 : Impossible true (graphGoal 246) 8 (vars 246).toFinset := by
  apply compactRoot (g := grid246) (t := tab246) (dom := compactDomains246) (perms := compactPerms246) pairs246 domains246 autos246
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev246k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound246 : Lower true (vars 246) (graphGoal 246) 9 :=
  plain_low (hints := 303105344) (by decide +kernel) excluded246

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound226 : Lower true (vars 226) (graphGoal 226) 4 :=
  carry_of (old := 226) (rep := 216) (swaps := [97, 83, 100, 67]) (by decide +kernel) bound216

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound225 : Lower true (vars 225) (graphGoal 225) 4 :=
  carry_of (old := 225) (rep := 216) (swaps := [112, 84, 115]) (by decide +kernel) bound216

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound195 : Lower true (vars 195) (graphGoal 195) 4 :=
  carry_of (old := 195) (rep := 216) (swaps := [48, 65]) (by decide +kernel) bound216

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound163 : Lower true (vars 163) (graphGoal 163) 4 :=
  carry_of (old := 163) (rep := 216) (swaps := [48, 113, 101, 116]) (by decide +kernel) bound216

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound99 : Lower true (vars 99) (graphGoal 99) 4 :=
  carry_of (old := 99) (rep := 216) (swaps := [96, 65, 117, 99]) (by decide +kernel) bound216

def grid227 : CompactGrid := (227, 6, samplesP227, samplesQ227)
def tab227 : CompactTable := (compactCount227, compactPath227, compactLive227, compactPoolIDs227, compactBucket227)
def check227 (k : Nat) := compactNode grid227 tab227 compactDomains227 compactPerms227 k
def sliceSpecs227 : List SliceSpec := [(1, 0, 226, 0, 0, 4, 4), (2, 0, 225, 0, 0, 4, 4), (32, 0, 195, 0, 0, 4, 4), (64, 0, 163, 0, 0, 4, 4), (128, 0, 99, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains227 : ∀ d ∈ compactDomains227, Slice true (vars 227) (graphGoal 227) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(226, 4), (225, 4), (195, 4), (163, 4), (99, 4)]) (specs := sliceSpecs227)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound226
    · exact bound225
    · exact bound195
    · exact bound163
    · exact bound99
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs227 : properPairs (graphGoal 227) (asRow samplesP227) (asRow samplesQ227) :=
  compactPairs (g := grid227) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos227 : ∀ p ∈ compactPerms227, autoOK (graphGoal 227) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c227k4p0 : chartBlock (check227 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev227k4 : chartBlock (check227 4) 0 1 = true :=
  c227k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c227k5p0 : chartBlock (check227 5) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev227k5 : chartBlock (check227 5) 0 2 = true :=
  c227k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c227k6p0 : chartBlock (check227 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev227k6 : chartBlock (check227 6) 0 1 = true :=
  c227k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded227 : Impossible true (graphGoal 227) 6 (vars 227).toFinset := by
  apply compactRoot (g := grid227) (t := tab227) (dom := compactDomains227) (perms := compactPerms227) pairs227 domains227 autos227
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev227k4
    · exact lev227k5
    · exact lev227k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound227 : Lower true (vars 227) (graphGoal 227) 7 :=
  plain_low (hints := 268435541) (by decide +kernel) excluded227

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound179 : Lower true (vars 179) (graphGoal 179) 7 :=
  carry_of (old := 179) (rep := 218) (swaps := [48, 113, 101]) (by decide +kernel) bound218

def grid242 : CompactGrid := (242, 5, samplesP242, samplesQ242)
def tab242 : CompactTable := (compactCount242, compactPath242, compactLive242, compactPoolIDs242, compactBucket242)
def check242 (k : Nat) := compactNode grid242 tab242 compactDomains242 compactPerms242 k
def sliceSpecs242 : List SliceSpec := [(32, 0, 210, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains242 : ∀ d ∈ compactDomains242, Slice true (vars 242) (graphGoal 242) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(210, 5)]) (specs := sliceSpecs242)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound210
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs242 : properPairs (graphGoal 242) (asRow samplesP242) (asRow samplesQ242) :=
  compactPairs (g := grid242) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos242 : ∀ p ∈ compactPerms242, autoOK (graphGoal 242) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c242k5p0 : chartBlock (check242 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev242k5 : chartBlock (check242 5) 0 1 = true :=
  c242k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded242 : Impossible true (graphGoal 242) 5 (vars 242).toFinset := by
  apply compactRoot (g := grid242) (t := tab242) (dom := compactDomains242) (perms := compactPerms242) pairs242 domains242 autos242
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev242k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound242 : Lower true (vars 242) (graphGoal 242) 6 :=
  plain_low (hints := 386990144) (by decide +kernel) excluded242

def grid241 : CompactGrid := (241, 4, samplesP241, samplesQ241)
def tab241 : CompactTable := (compactCount241, compactPath241, compactLive241, compactPoolIDs241, compactBucket241)
def check241 (k : Nat) := compactNode grid241 tab241 compactDomains241 compactPerms241 k
def sliceSpecs241 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains241 : ∀ d ∈ compactDomains241, Slice true (vars 241) (graphGoal 241) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs241)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs241 : properPairs (graphGoal 241) (asRow samplesP241) (asRow samplesQ241) :=
  compactPairs (g := grid241) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos241 : ∀ p ∈ compactPerms241, autoOK (graphGoal 241) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c241k4p0 : chartBlock (check241 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev241k4 : chartBlock (check241 4) 0 1 = true :=
  c241k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded241 : Impossible true (graphGoal 241) 4 (vars 241).toFinset := by
  apply compactRoot (g := grid241) (t := tab241) (dom := compactDomains241) (perms := compactPerms241) pairs241 domains241 autos241
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev241k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound241 : Lower true (vars 241) (graphGoal 241) 5 :=
  plain_low (hints := 1074200581) (by decide +kernel) excluded241

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound115 : Lower true (vars 115) (graphGoal 115) 5 :=
  carry_of (old := 115) (rep := 241) (swaps := [113, 101]) (by decide +kernel) bound241

def grid243 : CompactGrid := (243, 8, samplesP243, samplesQ243)
def tab243 : CompactTable := (compactCount243, compactPath243, compactLive243, compactPoolIDs243, compactBucket243)
def check243 (k : Nat) := compactNode grid243 tab243 compactDomains243 compactPerms243 k
def sliceSpecs243 : List SliceSpec := [(16, 0, 227, 0, 0, 7, 7), (32, 0, 211, 0, 0, 7, 7), (64, 0, 179, 0, 0, 7, 7), (1, 0, 242, 0, 0, 6, 6), (0, 1, 146, 96, 267386880, 6, 4), (2, 0, 241, 0, 0, 5, 5), (128, 0, 115, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains243 : ∀ d ∈ compactDomains243, Slice true (vars 243) (graphGoal 243) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(227, 7), (211, 7), (179, 7), (242, 6), (146, 4), (241, 5), (115, 5)]) (specs := sliceSpecs243)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound227
    · exact bound211
    · exact bound179
    · exact bound242
    · exact bound146
    · exact bound241
    · exact bound115
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs243 : properPairs (graphGoal 243) (asRow samplesP243) (asRow samplesQ243) :=
  compactPairs (g := grid243) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos243 : ∀ p ∈ compactPerms243, autoOK (graphGoal 243) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c243k5p0 : chartBlock (check243 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev243k5 : chartBlock (check243 5) 0 1 = true :=
  c243k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c243k6p0 : chartBlock (check243 6) 0 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev243k6 : chartBlock (check243 6) 0 5 = true :=
  c243k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c243k7p0 : chartBlock (check243 7) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev243k7 : chartBlock (check243 7) 0 3 = true :=
  c243k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c243k8p0 : chartBlock (check243 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev243k8 : chartBlock (check243 8) 0 1 = true :=
  c243k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded243 : Impossible true (graphGoal 243) 8 (vars 243).toFinset := by
  apply compactRoot (g := grid243) (t := tab243) (dom := compactDomains243) (perms := compactPerms243) pairs243 domains243 autos243
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev243k5
    · exact lev243k6
    · exact lev243k7
    · exact lev243k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound243 : Lower true (vars 243) (graphGoal 243) 9 :=
  plain_low (hints := 268501061) (by decide +kernel) excluded243

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound228 : Lower true (vars 228) (graphGoal 228) 5 :=
  carry_of (old := 228) (rep := 210) (swaps := [114, 101, 100, 113]) (by decide +kernel) bound210

def grid230 : CompactGrid := (230, 5, samplesP230, samplesQ230)
def tab230 : CompactTable := (compactCount230, compactPath230, compactLive230, compactPoolIDs230, compactBucket230)
def check230 (k : Nat) := compactNode grid230 tab230 compactDomains230 compactPerms230 k
def sliceSpecs230 : List SliceSpec := [(2, 0, 228, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains230 : ∀ d ∈ compactDomains230, Slice true (vars 230) (graphGoal 230) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(228, 5)]) (specs := sliceSpecs230)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound228
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs230 : properPairs (graphGoal 230) (asRow samplesP230) (asRow samplesQ230) :=
  compactPairs (g := grid230) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos230 : ∀ p ∈ compactPerms230, autoOK (graphGoal 230) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c230k5p0 : chartBlock (check230 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev230k5 : chartBlock (check230 5) 0 1 = true :=
  c230k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded230 : Impossible true (graphGoal 230) 5 (vars 230).toFinset := by
  apply compactRoot (g := grid230) (t := tab230) (dom := compactDomains230) (perms := compactPerms230) pairs230 domains230 autos230
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev230k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound230 : Lower true (vars 230) (graphGoal 230) 6 :=
  plain_low (hints := 303039824) (by decide +kernel) excluded230

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound229 : Lower true (vars 229) (graphGoal 229) 6 :=
  carry_of (old := 229) (rep := 230) (swaps := [16, 118]) (by decide +kernel) bound230

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound199 : Lower true (vars 199) (graphGoal 199) 6 :=
  carry_of (old := 199) (rep := 242) (swaps := [80, 97, 66, 84]) (by decide +kernel) bound242

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound165 : Lower true (vars 165) (graphGoal 165) 4 :=
  carry_of (old := 165) (rep := 216) (swaps := [48, 114, 101, 116]) (by decide +kernel) bound216

def grid167 : CompactGrid := (167, 4, samplesP167, samplesQ167)
def tab167 : CompactTable := (compactCount167, compactPath167, compactLive167, compactPoolIDs167, compactBucket167)
def check167 (k : Nat) := compactNode grid167 tab167 compactDomains167 compactPerms167 k
def sliceSpecs167 : List SliceSpec := [(2, 0, 165, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains167 : ∀ d ∈ compactDomains167, Slice true (vars 167) (graphGoal 167) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(165, 4)]) (specs := sliceSpecs167)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound165
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs167 : properPairs (graphGoal 167) (asRow samplesP167) (asRow samplesQ167) :=
  compactPairs (g := grid167) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos167 : ∀ p ∈ compactPerms167, autoOK (graphGoal 167) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c167k4p0 : chartBlock (check167 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev167k4 : chartBlock (check167 4) 0 1 = true :=
  c167k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded167 : Impossible true (graphGoal 167) 4 (vars 167).toFinset := by
  apply compactRoot (g := grid167) (t := tab167) (dom := compactDomains167) (perms := compactPerms167) pairs167 domains167 autos167
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev167k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound167 : Lower true (vars 167) (graphGoal 167) 5 :=
  plain_low (hints := 268436821) (by decide +kernel) excluded167

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound103 : Lower true (vars 103) (graphGoal 103) 5 :=
  carry_of (old := 103) (rep := 167) (swaps := [16, 118]) (by decide +kernel) bound167

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound197 : Lower true (vars 197) (graphGoal 197) 5 :=
  carry_of (old := 197) (rep := 210) (swaps := [96, 66, 118, 113]) (by decide +kernel) bound210

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound102 : Lower true (vars 102) (graphGoal 102) 4 :=
  carry_of (old := 102) (rep := 216) (swaps := [49, 114, 101, 100, 116]) (by decide +kernel) bound216

def grid231 : CompactGrid := (231, 8, samplesP231, samplesQ231)
def tab231 : CompactTable := (compactCount231, compactPath231, compactLive231, compactPoolIDs231, compactBucket231)
def check231 (k : Nat) := compactNode grid231 tab231 compactDomains231 compactPerms231 k
def sliceSpecs231 : List SliceSpec := [(4, 0, 227, 0, 0, 7, 7), (1, 0, 230, 0, 0, 6, 6), (2, 0, 229, 0, 0, 6, 6), (32, 0, 199, 0, 0, 6, 6), (64, 0, 167, 0, 0, 5, 5), (128, 0, 103, 0, 0, 5, 5), (3, 0, 228, 0, 0, 5, 5), (33, 0, 198, 0, 0, 5, 5), (34, 0, 197, 0, 0, 5, 5), (66, 0, 165, 0, 0, 4, 4), (68, 0, 163, 0, 0, 4, 4), (129, 0, 102, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains231 : ∀ d ∈ compactDomains231, Slice true (vars 231) (graphGoal 231) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(227, 7), (230, 6), (229, 6), (199, 6), (167, 5), (103, 5), (228, 5), (198, 5), (197, 5), (165, 4), (163, 4), (102, 4)]) (specs := sliceSpecs231)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound227
    · exact bound230
    · exact bound229
    · exact bound199
    · exact bound167
    · exact bound103
    · exact bound228
    · exact bound198
    · exact bound197
    · exact bound165
    · exact bound163
    · exact bound102
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs231 : properPairs (graphGoal 231) (asRow samplesP231) (asRow samplesQ231) :=
  compactPairs (g := grid231) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos231 : ∀ p ∈ compactPerms231, autoOK (graphGoal 231) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k4p0 : chartBlock (check231 4) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k4 : chartBlock (check231 4) 0 2 = true :=
  c231k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k5p0 : chartBlock (check231 5) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k5 : chartBlock (check231 5) 0 7 = true :=
  c231k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k6p0 : chartBlock (check231 6) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k6p1 : chartBlock (check231 6) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k6p2 : chartBlock (check231 6) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k6p3 : chartBlock (check231 6) 24 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k6 : chartBlock (check231 6) 0 27 = true :=
  (chartBlock_join (a := 16) (b := 11) (chartBlock_join (a := 8) (b := 8) c231k6p0 c231k6p1) (chartBlock_join (a := 8) (b := 3) c231k6p2 c231k6p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k7p0 : chartBlock (check231 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k7p1 : chartBlock (check231 7) 8 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k7 : chartBlock (check231 7) 0 9 = true :=
  (chartBlock_join (a := 8) (b := 1) c231k7p0 c231k7p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k8p0 : chartBlock (check231 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k8 : chartBlock (check231 8) 0 1 = true :=
  c231k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded231 : Impossible true (graphGoal 231) 8 (vars 231).toFinset := by
  apply compactRoot (g := grid231) (t := tab231) (dom := compactDomains231) (perms := compactPerms231) pairs231 domains231 autos231
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev231k4
    · exact lev231k5
    · exact lev231k6
    · exact lev231k7
    · exact lev231k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound231 : Lower true (vars 231) (graphGoal 231) 9 :=
  plain_low (hints := 268436821) (by decide +kernel) excluded231

def grid215 : CompactGrid := (215, 8, samplesP215, samplesQ215)
def tab215 : CompactTable := (compactCount215, compactPath215, compactLive215, compactPoolIDs215, compactBucket215)
def check215 (k : Nat) := compactNode grid215 tab215 compactDomains215 compactPerms215 k
def sliceSpecs215 : List SliceSpec := [(1, 0, 214, 0, 0, 8, 8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains215 : ∀ d ∈ compactDomains215, Slice true (vars 215) (graphGoal 215) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(214, 8)]) (specs := sliceSpecs215)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound214
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs215 : properPairs (graphGoal 215) (asRow samplesP215) (asRow samplesQ215) :=
  compactPairs (g := grid215) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos215 : ∀ p ∈ compactPerms215, autoOK (graphGoal 215) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c215k8p0 : chartBlock (check215 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev215k8 : chartBlock (check215 8) 0 1 = true :=
  c215k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded215 : Impossible true (graphGoal 215) 8 (vars 215).toFinset := by
  apply compactRoot (g := grid215) (t := tab215) (dom := compactDomains215) (perms := compactPerms215) pairs215 domains215 autos215
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev215k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound215 : Lower true (vars 215) (graphGoal 215) 9 :=
  plain_low (hints := 268502598) (by decide +kernel) excluded215

def grid183 : CompactGrid := (183, 7, samplesP183, samplesQ183)
def tab183 : CompactTable := (compactCount183, compactPath183, compactLive183, compactPoolIDs183, compactBucket183)
def check183 (k : Nat) := compactNode grid183 tab183 compactDomains183 compactPerms183 k
def sliceSpecs183 : List SliceSpec := [(4, 0, 179, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains183 : ∀ d ∈ compactDomains183, Slice true (vars 183) (graphGoal 183) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(179, 7)]) (specs := sliceSpecs183)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound179
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs183 : properPairs (graphGoal 183) (asRow samplesP183) (asRow samplesQ183) :=
  compactPairs (g := grid183) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos183 : ∀ p ∈ compactPerms183, autoOK (graphGoal 183) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c183k7p0 : chartBlock (check183 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev183k7 : chartBlock (check183 7) 0 1 = true :=
  c183k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded183 : Impossible true (graphGoal 183) 7 (vars 183).toFinset := by
  apply compactRoot (g := grid183) (t := tab183) (dom := compactDomains183) (perms := compactPerms183) pairs183 domains183 autos183
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev183k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound183 : Lower true (vars 183) (graphGoal 183) 8 :=
  plain_low (hints := 268502341) (by decide +kernel) excluded183

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound244 : Lower true (vars 244) (graphGoal 244) 6 :=
  carry_of (old := 244) (rep := 242) (swaps := [33, 100]) (by decide +kernel) bound242

def grid245 : CompactGrid := (245, 6, samplesP245, samplesQ245)
def tab245 : CompactTable := (compactCount245, compactPath245, compactLive245, compactPoolIDs245, compactBucket245)
def check245 (k : Nat) := compactNode grid245 tab245 compactDomains245 compactPerms245 k
def sliceSpecs245 : List SliceSpec := [(1, 0, 244, 0, 0, 6, 6)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains245 : ∀ d ∈ compactDomains245, Slice true (vars 245) (graphGoal 245) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(244, 6)]) (specs := sliceSpecs245)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound244
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs245 : properPairs (graphGoal 245) (asRow samplesP245) (asRow samplesQ245) :=
  compactPairs (g := grid245) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos245 : ∀ p ∈ compactPerms245, autoOK (graphGoal 245) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c245k6p0 : chartBlock (check245 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev245k6 : chartBlock (check245 6) 0 1 = true :=
  c245k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded245 : Impossible true (graphGoal 245) 6 (vars 245).toFinset := by
  apply compactRoot (g := grid245) (t := tab245) (dom := compactDomains245) (perms := compactPerms245) pairs245 domains245 autos245
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev245k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound245 : Lower true (vars 245) (graphGoal 245) 7 :=
  plain_low (hints := 537330949) (by decide +kernel) excluded245

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound118 : Lower true (vars 118) (graphGoal 118) 5 :=
  carry_of (old := 118) (rep := 241) (swaps := [16, 114, 84, 101]) (by decide +kernel) bound241

def grid119 : CompactGrid := (119, 5, samplesP119, samplesQ119)
def tab119 : CompactTable := (compactCount119, compactPath119, compactLive119, compactPoolIDs119, compactBucket119)
def check119 (k : Nat) := compactNode grid119 tab119 compactDomains119 compactPerms119 k
def sliceSpecs119 : List SliceSpec := [(1, 0, 118, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains119 : ∀ d ∈ compactDomains119, Slice true (vars 119) (graphGoal 119) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(118, 5)]) (specs := sliceSpecs119)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound118
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs119 : properPairs (graphGoal 119) (asRow samplesP119) (asRow samplesQ119) :=
  compactPairs (g := grid119) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos119 : ∀ p ∈ compactPerms119, autoOK (graphGoal 119) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k5p0 : chartBlock (check119 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k5 : chartBlock (check119 5) 0 1 = true :=
  c119k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded119 : Impossible true (graphGoal 119) 5 (vars 119).toFinset := by
  apply compactRoot (g := grid119) (t := tab119) (dom := compactDomains119) (perms := compactPerms119) pairs119 domains119 autos119
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev119k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound119 : Lower true (vars 119) (graphGoal 119) 6 :=
  plain_low (hints := 66885) (by decide +kernel) excluded119

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound213 : Lower true (vars 213) (graphGoal 213) 6 :=
  carry_of (old := 213) (rep := 242) (swaps := [80, 66, 100, 97, 81]) (by decide +kernel) bound242

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound181 : Lower true (vars 181) (graphGoal 181) 5 :=
  carry_of (old := 181) (rep := 241) (swaps := [80, 98]) (by decide +kernel) bound241

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound54 : Lower true (vars 54) (graphGoal 54) 4 :=
  carry_of (old := 54) (rep := 216) (swaps := [97, 66, 67, 117, 99]) (by decide +kernel) bound216

def grid55 : CompactGrid := (55, 4, samplesP55, samplesQ55)
def tab55 : CompactTable := (compactCount55, compactPath55, compactLive55, compactPoolIDs55, compactBucket55)
def check55 (k : Nat) := compactNode grid55 tab55 compactDomains55 compactPerms55 k
def sliceSpecs55 : List SliceSpec := [(1, 0, 54, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains55 : ∀ d ∈ compactDomains55, Slice true (vars 55) (graphGoal 55) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(54, 4)]) (specs := sliceSpecs55)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound54
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs55 : properPairs (graphGoal 55) (asRow samplesP55) (asRow samplesQ55) :=
  compactPairs (g := grid55) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos55 : ∀ p ∈ compactPerms55, autoOK (graphGoal 55) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c55k4p0 : chartBlock (check55 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev55k4 : chartBlock (check55 4) 0 1 = true :=
  c55k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded55 : Impossible true (graphGoal 55) 4 (vars 55).toFinset := by
  apply compactRoot (g := grid55) (t := tab55) (dom := compactDomains55) (perms := compactPerms55) pairs55 domains55 autos55
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev55k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound55 : Lower true (vars 55) (graphGoal 55) 5 :=
  plain_low (hints := 66885) (by decide +kernel) excluded55

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound51 : Lower true (vars 51) (graphGoal 51) 4 :=
  carry_of (old := 51) (rep := 216) (swaps := [48, 113, 101, 118]) (by decide +kernel) bound216

def grid247 : CompactGrid := (247, 10, samplesP247, samplesQ247)
def tab247 : CompactTable := (compactCount247, compactPath247, compactLive247, compactPoolIDs247, compactBucket247)
def check247 (k : Nat) := compactNode grid247 tab247 compactDomains247 compactPerms247 k
def sliceSpecs247 : List SliceSpec := [(1, 0, 246, 0, 0, 9, 9), (4, 0, 243, 0, 0, 9, 9), (16, 0, 231, 0, 0, 9, 9), (32, 0, 215, 0, 0, 9, 9), (64, 0, 183, 0, 0, 8, 8), (2, 0, 245, 0, 0, 7, 7), (0, 1, 150, 96, 267386880, 7, 5), (128, 0, 119, 0, 0, 6, 6), (18, 0, 229, 0, 0, 6, 6), (34, 0, 213, 0, 0, 6, 6), (64, 1, 150, 32, 15728640, 6, 5), (6, 0, 241, 0, 0, 5, 5), (66, 0, 181, 0, 0, 5, 5), (80, 0, 167, 0, 0, 5, 5), (132, 0, 115, 0, 0, 5, 5), (192, 0, 55, 0, 0, 5, 5), (196, 0, 51, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains247 : ∀ d ∈ compactDomains247, Slice true (vars 247) (graphGoal 247) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(246, 9), (243, 9), (231, 9), (215, 9), (183, 8), (245, 7), (150, 5), (119, 6), (229, 6), (213, 6), (241, 5), (181, 5), (167, 5), (115, 5), (55, 5), (51, 4)]) (specs := sliceSpecs247)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound246
    · exact bound243
    · exact bound231
    · exact bound215
    · exact bound183
    · exact bound245
    · exact bound150
    · exact bound119
    · exact bound229
    · exact bound213
    · exact bound241
    · exact bound181
    · exact bound167
    · exact bound115
    · exact bound55
    · exact bound51
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs247 : properPairs (graphGoal 247) (asRow samplesP247) (asRow samplesQ247) :=
  compactPairs (g := grid247) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos247 : ∀ p ∈ compactPerms247, autoOK (graphGoal 247) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k6p0 : chartBlock (check247 6) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k6p1 : chartBlock (check247 6) 8 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev247k6 : chartBlock (check247 6) 0 13 = true :=
  (chartBlock_join (a := 8) (b := 5) c247k6p0 c247k6p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k7p0 : chartBlock (check247 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k7p1 : chartBlock (check247 7) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k7p2 : chartBlock (check247 7) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k7p3 : chartBlock (check247 7) 24 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k7p4 : chartBlock (check247 7) 32 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k7p5 : chartBlock (check247 7) 40 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k7p6 : chartBlock (check247 7) 48 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev247k7 : chartBlock (check247 7) 0 54 = true :=
  (chartBlock_join (a := 24) (b := 30) (chartBlock_join (a := 8) (b := 16) c247k7p0 (chartBlock_join (a := 8) (b := 8) c247k7p1 c247k7p2)) (chartBlock_join (a := 16) (b := 14) (chartBlock_join (a := 8) (b := 8) c247k7p3 c247k7p4) (chartBlock_join (a := 8) (b := 6) c247k7p5 c247k7p6)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k8p0 : chartBlock (check247 8) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k8p1 : chartBlock (check247 8) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k8p2 : chartBlock (check247 8) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k8p3 : chartBlock (check247 8) 24 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k8p4 : chartBlock (check247 8) 32 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k8p5 : chartBlock (check247 8) 40 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev247k8 : chartBlock (check247 8) 0 46 = true :=
  (chartBlock_join (a := 24) (b := 22) (chartBlock_join (a := 8) (b := 16) c247k8p0 (chartBlock_join (a := 8) (b := 8) c247k8p1 c247k8p2)) (chartBlock_join (a := 8) (b := 14) c247k8p3 (chartBlock_join (a := 8) (b := 6) c247k8p4 c247k8p5)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k9p0 : chartBlock (check247 9) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev247k9 : chartBlock (check247 9) 0 8 = true :=
  c247k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k10p0 : chartBlock (check247 10) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev247k10 : chartBlock (check247 10) 0 1 = true :=
  c247k10p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded247 : Impossible true (graphGoal 247) 10 (vars 247).toFinset := by
  apply compactRoot (g := grid247) (t := tab247) (dom := compactDomains247) (perms := compactPerms247) pairs247 domains247 autos247
  · intro k hk
    change k ≤ 10 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev247k6
    · exact lev247k7
    · exact lev247k8
    · exact lev247k9
    · exact lev247k10
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound247 : Lower true (vars 247) (graphGoal 247) 11 :=
  plain_low (hints := 268502341) (by decide +kernel) excluded247

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound239 : Lower true (vars 239) (graphGoal 239) 11 :=
  carry_of (old := 239) (rep := 247) (swaps := [16, 67, 118]) (by decide +kernel) bound247

def grid223 : CompactGrid := (223, 10, samplesP223, samplesQ223)
def tab223 : CompactTable := (compactCount223, compactPath223, compactLive223, compactPoolIDs223, compactBucket223)
def check223 (k : Nat) := compactNode grid223 tab223 compactDomains223 compactPerms223 k
def sliceSpecs223 : List SliceSpec := [(4, 0, 219, 0, 0, 10, 10)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains223 : ∀ d ∈ compactDomains223, Slice true (vars 223) (graphGoal 223) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(219, 10)]) (specs := sliceSpecs223)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound219
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs223 : properPairs (graphGoal 223) (asRow samplesP223) (asRow samplesQ223) :=
  compactPairs (g := grid223) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos223 : ∀ p ∈ compactPerms223, autoOK (graphGoal 223) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c223k10p0 : chartBlock (check223 10) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev223k10 : chartBlock (check223 10) 0 1 = true :=
  c223k10p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded223 : Impossible true (graphGoal 223) 10 (vars 223).toFinset := by
  apply compactRoot (g := grid223) (t := tab223) (dom := compactDomains223) (perms := compactPerms223) pairs223 domains223 autos223
  · intro k hk
    change k ≤ 10 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev223k10
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound223 : Lower true (vars 223) (graphGoal 223) 11 :=
  plain_low (hints := 268502595) (by decide +kernel) excluded223

def grid254 : CompactGrid := (254, 9, samplesP254, samplesQ254)
def tab254 : CompactTable := (compactCount254, compactPath254, compactLive254, compactPoolIDs254, compactBucket254)
def check254 (k : Nat) := compactNode grid254 tab254 compactDomains254 compactPerms254 k
def sliceSpecs254 : List SliceSpec := [(8, 0, 246, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains254 : ∀ d ∈ compactDomains254, Slice true (vars 254) (graphGoal 254) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(246, 9)]) (specs := sliceSpecs254)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound246
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs254 : properPairs (graphGoal 254) (asRow samplesP254) (asRow samplesQ254) :=
  compactPairs (g := grid254) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos254 : ∀ p ∈ compactPerms254, autoOK (graphGoal 254) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c254k9p0 : chartBlock (check254 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev254k9 : chartBlock (check254 9) 0 1 = true :=
  c254k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded254 : Impossible true (graphGoal 254) 9 (vars 254).toFinset := by
  apply compactRoot (g := grid254) (t := tab254) (dom := compactDomains254) (perms := compactPerms254) pairs254 domains254 autos254
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev254k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound254 : Lower true (vars 254) (graphGoal 254) 10 :=
  plain_low (hints := 303129920) (by decide +kernel) excluded254

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound253 : Lower true (vars 253) (graphGoal 253) 10 :=
  carry_of (old := 253) (rep := 254) (swaps := [16, 67, 118]) (by decide +kernel) bound254

def grid187 : CompactGrid := (187, 7, samplesP187, samplesQ187)
def tab187 : CompactTable := (compactCount187, compactPath187, compactLive187, compactPoolIDs187, compactBucket187)
def check187 (k : Nat) := compactNode grid187 tab187 compactDomains187 compactPerms187 k
def sliceSpecs187 : List SliceSpec := [(8, 0, 179, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains187 : ∀ d ∈ compactDomains187, Slice true (vars 187) (graphGoal 187) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(179, 7)]) (specs := sliceSpecs187)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound179
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs187 : properPairs (graphGoal 187) (asRow samplesP187) (asRow samplesQ187) :=
  compactPairs (g := grid187) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos187 : ∀ p ∈ compactPerms187, autoOK (graphGoal 187) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c187k7p0 : chartBlock (check187 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev187k7 : chartBlock (check187 7) 0 1 = true :=
  c187k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded187 : Impossible true (graphGoal 187) 7 (vars 187).toFinset := by
  apply compactRoot (g := grid187) (t := tab187) (dom := compactDomains187) (perms := compactPerms187) pairs187 domains187 autos187
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev187k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound187 : Lower true (vars 187) (graphGoal 187) 8 :=
  plain_low (hints := 268501059) (by decide +kernel) excluded187

def grid191 : CompactGrid := (191, 8, samplesP191, samplesQ191)
def tab191 : CompactTable := (compactCount191, compactPath191, compactLive191, compactPoolIDs191, compactBucket191)
def check191 (k : Nat) := compactNode grid191 tab191 compactDomains191 compactPerms191 k
def sliceSpecs191 : List SliceSpec := [(4, 0, 187, 0, 0, 8, 8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains191 : ∀ d ∈ compactDomains191, Slice true (vars 191) (graphGoal 191) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(187, 8)]) (specs := sliceSpecs191)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound187
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs191 : properPairs (graphGoal 191) (asRow samplesP191) (asRow samplesQ191) :=
  compactPairs (g := grid191) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos191 : ∀ p ∈ compactPerms191, autoOK (graphGoal 191) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c191k8p0 : chartBlock (check191 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev191k8 : chartBlock (check191 8) 0 1 = true :=
  c191k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded191 : Impossible true (graphGoal 191) 8 (vars 191).toFinset := by
  apply compactRoot (g := grid191) (t := tab191) (dom := compactDomains191) (perms := compactPerms191) pairs191 domains191 autos191
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev191k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound191 : Lower true (vars 191) (graphGoal 191) 9 :=
  plain_low (hints := 268502339) (by decide +kernel) excluded191

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound127 : Lower true (vars 127) (graphGoal 127) 9 :=
  carry_of (old := 127) (rep := 191) (swaps := [16, 67, 118]) (by decide +kernel) bound191

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound182 : Lower true (vars 182) (graphGoal 182) 6 :=
  carry_of (old := 182) (rep := 230) (swaps := [33, 100]) (by decide +kernel) bound230

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound109 : Lower true (vars 109) (graphGoal 109) 6 :=
  carry_of (old := 109) (rep := 230) (swaps := [32, 33, 99, 118]) (by decide +kernel) bound230

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound77 : Lower true (vars 77) (graphGoal 77) 5 :=
  carry_of (old := 77) (rep := 210) (swaps := [16, 98, 67, 118, 116]) (by decide +kernel) bound210

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound236 : Lower true (vars 236) (graphGoal 236) 6 :=
  carry_of (old := 236) (rep := 242) (swaps := [33, 99, 118, 116]) (by decide +kernel) bound242

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound220 : Lower true (vars 220) (graphGoal 220) 6 :=
  carry_of (old := 220) (rep := 242) (swaps := [66, 83, 100, 97]) (by decide +kernel) bound242

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound180 : Lower true (vars 180) (graphGoal 180) 4 :=
  carry_of (old := 180) (rep := 216) (swaps := [98, 83, 99]) (by decide +kernel) bound216

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound108 : Lower true (vars 108) (graphGoal 108) 4 :=
  carry_of (old := 108) (rep := 216) (swaps := [114, 84, 116]) (by decide +kernel) bound216

def grid252 : CompactGrid := (252, 7, samplesP252, samplesQ252)
def tab252 : CompactTable := (compactCount252, compactPath252, compactLive252, compactPoolIDs252, compactBucket252)
def check252 (k : Nat) := compactNode grid252 tab252 compactDomains252 compactPerms252 k
def sliceSpecs252 : List SliceSpec := [(8, 0, 244, 0, 0, 6, 6), (16, 0, 236, 0, 0, 6, 6), (32, 0, 220, 0, 0, 6, 6), (0, 8, 180, 64, 251658240, 5, 4), (0, 16, 108, 128, 4026531840, 5, 4), (0, 32, 216, 4, 3840, 5, 4), (4, 32, 216, 0, 0, 4, 4), (64, 8, 180, 0, 0, 4, 4), (128, 16, 108, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains252 : ∀ d ∈ compactDomains252, Slice true (vars 252) (graphGoal 252) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(244, 6), (236, 6), (220, 6), (180, 4), (108, 4), (216, 4)]) (specs := sliceSpecs252)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound244
    · exact bound236
    · exact bound220
    · exact bound180
    · exact bound108
    · exact bound216
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs252 : properPairs (graphGoal 252) (asRow samplesP252) (asRow samplesQ252) :=
  compactPairs (g := grid252) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos252 : ∀ p ∈ compactPerms252, autoOK (graphGoal 252) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c252k4p0 : chartBlock (check252 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev252k4 : chartBlock (check252 4) 0 1 = true :=
  c252k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c252k5p0 : chartBlock (check252 5) 0 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev252k5 : chartBlock (check252 5) 0 4 = true :=
  c252k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c252k6p0 : chartBlock (check252 6) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev252k6 : chartBlock (check252 6) 0 3 = true :=
  c252k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c252k7p0 : chartBlock (check252 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev252k7 : chartBlock (check252 7) 0 1 = true :=
  c252k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded252 : Impossible true (graphGoal 252) 7 (vars 252).toFinset := by
  apply compactRoot (g := grid252) (t := tab252) (dom := compactDomains252) (perms := compactPerms252) pairs252 domains252 autos252
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev252k4
    · exact lev252k5
    · exact lev252k6
    · exact lev252k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound252 : Lower true (vars 252) (graphGoal 252) 8 :=
  plain_low (hints := 573007104) (by decide +kernel) excluded252

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound173 : Lower true (vars 173) (graphGoal 173) 5 :=
  carry_of (old := 173) (rep := 241) (swaps := [114, 83, 101, 116]) (by decide +kernel) bound241

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound45 : Lower true (vars 45) (graphGoal 45) 4 :=
  carry_of (old := 45) (rep := 216) (swaps := [96, 66, 117, 100]) (by decide +kernel) bound216

def grid189 : CompactGrid := (189, 6, samplesP189, samplesQ189)
def tab189 : CompactTable := (compactCount189, compactPath189, compactLive189, compactPoolIDs189, compactBucket189)
def check189 (k : Nat) := compactNode grid189 tab189 compactDomains189 compactPerms189 k
def sliceSpecs189 : List SliceSpec := [(8, 0, 181, 0, 0, 5, 5), (16, 0, 173, 0, 0, 5, 5), (0, 8, 180, 1, 15, 5, 4), (0, 16, 45, 128, 4026531840, 5, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains189 : ∀ d ∈ compactDomains189, Slice true (vars 189) (graphGoal 189) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(181, 5), (173, 5), (180, 4), (45, 4)]) (specs := sliceSpecs189)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound181
    · exact bound173
    · exact bound180
    · exact bound45
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs189 : properPairs (graphGoal 189) (asRow samplesP189) (asRow samplesQ189) :=
  compactPairs (g := grid189) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos189 : ∀ p ∈ compactPerms189, autoOK (graphGoal 189) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c189k6p0 : chartBlock (check189 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev189k6 : chartBlock (check189 6) 0 1 = true :=
  c189k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded189 : Impossible true (graphGoal 189) 6 (vars 189).toFinset := by
  apply compactRoot (g := grid189) (t := tab189) (dom := compactDomains189) (perms := compactPerms189) pairs189 domains189 autos189
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev189k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound189 : Lower true (vars 189) (graphGoal 189) 7 :=
  plain_low (hints := 537330947) (by decide +kernel) excluded189

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound126 : Lower true (vars 126) (graphGoal 126) 7 :=
  carry_of (old := 126) (rep := 189) (swaps := [16, 67, 118]) (by decide +kernel) bound189

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound59 : Lower true (vars 59) (graphGoal 59) 5 :=
  carry_of (old := 59) (rep := 241) (swaps := [113, 83, 101, 118]) (by decide +kernel) bound241

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound47 : Lower true (vars 47) (graphGoal 47) 5 :=
  carry_of (old := 47) (rep := 55) (swaps := [16, 67]) (by decide +kernel) bound55

def grid63 : CompactGrid := (63, 6, samplesP63, samplesQ63)
def tab63 : CompactTable := (compactCount63, compactPath63, compactLive63, compactPoolIDs63, compactBucket63)
def check63 (k : Nat) := compactNode grid63 tab63 compactDomains63 compactPerms63 k
def sliceSpecs63 : List SliceSpec := [(4, 0, 59, 0, 0, 5, 5), (8, 0, 55, 0, 0, 5, 5), (16, 0, 47, 0, 0, 5, 5), (1, 8, 54, 0, 0, 4, 4), (2, 16, 45, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains63 : ∀ d ∈ compactDomains63, Slice true (vars 63) (graphGoal 63) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(59, 5), (55, 5), (47, 5), (54, 4), (45, 4)]) (specs := sliceSpecs63)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound59
    · exact bound55
    · exact bound47
    · exact bound54
    · exact bound45
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs63 : properPairs (graphGoal 63) (asRow samplesP63) (asRow samplesQ63) :=
  compactPairs (g := grid63) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos63 : ∀ p ∈ compactPerms63, autoOK (graphGoal 63) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c63k5p0 : chartBlock (check63 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev63k5 : chartBlock (check63 5) 0 1 = true :=
  c63k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c63k6p0 : chartBlock (check63 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev63k6 : chartBlock (check63 6) 0 1 = true :=
  c63k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded63 : Impossible true (graphGoal 63) 6 (vars 63).toFinset := by
  apply compactRoot (g := grid63) (t := tab63) (dom := compactDomains63) (perms := compactPerms63) pairs63 domains63 autos63
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev63k5
    · exact lev63k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound63 : Lower true (vars 63) (graphGoal 63) 7 :=
  plain_low (hints := 66883) (by decide +kernel) excluded63

def grid255 : CompactGrid := (255, 12, samplesP255, samplesQ255)
def tab255 : CompactTable := (compactCount255, compactPath255, compactLive255, compactPoolIDs255, compactBucket255)
def check255 (k : Nat) := compactNode grid255 tab255 compactDomains255 compactPerms255 k
def sliceSpecs255 : List SliceSpec := [(4, 0, 251, 0, 0, 11, 11), (8, 0, 247, 0, 0, 11, 11), (16, 0, 239, 0, 0, 11, 11), (32, 0, 223, 0, 0, 11, 11), (1, 0, 254, 0, 0, 10, 10), (2, 0, 253, 0, 0, 10, 10), (64, 0, 191, 0, 0, 9, 9), (128, 0, 127, 0, 0, 9, 9), (0, 8, 182, 65, 251658255, 8, 6), (0, 16, 109, 130, 4026532080, 8, 6), (0, 1, 150, 104, 267448320, 8, 5), (0, 2, 77, 176, 4043243520, 8, 5), (3, 0, 252, 0, 0, 8, 8), (68, 0, 187, 0, 0, 8, 8), (72, 0, 183, 0, 0, 8, 8), (66, 0, 189, 0, 0, 7, 7), (129, 0, 126, 0, 0, 7, 7), (192, 0, 63, 0, 0, 7, 7), (128, 16, 109, 2, 240, 7, 6), (8, 1, 150, 96, 267386880, 7, 5), (64, 1, 150, 40, 15790080, 7, 5), (128, 2, 77, 48, 16711680, 7, 5), (130, 0, 109, 0, 0, 6, 6), (65, 8, 182, 0, 0, 6, 6), (160, 2, 77, 16, 983040, 6, 5), (193, 0, 54, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains255 : ∀ d ∈ compactDomains255, Slice true (vars 255) (graphGoal 255) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(251, 11), (247, 11), (239, 11), (223, 11), (254, 10), (253, 10), (191, 9), (127, 9), (182, 6), (109, 6), (150, 5), (77, 5), (252, 8), (187, 8), (183, 8), (189, 7), (126, 7), (63, 7), (54, 4)]) (specs := sliceSpecs255)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound251
    · exact bound247
    · exact bound239
    · exact bound223
    · exact bound254
    · exact bound253
    · exact bound191
    · exact bound127
    · exact bound182
    · exact bound109
    · exact bound150
    · exact bound77
    · exact bound252
    · exact bound187
    · exact bound183
    · exact bound189
    · exact bound126
    · exact bound63
    · exact bound54
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs255 : properPairs (graphGoal 255) (asRow samplesP255) (asRow samplesQ255) :=
  compactPairs (g := grid255) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos255 : ∀ p ∈ compactPerms255, autoOK (graphGoal 255) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k7p0 : chartBlock (check255 7) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev255k7 : chartBlock (check255 7) 0 3 = true :=
  c255k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k8p0 : chartBlock (check255 8) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k8p1 : chartBlock (check255 8) 8 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev255k8 : chartBlock (check255 8) 0 11 = true :=
  (chartBlock_join (a := 8) (b := 3) c255k8p0 c255k8p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k9p0 : chartBlock (check255 9) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k9p1 : chartBlock (check255 9) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k9p2 : chartBlock (check255 9) 16 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev255k9 : chartBlock (check255 9) 0 20 = true :=
  (chartBlock_join (a := 8) (b := 12) c255k9p0 (chartBlock_join (a := 8) (b := 4) c255k9p1 c255k9p2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k10p0 : chartBlock (check255 10) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k10p1 : chartBlock (check255 10) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k10p2 : chartBlock (check255 10) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k10p3 : chartBlock (check255 10) 24 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k10p4 : chartBlock (check255 10) 32 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev255k10 : chartBlock (check255 10) 0 37 = true :=
  (chartBlock_join (a := 16) (b := 21) (chartBlock_join (a := 8) (b := 8) c255k10p0 c255k10p1) (chartBlock_join (a := 8) (b := 13) c255k10p2 (chartBlock_join (a := 8) (b := 5) c255k10p3 c255k10p4)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k11p0 : chartBlock (check255 11) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev255k11 : chartBlock (check255 11) 0 8 = true :=
  c255k11p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k12p0 : chartBlock (check255 12) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev255k12 : chartBlock (check255 12) 0 1 = true :=
  c255k12p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded255 : Impossible true (graphGoal 255) 12 (vars 255).toFinset := by
  apply compactRoot (g := grid255) (t := tab255) (dom := compactDomains255) (perms := compactPerms255) pairs255 domains255 autos255
  · intro k hk
    change k ≤ 12 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev255k7
    · exact lev255k8
    · exact lev255k9
    · exact lev255k10
    · exact lev255k11
    · exact lev255k12
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound255 : Lower true (vars 255) (graphGoal 255) 13 :=
  plain_low (hints := 268502339) (by decide +kernel) excluded255
def winningGates : List Gate := [⟨.or,[7,5]⟩, ⟨.or,[7,1]⟩, ⟨.or,[5,3]⟩, ⟨.or,[3,2]⟩, ⟨.or,[2,1]⟩, ⟨.or,[7,11]⟩, ⟨.or,[6,10]⟩, ⟨.and,[8,12]⟩, ⟨.and,[9,4]⟩, ⟨.and,[13,6]⟩, ⟨.and,[14,0]⟩, ⟨.or,[18,17]⟩, ⟨.or,[19,16]⟩, ⟨.or,[20,15]⟩]
theorem winningLegal : ∀ g ∈ winningGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [winningGates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem winningCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨winningGates,21⟩ (List.ofFn x) = edge8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem asListed : ∀ x : Fin 8 → Bool, edge8 x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
end PEqualNP.Outside.L_meta_14722

open PEqualNP.Outside.L_meta_14722 PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_14722 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ correct
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g,hg,op⟩ := hn
    have lt : gates.countP (fun q => !isNot q) < gates.length := by
      rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
      · exact h
      · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
        simp [isNot,op] at eq
    obtain ⟨k,hk,run⟩ := physicalSigned ⟨gates,o⟩ legal (fun x => (correct x).trans (asListed x).symm)
    change k ≤ gates.countP (fun q => !isNot q) at hk
    have low : 12 < k := by
      by_contra! small
      apply excluded255 k small
      have same : graph = graphGoal 255 := by decide +kernel
      simpa only [←same, show vars 255 = eightInputs by rfl] using run
    exact ⟨winningGates,21,winningLegal,by change 14 ≤ gates.length; omega, fun x => (winningCorrect x).trans (asListed x)⟩
  · refine ⟨gates,o,?_,le_rfl,correct⟩
    intro g hg
    obtain ⟨op,arity⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),arity⟩
