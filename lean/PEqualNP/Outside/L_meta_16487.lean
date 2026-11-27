import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16487

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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


abbrev Row := Fin 256

def plainWord (a : Sig) : Bool := !(bit 0 a)

theorem normalize_plain {u} {w : List Sig} (h : w.all plainWord = true) : w.map (nrm u) = w := by
  have eq : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [eq, List.map_id]

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




variable {n : ℕ}

def roots (wires : Fin n → Sig) : List Sig := List.ofFn wires

def sampled (wires : Fin n → Sig) (r : Row) (i : Fin n) : Bool := bit r (wires i)

theorem sampledInput (wires : Fin n → Sig) (r : Row) :
    List.ofFn (sampled wires r) = (roots wires).map (bit r) := by
  rw [roots, List.map_ofFn]
  rfl

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))



section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩


end Live

namespace Projection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]
theorem build_mono {ops : β → β → Finset β} {g : β} {k : ℕ} {S T : Finset β}
    (h : build ops g k S) (hst : S ⊆ T) : build ops g k T := by
  induction k generalizing S T with
  | zero => exact hst h
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, ht⟩
    · exact Or.inl (ih h hst)
    · exact Or.inr ⟨a, hst ha, b, hst hb, hab, z, hz, ih ht (Finset.insert_subset_insert _ hst)⟩
def proj (f : α → β) (s : Finset α) : Finset β := (s.image f).erase 0
def zeros (f : α → β) (s : Finset α) : ℕ := (s.filter (fun a => f a = 0)).card

theorem zeros_paid (f : α → β) (a b z : α) (r : Finset α)
    (ha : f a ≠ 0) (hb : f b ≠ 0) :
    zeros f (insert a (insert b r)) ≤ zeros f (insert z r) := by
  simp only [zeros, Finset.filter_insert, if_neg ha, if_neg hb]
  split_ifs
  · exact Finset.card_le_card (Finset.subset_insert _ _)
  · exact le_rfl

theorem zeros_free (f : α → β) (a b z : α) (r : Finset α)
    (hn : z ∉ insert a (insert b r))
    (hz : f a = 0 → f b = 0 → f z = 0) :
    zeros f (insert a (insert b r)) ≤ zeros f (insert z r) + 1 := by
  have hzr : z ∉ r := fun hr => hn (by simp [hr])
  let t := r.filter (fun x => f x = 0)
  have h1 := Finset.card_insert_le a t
  have h2 := Finset.card_insert_le b t
  have h3 := Finset.card_insert_le a (insert b t)
  have h4 : t.card ≤ (insert z t).card := Finset.card_le_card (Finset.subset_insert _ _)
  have hznot : z ∉ t := by simp [t, hzr]
  have h5 := Finset.card_insert_of_notMem hznot
  dsimp [t] at h1 h2 h3 h4 h5
  by_cases ha : f a = 0 <;> by_cases hb : f b = 0 <;> by_cases hzero : f z = 0
  all_goals simp only [zeros, Finset.filter_insert, ha, hb, hzero, if_true, if_false]
  all_goals try { exfalso; exact hzero (hz ha hb) }
  all_goals omega

theorem proj_subset_insert (f : α → β) (a b z : α) (r : Finset α) :
    proj f (insert z r) ⊆ insert (f z) (proj f (insert a (insert b r))) := by
  intro x hx
  simp only [proj, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hx ⊢
  rcases hx with ⟨hx0, w, (rfl | hw), rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hx0, w, Or.inr (Or.inr hw), rfl⟩

theorem proj_subset_free (f : α → β) (a b z : α) (r : Finset α)
    (hz : f z = 0 ∨ f z = f a ∨ f z = f b) :
    proj f (insert z r) ⊆ proj f (insert a (insert b r)) := by
  intro x hx
  simp only [proj, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hx ⊢
  rcases hx with ⟨hx0, w, (rfl | hw), rfl⟩
  · rcases hz with hz | hz | hz
    · exact False.elim (hx0 hz)
    · exact ⟨hx0, a, Or.inl rfl, hz.symm⟩
    · exact ⟨hx0, b, Or.inr (Or.inl rfl), hz.symm⟩
  · exact ⟨hx0, w, Or.inr (Or.inr hw), rfl⟩

theorem project_step (f : α → β) (ops : α → α → Finset α) (ops' : β → β → Finset β)
    (samezero : ∀ a b z, z ∈ ops a b → f a = 0 → f b = 0 → f z = 0)
    (casesStep : ∀ a b z, z ∈ ops a b →
      f z = 0 ∨ f z = f a ∨ f z = f b ∨
        (f a ≠ 0 ∧ f b ≠ 0 ∧ f a ≠ f b ∧ f z ∈ ops' (f a) (f b))) :
    ∀ a b z r, a ≠ b → z ∈ ops a b → z ∉ insert a (insert b r) →
      let s := insert a (insert b r)
      let t := insert z r
      ((proj f t ⊆ proj f s ∧ zeros f s ≤ zeros f t + 1) ∨
       (∃ x ∈ proj f s, ∃ y ∈ proj f s, x ≠ y ∧ ∃ v ∈ ops' x y,
         proj f t ⊆ insert v (proj f s) ∧ zeros f s ≤ zeros f t)) := by
  intro a b z r hab hz hn
  rcases casesStep a b z hz with h | h | h | ⟨ha, hb, hab', hmem⟩
  · exact Or.inl ⟨proj_subset_free f a b z r (Or.inl h), zeros_free f a b z r hn (samezero a b z hz)⟩
  · exact Or.inl ⟨proj_subset_free f a b z r (Or.inr (Or.inl h)), zeros_free f a b z r hn (samezero a b z hz)⟩
  · exact Or.inl ⟨proj_subset_free f a b z r (Or.inr (Or.inr h)), zeros_free f a b z r hn (samezero a b z hz)⟩
  · right
    refine ⟨f a, ?_, f b, ?_, hab', f z, hmem, proj_subset_insert f a b z r, zeros_paid f a b z r ha hb⟩
    · simp [proj, ha]
    · simp [proj, hb]

theorem projection {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {goal : α} (f : α → β) (hg : f goal ≠ 0)
    (step : ∀ a b z r, a ≠ b → z ∈ ops a b → z ∉ insert a (insert b r) →
      let s := insert a (insert b r)
      let t := insert z r
      ((proj f t ⊆ proj f s ∧ zeros f s ≤ zeros f t + 1) ∨
       (∃ x ∈ proj f s, ∃ y ∈ proj f s, x ≠ y ∧ ∃ v ∈ ops' x y,
         proj f t ⊆ insert v (proj f s) ∧ zeros f s ≤ zeros f t)))
    {k : ℕ} {s : Finset α} (h : live ops goal k s) :
    ∃ j, j + zeros f s ≤ k ∧ build ops' (f goal) j (proj f s) := by
  induction k generalizing s with
  | zero =>
    change s = {goal} at h
    subst s
    refine ⟨0, ?_, ?_⟩
    · simp [zeros, hg]
    · simp [build, proj, hg]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, r, rfl, tail⟩
    · obtain ⟨j, hj, hbuild⟩ := ih skip
      exact ⟨j, by omega, hbuild⟩
    · obtain ⟨j, hj, hbuild⟩ := ih tail
      rcases step a b z r hab hz hout with ⟨hsub, hc⟩ | ⟨x, hx, y, hy, hxy, v, hv, hsub, hc⟩
      · exact ⟨j, by omega, build_mono hbuild hsub⟩
      · exact ⟨j+1, by omega, Or.inr ⟨x, hx, y, hy, hxy, v, hv, build_mono hbuild hsub⟩⟩
end Projection


def signedOps (a b : Sig) : Finset Sig := ((List.range 4).map (fun d => bin d a b)).toFinset

theorem memSigned {a b z : Sig} : z ∈ signedOps a b ↔ ∃ d < 4, bin d a b = z := by
  simp only [signedOps, List.mem_toFinset, List.mem_map, List.mem_range]

theorem anySigned {u : Bool} {T : Sig} {k : ℕ} {S : Finset Sig} (h : Live u T k S) :
    live signedOps T k S := by
  induction h using Live.ind with
  | stop hp => rfl
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have d4 : d < 4 := by rcases hd with h | h <;> omega
    exact Or.inr ⟨a, by simp, b, by simp, hab, bin d a b, memSigned.mpr ⟨d, d4, rfl⟩,
      hf, U, rfl, ih⟩

theorem signedSeparates (r s : Row) (a b z : Sig) (hz : z ∈ signedOps a b)
    (hd : bit r z ≠ bit s z) : bit r a ≠ bit s a ∨ bit r b ≠ bit s b := by
  obtain ⟨d, _, rfl⟩ := memSigned.mp hz
  by_cases h : bit r a = bit s a
  · right
    intro hb
    apply hd
    rw [bit_bin, bit_bin, h, hb]
  · exact Or.inl h

def crop (w : Sig) : Sig := (w.setWidth 128).setWidth 256

theorem bitCrop (w : Sig) (i : ℕ) :
    (crop w).getLsbD i = (decide (i < 128) && w.getLsbD i) := by
  by_cases h : i < 128
  · have hh : i < 256 := by omega
    simp [crop, h, hh]
  · simp [crop, h]


theorem crop_bin (d : ℕ) (a b : Sig) : crop (bin d a b) = bin d (crop a) (crop b) := by
  simp only [bin]
  split_ifs <;> apply BitVec.eq_of_getLsbD_eq
  all_goals
    intro i hi
    by_cases lo : i < 128 <;>
      simp only [bitCrop, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        hi, lo, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_false,
        Bool.false_or, Bool.or_false, Bool.not_false]



theorem bin_zero_op (a b : Sig) : bin 0 a b = a &&& b := rfl
theorem bin_one_op (a b : Sig) : bin 1 a b = a ||| b := rfl
theorem bin_two_op (a b : Sig) : bin 2 a b = a &&& ~~~b := rfl
theorem bin_three_op (a b : Sig) : bin 3 a b = ~~~a &&& b := rfl

theorem crop_cases (a b z : Sig) (hz : z ∈ signedOps a b) :
    crop z = 0 ∨ crop z = crop a ∨ crop z = crop b ∨
    (crop a ≠ 0 ∧ crop b ≠ 0 ∧ crop a ≠ crop b ∧ crop z ∈ signedOps (crop a) (crop b)) := by
  obtain ⟨d, d4, rfl⟩ := memSigned.mp hz
  rw [crop_bin]
  generalize crop a = p
  generalize crop b = q
  by_cases ha : p = 0
  · subst p
    rcases (show d=0 ∨ d=1 ∨ d=2 ∨ d=3 by omega) with rfl | rfl | rfl | rfl
    · left; exact BitVec.zero_and
    · right; right; left; exact BitVec.zero_or
    · left; exact BitVec.zero_and
    · right; right; left; exact BitVec.allOnes_and
  by_cases hb : q = 0
  · subst q
    rcases (show d=0 ∨ d=1 ∨ d=2 ∨ d=3 by omega) with rfl | rfl | rfl | rfl
    · left; exact BitVec.and_zero
    · right; left; exact BitVec.or_zero
    · right; left; exact BitVec.and_allOnes
    · left; exact BitVec.and_zero
  by_cases h : p = q
  · subst q
    rcases (show d=0 ∨ d=1 ∨ d=2 ∨ d=3 by omega) with rfl | rfl | rfl | rfl
    · right; left; exact BitVec.and_self
    · right; left; exact BitVec.or_self
    · left; exact BitVec.and_not_self p
    · left; exact BitVec.not_and_self p
  exact Or.inr (Or.inr (Or.inr ⟨ha, hb, h, memSigned.mpr ⟨d, d4, rfl⟩⟩))

theorem crop_zero (a b z : Sig) (hz : z ∈ signedOps a b)
    (ha : crop a = 0) (hb : crop b = 0) : crop z = 0 := by
  obtain ⟨d, d4, rfl⟩ := memSigned.mp hz
  have ds : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
  rw [crop_bin, ha, hb]
  rcases ds with rfl | rfl | rfl | rfl <;> simp [bin]


def cut (w : Sig) : BitVec 64 := ((w >>> 64) ^^^ w).setWidth 64

def cuts (xs : List Sig) : BitVec 64 := xs.foldr (fun w total => cut w ||| total) 0

def separatedOn (T : Sig) (xs : List Sig) : Bool := (cuts xs &&& cut T) == cut T

theorem cut_get (w : Sig) (i : ℕ) (hi : i < 64) :
    (cut w).getLsbD i = (w.getLsbD (64+i) ^^ w.getLsbD i) := by
  simp [cut, hi]

theorem cutsOfMem {i : ℕ} {a : Sig} {xs : List Sig} (m : a ∈ xs)
    (h : (cut a).getLsbD i = true) : (cuts xs).getLsbD i = true := by
  induction xs with
  | nil => simp at m
  | cons b bs ih =>
    rcases List.mem_cons.mp m with rfl | tail
    · simp [cuts, h]
    · change (cut b ||| cuts bs).getLsbD i = true
      rw [BitVec.getLsbD_or, ih tail]
      simp

theorem separatedOfLive {T : Sig} {k : ℕ} {S : Finset Sig} (run : live signedOps T k S)
    {xs : List Sig} (eq : xs.toFinset = S) :
    separatedOn T xs = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  cases bitreq : (cut T).getLsbD i
  · simp
  · have ci : 64+i < 256 := by omega
    rw [cut_get T i hi] at bitreq
    have diff : bit ⟨64+i, ci⟩ T ≠ bit ⟨i, by omega⟩ T := by
      intro he
      change T.getLsbD (64+i) = T.getLsbD i at he
      rw [he] at bitreq
      simp at bitreq
    obtain ⟨a, ha, hdiff⟩ := live_separates (fun w => bit ⟨64+i, ci⟩ w ≠ bit ⟨i, by omega⟩ w) diff (signedSeparates _ _) run
    rw [← eq] at ha
    have hbit : (cut a).getLsbD i = true := by
      rw [cut_get a i hi]
      change a.getLsbD (64+i) ≠ a.getLsbD i at hdiff
      cases h1 : a.getLsbD (64+i) <;> cases h2 : a.getLsbD i <;> simp_all
    simpa using cutsOfMem (List.mem_toFinset.mp ha) hbit

def keepChoices (a b : Sig) (r : List Sig) : List (List Sig) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Sig} {a b : Sig} {needed : Finset Sig}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind


def searchBranches (T : Sig) (k : ℕ) (xs : List Sig) (search : List Sig → Bool) : Bool :=
  (pairs xs).any (fun (a,b,r) =>
    (List.range 4).any (fun d =>
      (keepChoices a b r).any (fun kept =>
        let z := bin d a b
        let next := z :: kept
        decide (z ≠ a ∧ z ≠ b ∧ z ∉ kept) &&
        decide (next.length ≤ k + 1) && separatedOn T next && search next)))

theorem searchBranches_mono (T : Sig) {k l : ℕ} (bound : k ≤ l) (xs : List Sig)
    {f g : List Sig → Bool} (next : ∀ ws, f ws = true → g ws = true)
    (h : searchBranches T k xs f = true) : searchBranches T l xs g = true := by
  unfold searchBranches at h ⊢
  obtain ⟨⟨a,b,r⟩, hab, step⟩ := List.any_eq_true.mp h
  obtain ⟨d, hd, step⟩ := List.any_eq_true.mp step
  obtain ⟨kept, hkept, step⟩ := List.any_eq_true.mp step
  apply List.any_eq_true.mpr
  refine ⟨(a,b,r), hab, List.any_eq_true.mpr ⟨d, hd, List.any_eq_true.mpr ⟨kept, hkept, ?_⟩⟩⟩
  dsimp only at step ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at step ⊢
  rcases step with ⟨⟨⟨fresh, len⟩, sep⟩, tail⟩
  exact ⟨⟨⟨fresh, len.trans (Nat.succ_le_succ bound)⟩, sep⟩, next _ tail⟩

def boundedSearch (T : Sig) : ℕ → List Sig → Bool
  | 0, xs => xs == [T]
  | k + 1, xs => (xs == [T]) ||
    (decide (xs.length ≤ k + 2) && separatedOn T xs &&
      searchBranches T k xs (boundedSearch T k))

theorem searchBudgetStep (T : Sig) (k : ℕ) (xs : List Sig)
    (h : boundedSearch T k xs = true) : boundedSearch T (k + 1) xs = true := by
  induction k generalizing xs with
  | zero =>
    change (xs == [T]) = true at h
    rw [boundedSearch, h]
    rfl
  | succ k ih =>
    rw [boundedSearch] at h ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with done | ⟨⟨len, sep⟩, tails⟩
    · exact Or.inl done
    · refine Or.inr ⟨⟨by omega, sep⟩, ?_⟩
      exact searchBranches_mono T (Nat.le_succ k) xs ih tails

theorem boundedComplete (T : Sig) {k : ℕ} {S : Finset Sig}
    (run : live signedOps T k S) (xs : List Sig) (hn : xs.Nodup) (hs : xs.toFinset = S) :
    boundedSearch T k xs = true := by
  induction k generalizing S xs with
  | zero =>
    have hS : S = {T} := run
    subst S
    have hlen := List.toFinset_card_of_nodup hn
    rw [hs] at hlen
    simp only [Finset.card_singleton] at hlen
    cases xs with
    | nil => simp at hlen
    | cons v vs =>
      cases vs with
      | nil => simpa [boundedSearch] using hs
      | cons w ws => simp at hlen
  | succ k ih =>
    have len : xs.length ≤ k + 2 := by
      rw [← List.toFinset_card_of_nodup hn, hs]
      exact live_card run
    have separate := separatedOfLive run hs
    rcases run with skip | ⟨a, ma, b, mb, hab, z, opZ, hf, U, rfl, tail⟩
    · exact searchBudgetStep T k xs (ih skip xs hn hs)
    obtain ⟨d, d4, rfl⟩ := memSigned.mp opZ
    have hd : allowed true d := Or.inr ⟨rfl,d4⟩
    let z := bin d a b
    have hz : z ∉ U := fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have aMem : a ∈ xs := List.mem_toFinset.mp (hs.symm ▸ (by simp : a ∈ insert a (insert b U)))
    have bMem : b ∈ xs := List.mem_toFinset.mp (hs.symm ▸ (by simp : b ∈ insert a (insert b U)))
    obtain ⟨r, step, hp⟩ := pick_two aMem bMem hab
    have proof (p q : Sig) (j : ℕ) (hit : (p,q,r) ∈ pairs xs)
        (hpq : xs.Perm (p :: q :: r)) (hs' : xs.toFinset = insert p (insert q U))
        (j4 : j < 4) (heq : bin j p q = z) :
        searchBranches T k xs (boundedSearch T k) = true := by
      unfold searchBranches
      obtain ⟨kept, hkeep, hnK, hK⟩ := recover_kept hpq hn hs'
      have hnz : (z :: kept).Nodup := by
        refine List.nodup_cons.mpr ⟨?_, hnK⟩
        intro hm
        exact hz (hK ▸ List.mem_toFinset.mpr hm)
      have hsZ : (z :: kept).toFinset = insert z U := by simp [hK]
      have hlen : (z :: kept).length ≤ k+1 := by
        rw [← List.toFinset_card_of_nodup hnz, hsZ]
        exact live_card tail
      have guard := separatedOfLive tail hsZ
      have good := ih tail (z :: kept) hnz hsZ
      apply List.any_eq_true.mpr
      refine ⟨(p,q,r), hit, List.any_eq_true.mpr ⟨j, List.mem_range.mpr j4, ?_⟩⟩
      apply List.any_eq_true.mpr
      refine ⟨kept, hkeep, ?_⟩
      dsimp only
      have fresh : decide (z ≠ p ∧ z ≠ q ∧ z ∉ kept) = true := by
        apply decide_eq_true
        refine ⟨?_, ?_, ?_⟩
        · intro h
          apply hf
          change z ∈ insert a (insert b U)
          rw [h, ← hs]
          exact List.mem_toFinset.mpr (hpq.mem_iff.mpr (by simp : p ∈ p :: q :: r))
        · intro h
          apply hf
          change z ∈ insert a (insert b U)
          rw [h, ← hs]
          exact List.mem_toFinset.mpr (hpq.mem_iff.mpr (by simp : q ∈ p :: q :: r))
        · exact fun h => hz (hK ▸ List.mem_toFinset.mpr h)
      rw [heq, fresh, guard, good]
      simp only [Bool.true_and, Bool.and_true, decide_eq_true_eq]
      exact hlen
    rw [boundedSearch, Bool.or_eq_true]
    right
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨len, separate⟩, ?_⟩
    rcases step with h | h
    · exact proof a b d h hp hs d4 rfl
    · obtain ⟨hd', _⟩ := flip_flip hd
      have d4' : flipOp d < 4 := by rcases hd' with h | h <;> omega
      exact proof b a (flipOp d) h (hp.trans (List.Perm.swap _ _ _))
        (by simpa [Finset.insert_comm] using hs) d4' (bin_flip hd a b).symm




theorem binary_lower_projected (C : Circuit) (fit : FanInTwo C) (wires : Fin n → Sig)
    (wirePlain : (roots wires).all plainWord = true) (T : Sig)
    (pT : proper T) (t0 : bit 0 T = false)
    (computes : ∀ r : Row, C.eval (List.ofFn (sampled wires r)) = bit r T)
    (positions : Fin n → Row × Row)
    (changes : ∀ i : Fin n, bit (positions i).1 T ≠ bit (positions i).2 T)
    (isolated : ∀ i j : Fin n, wires j ≠ wires i →
      bit (positions i).1 (wires j) = bit (positions i).2 (wires j))
    (minor : List Sig) (minorT : Sig) (removed cap : ℕ)
    (hproj : crop T = minorT) (hgoal : minorT ≠ 0)
    (hcount : Projection.zeros crop (roots wires).toFinset = removed)
    (htarget : ∀ i : Fin n, crop (wires i) = 0 ∨ crop (wires i) ∈ minor)
    (hdist : minor.Nodup)
    (noSmall : ∀ j : Fin cap, (minor.sublists.all (fun xs =>
      !(boundedSearch minorT j.val xs))) = true) :
    removed + cap ≤ C.gates.countP (fun g => !isNot g) := by
  have goalEq : (execute C.gates (roots wires)).getD C.output zero = T := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fit g hg).1), ← sampledInput]
    exact computes r
  have out := get_rep (u := true) (execute C.gates (roots wires)) C.output
  rw [goalEq] at out
  unfold Repr at out
  rw [nrm_id t0] at out
  obtain ⟨k, S, hk, run, sub⟩ := extract (u := true) C.gates (roots wires) fit (by simp) pT
    (out.resolve_right (fun h => h pT))
  rw [normalize_plain wirePlain] at sub
  have incl : (roots wires).toFinset ⊆ S := by
    intro a ha
    have mem := List.mem_toFinset.mp ha
    rw [roots] at mem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp mem
    apply raw_required run (roots wires) _ sub (positions i).1 (positions i).2 (changes i)
    intro v hv hne
    rw [roots] at hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    exact isolated i j hne
  have equal : (roots wires).toFinset = S :=
    Finset.Subset.antisymm incl (fun a ha => List.mem_toFinset.mpr (sub a ha))
  have nonzero : crop T ≠ 0 := by rw [hproj]; exact hgoal
  obtain ⟨j, hj, hb⟩ := Projection.projection (ops' := signedOps) crop nonzero
    (Projection.project_step crop signedOps signedOps crop_zero crop_cases) (anySigned run)
  rw [← equal, hcount] at hj
  rw [hproj] at hb
  by_contra! lower
  have small : j < cap := by omega
  obtain ⟨S', hs', run'⟩ := compress hb
  have subset : S' ⊆ minor.toFinset := by
    intro a ha
    obtain ⟨hnz, himg⟩ := Finset.mem_erase.mp (hs' ha)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp himg
    have h := sub w hw
    rw [roots] at h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    exact List.mem_toFinset.mpr ((htarget i).resolve_left hnz)
  let xs := minor.filter (fun w => decide (w ∈ S'))
  have xsSet : xs.toFinset = S' := by
    ext v
    simp only [xs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨List.mem_toFinset.mp (subset h), h⟩⟩
  have exhausted := List.all_eq_true.mp (noSmall ⟨j, small⟩) xs
    (List.mem_sublists.mpr List.filter_sublist)
  have passed := boundedComplete minorT run' xs (hdist.filter _) xsSet
  simp [passed] at exhausted

theorem no_inversion_projected {f : (Fin n → Bool) → Bool} (wires : Fin n → Sig)
    (wirePlain : (roots wires).all plainWord = true) (T : Sig)
    (pT : proper T) (t0 : bit 0 T = false)
    (table : ∀ r : Row, f (sampled wires r) = bit r T)
    (positions : Fin n → Row × Row)
    (changes : ∀ i : Fin n, bit (positions i).1 T ≠ bit (positions i).2 T)
    (isolated : ∀ i j : Fin n, wires j ≠ wires i →
      bit (positions i).1 (wires j) = bit (positions i).2 (wires j))
    (minor : List Sig) (minorT : Sig) (removed cap : ℕ)
    (hproj : crop T = minorT) (hgoal : minorT ≠ 0)
    (hcount : Projection.zeros crop (roots wires).toFinset = removed)
    (htarget : ∀ i : Fin n, crop (wires i) = 0 ∨ crop (wires i) ∈ minor)
    (hdist : minor.Nodup)
    (noSmall : ∀ j : Fin cap, (minor.sublists.all (fun xs =>
      !(boundedSearch minorT j.val xs))) = true)
    (W : Circuit) (mono : Monotone2 W) (small : W.size ≤ removed + cap + 1)
    (correct : ∀ x : Fin n → Bool, W.eval (List.ofFn x) = f x) :
    ∀ s : ℕ, HasCircuitSize n f s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  intro s h
  obtain ⟨C, fit, budget, eval⟩ := h
  by_cases hn : ∃ g ∈ C.gates, g.op = GateOp.not
  · have lower := binary_lower_projected C fit wires wirePlain T pT t0
      (fun r => (eval (sampled wires r)).trans (table r)) positions changes isolated
      minor minorT removed cap hproj hgoal hcount htarget hdist noSmall
    obtain ⟨g, hg, hop⟩ := hn
    have extra : C.gates.countP (fun t => !isNot t) < C.gates.length := by
      by_contra! h
      have hall := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot, hop] at hall
    change C.gates.length ≤ s at budget
    exact ⟨W, mono, by omega, correct⟩
  · refine ⟨C, ?_, budget, eval⟩
    intro g hg
    obtain ⟨ops, width⟩ := fit g hg
    have hnot : g.op ≠ GateOp.not := fun p => hn ⟨g, hg, p⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops
    refine ⟨?_, width⟩
    rcases ops with ha | ho | nt
    · simp [ha]
    · simp [ho]
    · exact False.elim (hnot nt)


def target : Sig := 0xaffffffffffffffff0000000000000000
def edgeFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 4004178568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def positions : Fin 6 → Row × Row := ![(4, 68), (1, 65), (128, 129), (2, 66), (3, 67), (130, 131)]
def wires : Fin 6 → Sig := ![0xcfffbffdfbf77eb7f0000000001f0000e, 0x3d65db4ebd5bab6d303f01f80fe0006d0, 0xe00000000000000000000000000000000, 0x39b6ed972e7dcfce4fc001fff000018e0, 0xe38f1e7cf9ef3f88ffffe00000001f00, 0x800000000000000000000000000000000]
def minorInputs : List Sig := [0xfffbffdfbf77eb7f0000000001f0000e, 0xd65db4ebd5bab6d303f01f80fe0006d0, 0x9b6ed972e7dcfce4fc001fff000018e0, 0xe38f1e7cf9ef3f88ffffe00000001f00]
def minorTarget : Sig := 0xffffffffffffffff0000000000000000
def shortCircuit : Circuit :=
  ⟨[⟨.or, [2, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 28000000 in
theorem exactTable : ∀ r : Row, edgeFn (sampled wires r) = bit r target := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 30000000 in
theorem exhausted : ∀ j : Fin 6, minorInputs.sublists.all
    (fun xs => !(boundedSearch minorTarget j.val xs)) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
theorem circuitCorrect : ∀ x : Fin 6 → Bool, shortCircuit.eval (List.ofFn x) = edgeFn x := by
  decide +kernel

end PEqualNP.Outside.L_meta_16487

open PEqualNP.Outside.L_meta_16487 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_16487 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004178568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4004178568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact no_inversion_projected wires (by decide +kernel) target
    (by unfold proper; decide +kernel) (by decide +kernel)
    exactTable positions (by decide +kernel) (by decide +kernel)
    minorInputs minorTarget 2 6 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) exhausted shortCircuit
    (by simp [shortCircuit, Monotone2]) (by decide +kernel) circuitCorrect
