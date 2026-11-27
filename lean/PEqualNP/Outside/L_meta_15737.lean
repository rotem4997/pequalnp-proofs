import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15737_aux

-- A wire records its values on the positive and negative members of 85 input pairs.

abbrev M := BitVec 85
abbrev Wire := M × M
namespace Wire
def zero : Wire := ⟨0,0⟩
def flip (u : Wire) : Wire := ⟨~~~u.1, ~~~u.2⟩
def meet (u v : Wire) : Wire := ⟨u.1 &&& v.1,u.2 &&& v.2⟩
def join (u v : Wire) : Wire := ⟨u.1 ||| v.1,u.2 ||| v.2⟩
def diff (u v : Wire) : Wire := meet u (flip v)
def ops (u v : Wire) := [meet u v,join u v,diff u v,diff v u]
def sig (u : Wire) := u.1 ^^^ u.2
def hit (u : Wire) := u.sig = (BitVec.allOnes 85)
def separates (u : Wire) (i : Fin 85) := u.1[i.val] ≠ u.2[i.val]
end Wire
open Wire

def allSig : List Wire → M
  | [] => 0
  | w::ws => w.sig ||| allSig ws

theorem allSig_bit (ws : List Wire) (i : Fin 85) :
    (allSig ws)[i.val] = true ↔ ∃ w ∈ ws, separates w i := by
  induction ws with
  | nil => simp [allSig]
  | cons u us ih =>
    simp [allSig, sig, separates] at ih ⊢
    exact or_congr_right ih

theorem hit_iff (u : Wire) : hit u ↔ ∀i : Fin 85, separates u i := by
  change u.sig = (BitVec.allOnes 85) ↔ _
  constructor
  · intro h i
    have hb : u.sig[i.val] = true := by rw [h]; exact BitVec.getElem_allOnes i.val i.isLt
    simpa [Wire.sig,Wire.separates] using hb
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hx := h ⟨i,hi⟩
    rw [BitVec.getElem_allOnes]
    simpa [Wire.sig,Wire.separates] using hx

theorem adequate (ws : List Wire) (h : ∀i : Fin 85, ∃ w ∈ws, separates w i) :
    allSig ws = (BitVec.allOnes 85) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_allOnes]
  exact (allSig_bit ws ⟨i,hi⟩).mpr (h _)

theorem sep_parent {a b c : Wire} (op : c∈ops a b) {i : Fin 85} (hs : separates c i) :
    separates a i ∨ separates b i := by
  by_contra! h
  simp [ops] at op
  rcases op with rfl|rfl|rfl|rfl <;>
    simp_all [separates,meet,join,diff,Wire.flip]

def Plan : ℕ → Finset Wire → Prop
  | 0, S => ∃ t : Wire, hit t ∧ S={t}
  | k+1, S => ∃ T a b c, Plan k T ∧ c∈T ∧ c∈ops a b ∧ c≠a ∧ c≠b ∧ c≠zero ∧ S=insert a (insert b (T.erase c))

theorem Plan.endAt (t : Wire) (yes : hit t) : Plan 0 {t} := ⟨t,yes,rfl⟩
theorem Plan.add {k T} (p : Plan k T) {a b c} (used : c∈T) (op : c∈ops a b) (fa : c≠a) (fb : c≠b) (nz : c≠zero) :
    Plan (k+1) (insert a (insert b (T.erase c))) := ⟨T,a,b,c,p,used,op,fa,fb,nz,rfl⟩

theorem Plan.byGates {C : (k : ℕ) → (S : Finset Wire) → Plan k S → Prop}
    (endAt : ∀(t : Wire) (h : hit t), C 0 {t} (Plan.endAt t h))
    (add : ∀{k T} (q : Plan k T) {a b c} (hu : c∈T) (ho : c∈ops a b) (fa : c≠a) (fb : c≠b) (nz : c≠zero),
      C k T q → C (k+1) (insert a (insert b (T.erase c))) (Plan.add q hu ho fa fb nz))
    {k S} (p : Plan k S) : C k S p := by
  induction k generalizing S with
  | zero => obtain ⟨t,h,rfl⟩ := p; exact endAt t h
  | succ k ih =>
    obtain ⟨T,a,b,c,q,h,op,fa,fb,nz,rfl⟩ := p
    exact add q h op fa fb nz (ih q)

theorem Plan.cardBound {k S} (p : Plan k S) : S.card ≤ k+1 := by
  induction p using Plan.byGates with
  | endAt => simp
  | @add k T _ a b c used op _ _ _ ih =>
    have h1 := Finset.card_insert_le a (insert b (T.erase c))
    have h2 := Finset.card_insert_le b (T.erase c)
    rw [Finset.card_erase_of_mem used] at h2
    have := Finset.card_pos.mpr ⟨c,used⟩
    omega

theorem Plan.cover {k S} (p : Plan k S) (i : Fin 85) : ∃ w∈S, separates w i := by
  induction p using Plan.byGates with
  | endAt t h => exact ⟨t,by simp,(hit_iff _).mp h i⟩
  | @add k T _ a b c used op _ _ _ ih =>
    obtain ⟨w,hw,sep⟩ := ih
    by_cases eq : w=c
    · subst w
      rcases sep_parent op sep with hs|hs
      · exact ⟨a,by simp,hs⟩
      · exact ⟨b,by simp,hs⟩
    · exact ⟨w,by simp [Finset.mem_erase,hw,eq],sep⟩

-- Trace the wires that a circuit output uses. Each binary gate can replace one live wire by two parents.

open Wire

def pairs : List Wire → List (Wire × Wire)
  | [] => []
  | x::xs => xs.map (fun y => (x,y)) ++ pairs xs

def drops (xs : List Wire) (a b : Wire) : List (List Wire) :=
  [xs,xs.filter (· != a),xs.filter (· != b),xs.filter (fun w=>w != a && w != b)]

def seek : ℕ → List Wire → Bool
  | 0, xs => xs.any (fun w => w.sig == (BitVec.allOnes 85))
  | k+1, xs =>
    xs.length ≤ k+2 && allSig xs == (BitVec.allOnes 85) &&
    (xs.any (fun w => w.sig == (BitVec.allOnes 85)) ||
      (pairs xs).any fun (a,b) => (ops a b).any fun c =>
        c != zero && !xs.contains c &&
        (drops xs a b).any fun keep => seek k (c::keep))
def pins : List Wire := [⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]

def probes : List (Nat × Nat) := [(3,2), (3,1), (5,4), (5,1), (7,6), (9,8), (9,1), (11,10), (13,12), (15,14), (19,18), (19,17), (21,20), (21,17), (22,20), (22,18), (22,6), (25,24), (25,17), (27,26), (29,28), (30,28), (30,26), (30,14), (35,34), (35,33), (37,36), (37,33), (38,36), (38,34), (38,6), (41,40), (41,33), (43,42), (45,44), (46,44), (46,42), (46,14), (51,50), (51,49), (53,52), (53,49), (54,52), (54,50), (57,56), (57,49), (58,56), (58,50), (58,42), (58,26), (61,60), (62,60), (3,14), (3,26), (3,42), (3,49), (3,50), (3,60), (5,14), (5,26), (5,42), (5,49), (5,50), (5,60), (9,14), (9,26), (9,42), (9,49), (9,50), (9,60), (22,14), (22,26), (22,42), (22,49), (22,50), (22,60), (38,14), (38,26), (38,42), (38,49), (38,50), (38,60), (58,14), (58,49), (58,60)]

def row (k : ℕ) (i : Fin 6) : Bool := k.testBit i.val

def probeP (j : Fin 85) : Fin 6 → Bool := row (probes.getD j.val (0,0)).1
def probeN (j : Fin 85) : Fin 6 → Bool := row (probes.getD j.val (0,0)).2
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008241896 * 2^32 + 3941116584) (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)

-- With input names a through f, the output is a(b + c + d) + b(c(e + f) + def), with + denoting OR.
def monoTen : Circuit :=
  ⟨[⟨.or,[1,2]⟩, ⟨.or,[6,3]⟩, ⟨.and,[0,7]⟩, ⟨.or,[4,5]⟩, ⟨.and,[2,9]⟩, ⟨.and,[4,5]⟩, ⟨.and,[3,11]⟩, ⟨.or,[10,12]⟩, ⟨.and,[1,13]⟩, ⟨.or,[8,14]⟩],15⟩

theorem tenMono : Monotone2 monoTen := by
  intro g hg
  simp [monoTen] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

theorem tenSize : monoTen.size = 10 := rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem tenEval : ∀ x : Fin 6 → Bool, monoTen.eval (List.ofFn x) = target x := by decide +kernel
open Wire

def phase (w a : Wire) := w=a ∨ w=a.flip
def known (pool : Finset Wire) (w : Wire) := phase w zero ∨ ∃a∈pool, phase w a
def hasPlan (pool : Finset Wire) (bound : ℕ) := ∃k ≤ bound, ∃S⊆pool, Plan k S

@[simp] theorem flipFlip (a : Wire) : a.flip.flip = a := by cases a; simp [Wire.flip]
theorem known_flip {S a} (h : known S a) : known S a.flip := by
  have sw {u v : Wire} (h : phase u v) : phase u.flip v := by
    rcases h with rfl|rfl
    · exact Or.inr rfl
    · exact Or.inl (flipFlip _)
  exact h.elim (fun c=>Or.inl (sw c)) (fun ⟨u,hu,ph⟩=> Or.inr ⟨u,hu,sw ph⟩)
theorem known_mono {S T : Finset Wire} (sub : S⊆T) {a} (h : known S a) : known T a :=
  h.elim Or.inl (fun ⟨v,hv,hh⟩=>Or.inr ⟨v,sub hv,hh⟩)
theorem zeroKnown {S} : known S zero := Or.inl (Or.inl rfl)

theorem meet_zero (u : Wire) : meet zero u = zero := by cases u; simp [meet,zero]
theorem meet_top (u : Wire) : meet zero.flip u = u := by cases u; unfold meet zero Wire.flip; congr 1 <;> exact BitVec.allOnes_and
theorem meet_comm (u v : Wire) : meet u v = meet v u := by simp [meet,BitVec.and_comm]
theorem join_flips (u v : Wire) : join u v = (meet u.flip v.flip).flip := by
  cases u; cases v; simp [meet,join,Wire.flip,BitVec.not_and]

def newGate (pool : Finset Wire) (z : Wire) :=
  ∃ a∈pool, ∃ b∈pool, ∃ c∈ops a b, phase z c

theorem meet_options {pool : Finset Wire} {u v : Wire} (hu : known pool u) (hv : known pool v) :
    known pool (meet u v) ∨ newGate pool (meet u v) := by
  rcases hu with (rfl|rfl)|⟨a,ha,hpa⟩
  · rw [meet_zero]; exact Or.inl zeroKnown
  · rw [meet_top]; exact Or.inl hv
  rcases hv with (rfl|rfl)|⟨b,hb,hpb⟩
  · rw [meet_comm,meet_zero]; exact Or.inl zeroKnown
  · rw [meet_comm,meet_top]; exact Or.inl (Or.inr ⟨a,ha,hpa⟩)
  right; refine ⟨a,ha,b,hb,?_⟩
  rcases hpa with rfl|rfl <;> rcases hpb with rfl|rfl
  · exact ⟨meet _ _,by simp [ops],Or.inl rfl⟩
  · exact ⟨diff _ _,by simp [ops],Or.inl rfl⟩
  · exact ⟨diff _ _,by simp [ops],Or.inl (meet_comm _ _)⟩
  · refine ⟨join a b,by simp [ops],Or.inr ?_⟩
    rw [join_flips,flipFlip]

theorem join_options {pool : Finset Wire} {u v : Wire} (hu : known pool u) (hv : known pool v) :
    known pool (join u v) ∨ newGate pool (join u v) := by
  rw [join_flips]
  rcases meet_options (known_flip hu) (known_flip hv) with h|⟨a,ha,b,hb,c,hc,ph⟩
  · exact Or.inl (known_flip h)
  · right; refine ⟨a,ha,b,hb,c,hc,?_⟩
    rcases ph with h|h
    · exact Or.inr (congrArg Wire.flip h)
    · exact Or.inl (by rw [h,flipFlip])

theorem contract {pool : Finset Wire} {k : ℕ} {z : Wire} (hz : ¬known pool z)
    {a b c : Wire} (ha : a ∈pool) (hb : b ∈pool) (op : c∈ops a b) (ph : phase z c)
    (later : hasPlan (insert c pool) k) : hasPlan pool (k+1) := by
  have nc : c∉pool := fun h=>hz (Or.inr ⟨c,h,ph⟩)
  have nz : c ≠ zero := by rintro rfl; exact hz (Or.inl ph)
  obtain ⟨m,mb,S,sub,p⟩ := later
  by_cases mem : c∈S
  · refine ⟨m+1,by omega,_,?_,Plan.add p mem op (by rintro rfl; exact nc ha)
      (by rintro rfl; exact nc hb) nz⟩
    intro x h
    simp only [Finset.mem_insert,Finset.mem_erase] at h
    rcases h with rfl|rfl|⟨ne,hx⟩
    · exact ha
    · exact hb
    · exact (Finset.mem_insert.mp (sub hx)).resolve_left ne
  · exact ⟨m,by omega,S,fun x hx=>(Finset.mem_insert.mp (sub hx)).resolve_left (by rintro rfl; exact mem hx),p⟩
open Wire PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def legal (g : Gate) : Prop := (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length ≤ 2
def cost (g : Gate) : ℕ := match g.op with | .and | .or => 1 | _ => 0
def count (gs : List Gate) := (gs.map cost).sum

def wordGate (gs : List Wire) (g : Gate) : Wire :=
  match g.inputs,g.op with
  | [],.or => zero
  | [],_ => zero.flip
  | i::_,.not => (gs.getD i zero).flip
  | [i],_ => gs.getD i zero
  | i::j::_,.and => meet (gs.getD i zero) (gs.getD j zero)
  | i::j::_,_ => join (gs.getD i zero) (gs.getD j zero)

def wordRun (gs : List Gate) (ws : List Wire) :=
  gs.foldl (fun acc g=>acc++[wordGate acc g]) ws

def side (neg : Bool) (i : Fin 85) (w : Wire) : Bool :=
  if neg then w.2[i.val] else w.1[i.val]

theorem known_at {pool : Finset Wire} {ws : List Wire} (hk : ∀w∈ws,known pool w) (i : ℕ) :
    known pool (ws.getD i zero) := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]; exact hk _ (List.getElem_mem ..)
  · rw [List.getD_eq_default _ _ (by omega)]; exact zeroKnown

theorem gate_options {pool : Finset Wire} {ws : List Wire} (hk : ∀w∈ws,known pool w)
    {g : Gate} (hg : legal g) : known pool (wordGate ws g) ∨ (cost g = 1 ∧ newGate pool (wordGate ws g)) := by
  rcases g with ⟨o,ins⟩
  obtain ⟨ho,hlen⟩ := hg
  change o = .and ∨ o = .or ∨ o = .not at ho
  change ins.length ≤ 2 at hlen
  cases ins with
  | nil =>
    rcases ho with rfl|rfl|rfl <;> first | exact Or.inl (known_flip zeroKnown) | exact Or.inl zeroKnown
  | cons i tail =>
    cases tail with
    | nil =>
      rcases ho with rfl|rfl|rfl <;> first | exact Or.inl (known_at hk i) | exact Or.inl (known_flip (known_at hk i))
    | cons j tail =>
      rcases ho with rfl|rfl|rfl
      · exact (meet_options (known_at hk i) (known_at hk j)).imp_right (fun h=>⟨rfl,h⟩)
      · exact (join_options (known_at hk i) (known_at hk j)).imp_right (fun h=>⟨rfl,h⟩)
      · exact Or.inl (known_flip (known_at hk i))

theorem sideGate (n : Bool) (i : Fin 85) (ws : List Wire) {g : Gate} (hg : legal g) :
    side n i (wordGate ws g) = g.op.eval (g.inputs.map fun j=>(ws.map (side n i)).getD j false) := by
  have hzero : side n i zero = false := by cases n <;> simp [side,zero]
  have atI (j : ℕ) : (ws.map (side n i)).getD j false = side n i (ws.getD j zero) := by
    rw [←hzero]; exact List.getD_map _ _ _
  simp only [atI]
  rcases g with ⟨o,ins⟩
  obtain ⟨ho,hlen⟩ := hg
  change o = .and ∨ o = .or ∨ o = .not at ho
  change ins.length ≤ 2 at hlen
  cases ins with
  | nil =>
    rcases ho with rfl|rfl|rfl <;> cases n <;> simp [wordGate,side,zero,Wire.flip,GateOp.eval] <;> exact BitVec.getElem_allOnes i.val i.isLt
  | cons a l =>
    cases l with
    | nil =>
      rcases ho with rfl|rfl|rfl <;> cases n <;> simp [wordGate,side,Wire.flip,GateOp.eval]
    | cons b t =>
      have : t=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst t
      rcases ho with rfl|rfl|rfl <;> cases n <;> simp [wordGate,side,Wire.flip,meet,join,GateOp.eval]

theorem sideRun (n : Bool) (i : Fin 85) (gs : List Gate) (ws : List Wire) (leg : ∀g∈gs,legal g) :
    (wordRun gs ws).map (side n i) =
    gs.foldl (fun v g=>v++[g.op.eval (g.inputs.map fun j=>v.getD j false)]) (ws.map (side n i)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change (wordRun gs (ws++[wordGate ws g])).map _ = _
    rw [ih _ (fun h hh=>leg h (by simp [hh]))]
    simp [sideGate n i ws (leg g (by simp))]

theorem fromRun (gs : List Gate) (pool : Finset Wire) (ws : List Wire) (out : ℕ)
    (hk : ∀w∈ws,known pool w) (leg : ∀g∈gs,legal g)
    (hwin : hit ((wordRun gs ws).getD out zero)) : hasPlan pool (count gs) := by
  induction gs generalizing pool ws with
  | nil =>
    change hit (ws.getD out zero) at hwin
    have hsignal (u : Wire) : u.flip.sig = u.sig := by
      cases u; apply BitVec.eq_of_getElem_eq; intro i hi; simp [sig,Wire.flip]
    have t0 : ¬hit zero := by change ¬((0 : M) = BitVec.allOnes 85); decide
    rcases known_at hk out with (h|h)|⟨u,hu,ph⟩
    · exact (t0 (h ▸ hwin)).elim
    · rw [h] at hwin; exact (t0 (by simpa [hit,hsignal] using hwin)).elim
    · have uhit : hit u := by
        rcases ph with h|h
        · rwa [h] at hwin
        · rw [h] at hwin; simpa only [hit,hsignal] using hwin
      exact ⟨0,by decide,_,Finset.singleton_subset_iff.mpr hu,Plan.endAt u uhit⟩
  | cons g gs ih =>
    let z := wordGate ws g
    have tail := fun u (h:u∈gs) => leg u (by simp [h])
    change hit ((wordRun gs (ws++[z])).getD out zero) at hwin
    change hasPlan pool (cost g + count gs)
    by_cases already : known pool z
    · obtain ⟨k,h,S,hs,hp⟩ := ih pool (ws++[z]) (by intro w hw; rcases List.mem_append.mp hw with h|h; exact hk w h; simp only [List.mem_singleton] at h; exact h ▸ already) tail hwin
      exact ⟨k,by omega,S,hs,hp⟩
    · rcases gate_options hk (leg g (by simp)) with h|⟨cg,a,ha,b,hb,c,hc,ph⟩
      · exact (already h).elim
      have kn : known (insert c pool) z := Or.inr ⟨c,by simp,ph⟩
      have sub : pool ⊆ insert c pool := Finset.subset_insert _ _
      have base : ∀w∈ws,known (insert c pool) w := fun w hw => known_mono sub (hk w hw)
      have more := ih (insert c pool) (ws++[z]) (by intro w hw; rcases List.mem_append.mp hw with h|h; exact base w h; simp only [List.mem_singleton] at h; exact h ▸ kn) tail hwin
      simpa [cg,Nat.add_comm] using contract already ha hb hc ph more
open Wire

theorem pairs_mem {a b : Wire} {xs : List Wire} (ha : a ∈xs) (hb : b ∈xs) (ne : a≠b) :
    (a,b)∈pairs xs ∨ (b,a)∈pairs xs := by
  induction xs with
  | nil => simp at ha
  | cons u us ih =>
    by_cases e : a=u
    · subst u
      left
      simp [pairs, (List.mem_cons.mp hb).resolve_left (Ne.symm ne)]
    by_cases f : b=u
    · subst u
      right
      simp [pairs, (List.mem_cons.mp ha).resolve_left ne]
    rcases ih ((List.mem_cons.mp ha).resolve_left e) ((List.mem_cons.mp hb).resolve_left f) with l|r
    · exact Or.inl (List.mem_append_right _ l)
    · exact Or.inr (List.mem_append_right _ r)

theorem ops_swap (a b c : Wire) : c∈ops a b ↔ c∈ops b a := by
  have andComm : meet a b = meet b a := by simp [meet,BitVec.and_comm]
  have orComm : join a b = join b a := by simp [join,BitVec.or_comm]
  simp only [ops,List.mem_cons,andComm,orComm]
  tauto

theorem noLoop {a c : Wire} (h : c∈ops a a) (n : c≠zero) : c=a := by
  have x : meet a a = a := by cases a; simp [meet]
  have y : join a a = a := by cases a; simp [join]
  have z : diff a a = zero := by cases a; simp [diff,meet,Wire.flip,zero]
  simpa [ops,x,y,z,n] using h

theorem getDrops {xs : List Wire} {K : Finset Wire} {a b : Wire}
    (h : xs.toFinset = insert a (insert b K)) (nd : xs.Nodup) :
    ∃ ys∈drops xs a b, ys.toFinset=K ∧ ys.Nodup := by
  have spec (w : Wire) : w∈xs ↔ w=a ∨ w=b ∨ w∈K := by
    rw [←List.mem_toFinset,h]; simp
  by_cases ha : a∈K <;> by_cases hb : b∈K
  · exact ⟨xs,by simp [drops],by simpa [ha,hb] using h,nd⟩
  · refine ⟨xs.filter (· != b),by simp [drops],?_,nd.filter _⟩
    ext w
    simp only [List.mem_toFinset,List.mem_filter,bne_iff_ne,spec]
    grind
  · refine ⟨xs.filter (· != a),by simp [drops],?_,nd.filter _⟩
    ext w
    simp only [List.mem_toFinset,List.mem_filter,bne_iff_ne,spec]
    grind
  · refine ⟨xs.filter (fun w=>w != a && w != b),by simp [drops],?_,nd.filter _⟩
    ext w
    simp only [List.mem_toFinset,List.mem_filter,Bool.and_eq_true,bne_iff_ne,spec]
    grind

theorem Plan.found {m : ℕ} {S : Finset Wire} (p : Plan m S) {k : ℕ} (bound : m≤k)
    (xs : List Wire) (eq : xs.toFinset=S) (nd : xs.Nodup) : seek k xs = true := by
  have guardCard : xs.length ≤ k+1 := by
    have h := p.cardBound
    rw [←eq,List.toFinset_card_of_nodup nd] at h
    omega
  have guardMask : allSig xs = (BitVec.allOnes 85) := by
    apply adequate
    intro i
    obtain ⟨w,hw,s⟩ := p.cover i
    exact ⟨w, List.mem_toFinset.mp (eq.symm ▸ hw),s⟩
  induction p using Plan.byGates generalizing k xs with
  | endAt t ht =>
    have mem : t ∈ xs := by apply List.mem_toFinset.mp; rw [eq]; simp
    have hit' : xs.any (fun w=>w.sig == (BitVec.allOnes 85)) = true := List.any_eq_true.mpr ⟨t,mem,by simpa [hit] using ht⟩
    cases k with
    | zero => exact hit'
    | succ k => simp only [seek,decide_eq_true guardCard, guardMask, beq_self_eq_true, hit', Bool.true_or, Bool.true_and]
  | @add m T p a b c used op fa fb nz ih =>
    cases k with
    | zero => omega
    | succ k =>
      have bank (z : Wire) : z∈xs ↔ z=a ∨ z=b ∨ z∈T.erase c := by
        rw [←List.mem_toFinset,eq]; simp
      have nc : c ∉ xs := by simp [bank,fa,fb]
      have ne : a≠b := by rintro rfl; exact fa (noLoop op nz)
      have advance (a' b' : Wire) (heq : xs.toFinset=insert a' (insert b' (T.erase c)))
          (legal : c∈ops a' b') : ((ops a' b').any fun d =>
          d != zero && !xs.contains d && (drops xs a' b').any fun keep => seek k (d::keep)) = true := by
        obtain ⟨ys,hy,ey,dy⟩ := getDrops heq nd
        have cy : c∉ys := by intro h; have := List.mem_toFinset.mpr h; simp [ey] at this
        have en : (c::ys).toFinset = T := by simp [ey,Finset.insert_erase used]
        have dn : (c::ys).Nodup := List.nodup_cons.mpr ⟨cy,dy⟩
        have hn : seek k (c::ys) = true := ih (by omega) _ en dn (by
          rw [←List.toFinset_card_of_nodup dn,en]; have := p.cardBound; omega) (by
          apply adequate; intro i; obtain ⟨z,hz,sz⟩ := p.cover i
          exact ⟨z,List.mem_toFinset.mp (en.symm ▸ hz),sz⟩)
        apply List.any_eq_true.mpr
        refine ⟨c,legal,?_⟩
        simp [nz,nc,List.any_eq_true]
        exact ⟨ys,hy,hn⟩
      simp only [seek,decide_eq_true guardCard,guardMask,beq_self_eq_true,Bool.true_and,Bool.or_eq_true]
      right
      apply List.any_eq_true.mpr
      rcases pairs_mem ((bank a).2 (Or.inl rfl)) ((bank b).2 (Or.inr (Or.inl rfl))) ne with h|h
      · exact ⟨_,h,advance a b eq op⟩
      · exact ⟨_,h,advance b a (by rw [eq,Finset.insert_comm]) ((ops_swap ..).1 op)⟩

-- Search the possible parents, discarding sets that are too large or fail to separate an input pair.

open Wire
def enough (k : ℕ) (xs : List Wire) : Bool :=
  decide (xs.length ≤ k+1) && (allSig xs == BitVec.allOnes 85)

def kids (k : ℕ) (xs : List Wire) : List (List Wire) :=
  (pairs xs).flatMap fun (a,b) => (ops a b).flatMap fun c =>
    if c ≠ zero ∧ c ∉ xs then
      ((drops xs a b).map (c::·)).filter (enough k)
    else []

open Wire

theorem mustCover {k} {xs : List Wire} (hk : 0<k) (found : seek k xs=true) : enough k xs = true := by
  cases k with
  | zero => contradiction
  | succ k =>
    simp only [seek,Bool.and_eq_true] at found
    exact Bool.and_eq_true_iff.mpr found.1

open Wire

def wireEq (a b : Wire) := a.1 == b.1 && a.2 == b.2

def quick : ℕ → List Wire → Bool
  | 0, xs => xs.any (fun w=>w.sig == BitVec.allOnes 85)
  | k+1,xs =>
    enough (k+1) xs && (xs.any (fun w=>w.sig == BitVec.allOnes 85) ||
      (pairs xs).any fun (a,b) =>
        let ds := (ops a b).filter (fun c=> !(wireEq c zero) && !(xs.any (wireEq c)))
        (drops xs a b).any fun keep =>
          (k==0 || decide (keep.length ≤ k)) &&
          let cover := allSig keep
          ds.any fun c =>
            (k==0 || ((c.sig ||| cover) == BitVec.allOnes 85)) && quick k (c::keep))
open Wire
theorem wireEq_true (a b : Wire) : wireEq a b=true ↔ a=b := by
  cases a; cases b; simp [wireEq]
theorem quickCovers (k : ℕ) (xs : List Wire) (h : seek k xs=true) : quick k xs=true := by
  induction k generalizing xs with
  | zero => exact h
  | succ k ih =>
    have ok := mustCover (Nat.zero_lt_succ k) h
    simp only [seek,Bool.and_eq_true,Bool.or_eq_true,List.any_eq_true] at h
    simp only [quick,ok,Bool.true_and,Bool.or_eq_true]
    rcases h.2 with hit|rest
    · exact Or.inl (List.any_eq_true.mpr hit)
    right
    obtain ⟨ab,hab,c,hc,⟨nz,nx⟩,keep,hkeep,yes⟩ := rest
    apply List.any_eq_true.mpr
    refine ⟨ab,hab,List.any_eq_true.mpr ⟨keep,hkeep,?_⟩⟩
    have cz : c≠zero := by simpa using nz
    have fresh : c∉xs := by simpa using nx
    have good : (!(wireEq c zero) && !(xs.any (wireEq c)))=true := by
      simp [←Bool.not_eq_true,wireEq_true,List.any_eq_true,cz,fresh]
    have legal : c ∈ (ops ab.1 ab.2).filter (fun w=> !(wireEq w zero) && !(xs.any (wireEq w))) := List.mem_filter.mpr ⟨hc,good⟩
    have room : k=0 ∨ (keep.length ≤ k ∧ c.sig ||| allSig keep = BitVec.allOnes 85) := by
      cases k with
      | zero => exact Or.inl rfl
      | succ k =>
        have yes' := mustCover (Nat.zero_lt_succ k) yes
        right
        simpa only [enough,List.length_cons,Nat.add_le_add_iff_right,allSig,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using yes'
    apply Bool.and_eq_true_iff.mpr
    constructor
    · rcases room with rfl|⟨len,_⟩ <;> simp [*]
    · apply List.any_eq_true.mpr
      refine ⟨c,legal,Bool.and_eq_true_iff.mpr ⟨?_,ih _ yes⟩⟩
      rcases room with rfl|⟨_,cov⟩ <;> simp [*]
theorem noSeekOfQuick {k xs} (h : quick k xs=false) : seek k xs=false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  have contra := quickCovers _ _ yes
  rw [h] at contra; contradiction
theorem noPoolOfQuick {k} {pool : List Wire} (h : pool.sublists.any (quick k)=false) :
    pool.sublists.any (seek k)=false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  obtain ⟨xs,mem,win⟩ := List.any_eq_true.mp yes
  have t := List.any_eq_true.mpr (show ∃x∈pool.sublists,quick k x=true from ⟨xs,mem,quickCovers k xs win⟩)
  rw [h] at t; contradiction

-- Restricting the input pairs can make live wires constant. Each such wire reduces the remaining gate budget.

open Wire

def fill (m : M) (j : Fin 85) (x : M) : M := if x[j.val] then x ||| ~~~m else x &&& m
def restrict (m : M) (j : Fin 85) (w : Wire) : Wire := ⟨fill m j w.1,fill m j w.2⟩

open Wire

abbrev constant (w : Wire) : Prop := w = zero ∨ w = zero.flip
theorem known_empty {w : Wire} : known ∅ w ↔ constant w := by simp [known,phase,constant]
theorem hit_not_const {w : Wire} (h : hit w) : ¬constant w := by
  rintro (rfl|rfl) <;> simp [hit,sig,zero,Wire.flip] at h

theorem op_known {S : Finset Wire} {a b c : Wire} (legal : c∈ops a b)
    (ka : known S a) (kb : known S b) : known S c ∨ newGate S c := by
  simp [ops] at legal
  rcases legal with rfl|rfl|rfl|rfl
  · exact meet_options ka kb
  · exact join_options ka kb
  · exact meet_options ka (known_flip kb)
  · exact meet_options kb (known_flip ka)

theorem meet_c_known {S : Finset Wire} {a b : Wire} (ca : constant a)
    (kb : known S b) : known S (meet a b) := by
  rcases ca with rfl|rfl
  · rw [meet_zero]; exact zeroKnown
  · rw [meet_top]; exact kb

theorem flip_c {a : Wire} (h : constant a) : constant a.flip := known_empty.1 (known_flip (known_empty.2 h))

theorem op_c_known {S : Finset Wire} {a b c : Wire} (h : c∈ops a b)
    (ka : known S a) (kb : known S b) (cp : constant a ∨ constant b) : known S c := by
  have mc {x y : Wire} (kx : known S x) (ky : known S y) (cc : constant x ∨ constant y) :
      known S (meet x y) := by
    rcases cc with z|z
    · exact meet_c_known z ky
    · rw [meet_comm]; exact meet_c_known z kx
  simp [ops] at h
  rcases h with rfl|rfl|rfl|rfl
  · exact mc ka kb cp
  · rw [join_flips]; exact known_flip (mc (known_flip ka) (known_flip kb) (cp.imp flip_c flip_c))
  · exact mc ka (known_flip kb) (cp.imp_right flip_c)
  · exact mc kb (known_flip ka) (cp.symm.imp_right flip_c)

def fee (φ : Wire→Wire) (S : Finset Wire) : ℕ := ∑w∈S, if constant (φ w) then 1 else 0
theorem fee_ins (φ : Wire→Wire) (w : Wire) (S : Finset Wire) :
    fee φ (insert w S) ≤ fee φ S + (if constant (φ w) then 1 else 0) := by
  by_cases h : w∈S
  · simp [h]
  · unfold fee; rw [Finset.sum_insert h,Nat.add_comm]
theorem fee_erase {φ : Wire→Wire} {w : Wire} {S : Finset Wire} (h : w∈S) :
    fee φ (S.erase w) + (if constant (φ w) then 1 else 0) = fee φ S := by
  exact Finset.sum_erase_add _ _ h

theorem Plan.project {φ : Wire→Wire}
    (hits : ∀w,hit w → hit (φ w))
    (opsMap : ∀a b c,c∈ops a b → φ c∈ops (φ a) (φ b))
    {m S} (h : Plan m S) (pool : Finset Wire) (available : ∀w∈S,known pool (φ w)) :
    ∃k, k+fee φ S ≤ m ∧ hasPlan pool k := by
  induction h using Plan.byGates generalizing pool with
  | endAt t ht =>
    have good := hits t ht
    have nc := hit_not_const good
    rcases available t (by simp) with hc|⟨a,ha,ph⟩
    · exact (nc hc).elim
    have ga : hit a := by
      rcases ph with e|e
      · rwa [e] at good
      · rw [e] at good
        have hs : a.flip.sig=a.sig := by
          cases a; apply BitVec.eq_of_getElem_eq; intro i hi; simp [sig,Wire.flip]
        simpa only [hit,hs] using good
    exact ⟨0,by simp only [fee,Finset.sum_singleton,ite_eq_right nc,Nat.zero_add,Nat.le_refl],0,by decide,_,Finset.singleton_subset_iff.mpr ha,Plan.endAt a ga⟩
  | @add m T p a b c used op _ _ _ ih =>
    have ka := available a (by simp)
    have kb := available b (by simp)
    have oc := opsMap _ _ _ op
    have ca := fee_ins φ a (insert b (T.erase c))
    have cb := fee_ins φ b (T.erase c)
    have ce := fee_erase (φ:=φ) used
    have rest : ∀w∈T.erase c, known pool (φ w) := fun w hw => available w (by simp [hw])
    by_cases kc : known pool (φ c)
    · obtain ⟨k,low,plan⟩ := ih pool (fun w hw=>by
        by_cases e : w=c
        · simpa [e] using kc
        · exact rest _ (Finset.mem_erase.mpr ⟨e,hw⟩))
      refine ⟨k,?_,plan⟩
      have both (h : constant (φ a)) (j : constant (φ b)) : constant (φ c) :=
        known_empty.mp (op_c_known oc (known_empty.mpr h) (known_empty.mpr j) (Or.inl h))
      by_cases a0 : constant (φ a) <;> by_cases b0 : constant (φ b) <;> by_cases c0 : constant (φ c) <;>
        simp [a0,b0,c0] at ca cb ce <;> first | omega | exact (c0 (both a0 b0)).elim
    · obtain ⟨u,hu,v,hv,d,od,ph⟩ := (op_known oc ka kb).resolve_left kc
      have na : ¬constant (φ a) := fun e=>kc (op_c_known oc ka kb (Or.inl e))
      have nb : ¬constant (φ b) := fun e=>kc (op_c_known oc ka kb (Or.inr e))
      obtain ⟨k,low,plan⟩ := ih (insert d pool) (fun w hw=>by
        by_cases e : w=c
        · subst w; exact Or.inr ⟨d,by simp,ph⟩
        · exact known_mono (Finset.subset_insert ..) (rest _ (Finset.mem_erase.mpr ⟨e,hw⟩)))
      refine ⟨k+1,?_,contract kc hu hv od ph plan⟩
      simp only [ite_eq_right na,ite_eq_right nb,Nat.add_zero] at ca cb
      omega

theorem fill_bit (m x : M) (i j : Fin 85) :
    (fill m j x)[i.val] = if m[i.val] then x[i.val] else x[j.val] := by
  cases a : x[j.val] <;> cases b : m[i.val] <;> simp [fill,a,b]

theorem restrict_hits (m : M) (j : Fin 85) (w : Wire) (h : hit w) : hit (restrict m j w) := by
  apply (hit_iff _).2
  intro i
  change (fill m j w.1)[i.val] ≠ (fill m j w.2)[i.val]
  rw [fill_bit,fill_bit]
  split
  · exact (hit_iff _).1 h i
  · exact (hit_iff _).1 h j

theorem restrict_ops (m : M) (j : Fin 85) (a b c : Wire) (h : c∈ops a b) :
    restrict m j c ∈ ops (restrict m j a) (restrict m j b) := by
  have AND (x y : M) : fill m j (x &&& y) = fill m j x &&& fill m j y := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    have eq (v : M) := fill_bit m v ⟨i,hi⟩ j
    simp only [BitVec.getElem_and,eq]; split <;> rfl
  have OR (x y : M) : fill m j (x ||| y) = fill m j x ||| fill m j y := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    have eq (v : M) := fill_bit m v ⟨i,hi⟩ j
    simp only [BitVec.getElem_or,eq]; split <;> rfl
  have NOT (x : M) : fill m j (~~~x) = ~~~fill m j x := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    have eq (v : M) := fill_bit m v ⟨i,hi⟩ j
    simp only [BitVec.getElem_not,eq]; split <;> rfl
  simp [ops] at h ⊢
  rcases h with rfl|rfl|rfl|rfl <;> simp [restrict,meet,join,diff,Wire.flip,AND,OR,NOT]

-- Each branch is ruled out by a direct search or by a search on a restriction.

open Wire
def NoPlan (k : ℕ) (xs : List Wire) : Prop := ∀m ≤ k, ¬Plan m xs.toFinset
def recognized (bank : List Wire) (w : Wire) : Bool :=
  w==zero || w==zero.flip || bank.any (fun a=>w==a || w==a.flip)
open Wire

theorem Plan.peel {m S} (p : Plan (m+1) S) {k : ℕ} (bound : m≤k)
    (xs : List Wire) (eq : xs.toFinset=S) (nd : xs.Nodup) :
    ∃ys∈kids k xs, ys.Nodup ∧ Plan m ys.toFinset := by
  obtain ⟨T,a,b,c,pt,used,op,fa,fb,nz,rfl⟩ := p
  have bank (z : Wire) : z∈xs ↔ z=a ∨ z=b ∨ z∈T.erase c := by
    rw [←List.mem_toFinset,eq]; simp
  have nc : c∉xs := by simp [bank,fa,fb]
  have ne : a≠b := by rintro rfl; exact fa (noLoop op nz)
  have makeChild (a' b' : Wire) (heq : xs.toFinset=insert a' (insert b' (T.erase c)))
      (leg : c∈ops a' b') (hm : (a',b') ∈ pairs xs) : ∃ys∈kids k xs, ys.Nodup ∧ Plan m ys.toFinset := by
    obtain ⟨ys,hy,ey,dy⟩ := getDrops heq nd
    have cy : c∉ys := by intro h; have := List.mem_toFinset.mpr h; simp [ey] at this
    have en : (c::ys).toFinset = T := by simp [ey,Finset.insert_erase used]
    have dn := List.nodup_cons.mpr ⟨cy,dy⟩
    have hc : (c::ys).length ≤ k+1 := by
      rw [←List.toFinset_card_of_nodup dn,en]; have := pt.cardBound; omega
    have hs : allSig (c::ys) = BitVec.allOnes 85 := by
      apply adequate; intro i; obtain ⟨w,hw,sep⟩ := pt.cover i
      exact ⟨w,List.mem_toFinset.mp (en.symm ▸ hw),sep⟩
    refine ⟨c::ys,?_,dn,en.symm ▸ pt⟩
    apply List.mem_flatMap.mpr; refine ⟨(a',b'),hm,?_⟩
    apply List.mem_flatMap.mpr; refine ⟨c,leg,?_⟩
    rw [ite_eq_left (And.intro nz nc)]
    exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_,hy,rfl⟩,by simp only [enough,decide_eq_true hc,hs,beq_self_eq_true,Bool.true_and]⟩
  rcases pairs_mem ((bank a).2 (Or.inl rfl)) ((bank b).2 (Or.inr (Or.inl rfl))) ne with h|h
  · exact makeChild a b eq op h
  · exact makeChild b a (by rw [eq,Finset.insert_comm]) ((ops_swap ..).1 op) h

theorem hasPlanSearch {xs : List Wire} (nd : xs.Nodup) {k} (p : hasPlan xs.toFinset k) :
    xs.sublists.any (seek k) = true := by
  classical
  obtain ⟨m,mb,S,ss,pl⟩ := p
  let ys := xs.filter fun w=>w∈S
  have eq : ys.toFinset=S := by
    ext w
    simp only [ys,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun h=>⟨List.mem_toFinset.mp (ss h),h⟩⟩
  exact List.any_eq_true.mpr ⟨ys,List.mem_sublists.mpr (List.filter_sublist ..),pl.found mb ys eq (nd.filter _)⟩

theorem recognized_iff {xs : List Wire} {w : Wire} : recognized xs w = true ↔ known xs.toFinset w := by
  simp [recognized,known,phase]

theorem const_length (φ : Wire→Wire) (xs : List Wire) (nd : xs.Nodup) :
    (xs.filter (fun w => let t := φ w; t==zero || t==zero.flip)).length = fee φ xs.toFinset := by
  induction xs with
  | nil => simp [fee]
  | cons a xs ih =>
    obtain ⟨ne,dt⟩ := List.nodup_cons.mp nd
    have notin : a ∉xs.toFinset := by simpa using ne
    rw [List.toFinset_cons]
    unfold fee at *
    rw [Finset.sum_insert notin]
    by_cases h : constant (φ a)
    · have hb : (φ a==zero || φ a==zero.flip)=true := by simpa [constant] using h
      simp [hb,h,ih dt,Nat.add_comm]
    · have hb : (φ a==zero || φ a==zero.flip)=false := by simpa [constant,not_or] using h
      simp [hb,h,ih dt]

def applies (mask : M) (j : Fin 85) (bank : List Wire) (budget k : ℕ) (xs : List Wire) : Bool :=
  decide (k ≤ budget + (xs.filter (fun w => let t := restrict mask j w; t==zero || t==zero.flip)).length) &&
    xs.all (fun w=>recognized bank (restrict mask j w))

theorem banByRestriction {mask j bank budget k xs} (nodup : bank.Nodup) (ban : bank.sublists.any (quick budget)=false)
    (nd : xs.Nodup) (active : applies mask j bank budget k xs=true) : NoPlan k xs := by
  intro m upper pl
  simp only [applies,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at active
  have avail : ∀w∈xs.toFinset,known bank.toFinset (restrict mask j w) :=
    fun w hw=>recognized_iff.mp (active.2 w (List.mem_toFinset.mp hw))
  obtain ⟨q,low,has⟩ := pl.project (restrict_hits mask j) (restrict_ops mask j) bank.toFinset avail
  have qr : q≤budget := by have aux := active.1; rw [const_length _ _ nd] at aux; omega
  obtain ⟨n,nh,S,sub,plan⟩ := has
  have yes := hasPlanSearch nodup (k:=budget) ⟨n,by omega,S,sub,plan⟩
  rw [noPoolOfQuick ban] at yes; contradiction


theorem banBySearch {k xs} (nd : xs.Nodup) (h : quick k xs = false) : NoPlan k xs := by
  intro m hm p
  have t := quickCovers k xs (p.found hm xs rfl nd)
  rw [h] at t
  contradiction

theorem banBySplit {k xs} (nd : xs.Nodup) (miss : xs.any (fun w=>w.sig == BitVec.allOnes 85)=false)
    (h : ∀ys∈kids k xs, NoPlan k ys) : NoPlan (k+1) xs := by
  intro m hm p
  cases m with
  | zero =>
    obtain ⟨t,win,e⟩ := p
    have mem : t∈xs := by apply List.mem_toFinset.mp; rw [e]; simp
    have yes := List.any_eq_true.mpr (show ∃w∈xs,(w.sig == BitVec.allOnes 85)=true from ⟨_,mem,by simpa [hit] using win⟩)
    rw [miss] at yes; contradiction
  | succ m =>
    obtain ⟨ys,mem,_,py⟩ := p.peel (k:=k) (by omega) xs rfl nd
    exact h ys mem m (by omega) py

-- The 70 lists below are the possible frontiers after the first binary gate. Their enumeration is checked below.

def frontier0 : List Wire := [⟨0x3f000c203080e93#85,0x0#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier1 : List Wire := [⟨0x1fffffffffffffffffffff#85,0xdf7df7df3aaf36bcdaedb#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier2 : List Wire := [⟨0x3ffc0433058c16316c#85,0x88208208022810a04284a#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier3 : List Wire := [⟨0x1fffc0000bcc3870e1c000#85,0x575d75d73887261c98691#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier4 : List Wire := [⟨0xfc0403040c10331c#85,0x0#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier5 : List Wire := [⟨0x3fffffffc3fffffffffff#85,0x1e9a69a69c27ad5eb57b5e#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier6 : List Wire := [⟨0x3f03f030c3830e0ce3#85,0x88208208022810a04284a#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier7 : List Wire := [⟨0x3ffc000080c3870e1c000#85,0x161861861c052c54b15314#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier8 : List Wire := [⟨0x3f00043007801e03e0#85,0x0#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier9 : List Wire := [⟨0x1c003ffffff3ff8ffe3fff#85,0x1efbefbeff72bf8afe2bea#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier10 : List Wire := [⟨0xfff003c00f003c1f#85,0x88208208022810a04284a#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier11 : List Wire := [⟨0x1c0000000bc03800e00000#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier12 : List Wire := [⟨0x433c0001e3c00#85,0x882082080228000042800#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier13 : List Wire := [⟨0x1c0fffffffffc78fffffff#85,0x1baebaebaeffc10a7efc4a#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier14 : List Wire := [⟨0x1c0fffffffffc78fffffff#85,0x1baebaebaeffc10a7efc4a#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier15 : List Wire := [⟨0x3ffff000078f0003ff#85,0x10a00004a#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier16 : List Wire := [⟨0x1c0fc0000bcc0000e1c000#85,0x132cb2cb2edd40007ad400#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier17 : List Wire := [⟨0x1c0fc0000bcc0000e1c000#85,0x132cb2cb2edd40007ad400#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier18 : List Wire := [⟨0x433c78f000000#85,0x88208208022810a000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier19 : List Wire := [⟨0x1ff03fffffffffff1e3fff#85,0x1bcf3cf3cdffdfbf04284a#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier20 : List Wire := [⟨0x1ff03fffffffffff1e3fff#85,0x1bcf3cf3cdffdfbf04284a#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩]
def frontier21 : List Wire := [⟨0x3ffff00000001e3fff#85,0x4284a#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier22 : List Wire := [⟨0x1ff000000bcc3870000000#85,0x134d34d34ddd5eb5000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier23 : List Wire := [⟨0x1ff000000bcc3870000000#85,0x134d34d34ddd5eb5000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩]
def frontier24 : List Wire := [⟨0x3ffc000080c3870e1c210#85,0x410410410002040810210#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier25 : List Wire := [⟨0x1fffc0ffffcffe7ff9ff9f#85,0x177df7df7f8d7e75f9d795#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier26 : List Wire := [⟨0x1c000003f3c0c203080c83#85,0x165965963885221488481#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier27 : List Wire := [⟨0xfc0403040c10310c#85,0x120820820c050c14305104#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier28 : List Wire := [⟨0x1c0000000bc03a00e80280#85,0x471c71c73003200c80280#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier29 : List Wire := [⟨0x1fffff03fffcfff3ffcff3#85,0x177df7df7fd87ee1fb87b1#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier30 : List Wire := [⟨0x3ffc003f00cc07301cc13#85,0x104104100884061018411#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier31 : List Wire := [⟨0x3f0004300580160160#85,0x120820820c500c80320120#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier32 : List Wire := [⟨0x1c0fc0000bccc000e9cc00#85,0x124924922884000488400#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier33 : List Wire := [⟨0x1c0fc0000bccc000e9cc00#85,0x124924922884000488400#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier34 : List Wire := [⟨0x1fffc003fffffa73fffe93#85,0x1ffffffffffff261fffe91#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier35 : List Wire := [⟨0x3f00003f0003a73000293#85,0x451451451003261810291#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier36 : List Wire := [⟨0x3f00003f0003a73000293#85,0x451451451003261810291#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier37 : List Wire := [⟨0x4330000163000#85,0x1a8a28a28c778000367800#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier38 : List Wire := [⟨0x1ff000000bccfa73000000#85,0x145145141885221000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier39 : List Wire := [⟨0x1ff000000bccfa73000000#85,0x145145141885221000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩]
def frontier40 : List Wire := [⟨0x1fffc003ffffffffe9ce93#85,0x1fffffffffffffffc98691#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier41 : List Wire := [⟨0xfc003f0000000e9ce93#85,0x430c30c32002040c98691#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier42 : List Wire := [⟨0xfc003f0000000e9ce93#85,0x430c30c32002040c98691#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩]
def frontier43 : List Wire := [⟨0x433058c000000#85,0x1a8a28a28c778d9e000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier44 : List Wire := [⟨0xc003c00f00300#85,0x161861861c002c00b00300#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier45 : List Wire := [⟨0x1ffffffc0fff3ffcfff3fc#85,0x1679e79e7f553ed4fb53b4#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier46 : List Wire := [⟨0x1ffffffc0fff3ffcfff3fc#85,0x1679e79e7f553ed4fb53b4#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier47 : List Wire := [⟨0x3ffc0fc000f007c01f01c#85,0x50054015014#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier48 : List Wire := [⟨0x1c003f0003f003800e00e0#85,0x618618635012804a00a0#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier49 : List Wire := [⟨0x1c003f0003f003800e00e0#85,0x618618635012804a00a0#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier50 : List Wire := [⟨0xfc0000c0f0000f1f000#85,0x120820820c050000305000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier51 : List Wire := [⟨0x1fffc0fc0ffffc7cffff1c#85,0x1fbefbefbeffec54ffff14#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier52 : List Wire := [⟨0x3f000fc00003c7c00031c#85,0x410410410002c54810314#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier53 : List Wire := [⟨0x1c00000003f0c0000e0c00#85,0x9a69a69a2fac0004eac00#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier54 : List Wire := [⟨0x3f000000c0f3c7c000000#85,0x120820820c050c14000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier55 : List Wire := [⟨0x1fffc0fc0ffffffff1f31c#85,0x1fdf7df7ddffffffb15314#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier56 : List Wire := [⟨0xfc0fc00000000f1f31c#85,0x410410410002040b15314#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier57 : List Wire := [⟨0x1c00000003f0c383000000#85,0x9c71c71c1fad3ab000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier58 : List Wire := [⟨0x1c0000000ff00000fe0000#85,0x1228a28a2e5000007a0000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier59 : List Wire := [⟨0x1c0fff000fffff80ffffe0#85,0x1ffffffffffffe80feffa0#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier60 : List Wire := [⟨0x3f0000003f800003e0#85,0x451451451003e808003a0#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier61 : List Wire := [⟨0xfc000000fc00001fc00#85,0x986186180afc00004fc00#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier62 : List Wire := [⟨0x1c0000000ff03f80000000#85,0x124924924d501e80000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier63 : List Wire := [⟨0x1ff03f000ffffffffe03e0#85,0x1fffffffffffffbffa03a0#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier64 : List Wire := [⟨0x3f0000000000fe03e0#85,0x430c30c32002000fa03a0#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier65 : List Wire := [⟨0x3f00000000fc07f000000#85,0x986186180afc13f000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier66 : List Wire := [⟨0x1c0000000fffc000000000#85,0x1b8e38e38cffc000000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier67 : List Wire := [⟨0x1fffc0000ffffffffffc00#85,0x1befbefbefffdfbf7efc00#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier68 : List Wire := [⟨0xfc00000000000fffc00#85,0x208208220000007efc00#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def frontier69 : List Wire := [⟨0x3f0000000003fff000000#85,0x41041041001fbf000000#85⟩,⟨0x3ffff433c78f1e3fff#85,0x88208208022810a04284a#85⟩,⟨0x1fffc003fbccfa73e9ce93#85,0x575d75d73887261c98691#85⟩,⟨0x3ffc0fc0c0f3c7cf1f31c#85,0x161861861c052c54b15314#85⟩,⟨0x1c003f000ff03f80fe03e0#85,0x1679e79e7f503e80fa03a0#85⟩,⟨0x1c0fc0000fffc000fffc00#85,0x1baebaebaeffc0007efc00#85⟩,⟨0x1ff000000fffffff000000#85,0x1bcf3cf3cdffdfbf000000#85⟩]
def bank0 : List Wire := [⟨0x3000000000#85,0x400000001003000800000#85⟩,⟨0x400000003000000000000#85,0x1bffffffffffdfff7fffff#85⟩,⟨0x400000003003000000000#85,0x1001000000000#85⟩]
def bank1 : List Wire := [⟨0x300000000000#85,0x800000000708000000000#85⟩,⟨0x800000000c00000000000#85,0x17ffffffffdf7fffffffff#85⟩,⟨0x800000000f00000000000#85,0x500000000000#85⟩]
def bank2 : List Wire := [⟨0x30000000000#85,0x78000000000#85⟩,⟨0xc0000000000#85,0x1ffffffffffd7fffffffff#85⟩,⟨0xf0000000000#85,0x50000000000#85⟩]
def bank3 : List Wire := [⟨0xc000000#85,0x1e000000#85⟩,⟨0x30000000#85,0x1ffffffffffffff5ffffff#85⟩,⟨0x3c000000#85,0x14000000#85⟩]
def bank4 : List Wire := [⟨0x3000#85,0x7800#85⟩,⟨0xc000#85,0x1fffffffffffffffffd7ff#85⟩,⟨0xf000#85,0x5000#85⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched46 : quick 7 frontier46=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem pool0 : bank0.sublists.any (quick 3)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem pool1 : bank1.sublists.any (quick 3)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem pool2 : bank2.sublists.any (quick 3)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem pool3 : bank3.sublists.any (quick 3)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem pool4 : bank4.sublists.any (quick 3)=false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched20 : quick 7 frontier20=false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched14 : quick 7 frontier14=false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched42 : quick 7 frontier42=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched26 : quick 7 frontier26=false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched36 : quick 7 frontier36=false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched39 : quick 7 frontier39=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched17 : quick 7 frontier17=false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched33 : quick 7 frontier33=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched5 : quick 7 frontier5=false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched49 : quick 7 frontier49=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem searched23 : quick 7 frontier23=false := by decide +kernel

-- Verify each branch, then reconstruct the complete first step.

theorem excluded0 : NoPlan 7 frontier0 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded1 : NoPlan 7 frontier1 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded2 : NoPlan 7 frontier2 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded3 : NoPlan 7 frontier3 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded4 : NoPlan 7 frontier4 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded5 : NoPlan 7 frontier5 := banBySearch (by decide +kernel) searched5
theorem excluded6 : NoPlan 7 frontier6 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded7 : NoPlan 7 frontier7 :=
  banByRestriction (mask:=0x800000000f0c000000000#85) (j:=38) (bank:=bank1) (budget:=3) (by decide +kernel) pool1 (by decide +kernel) (by decide +kernel)
theorem excluded8 : NoPlan 7 frontier8 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded9 : NoPlan 7 frontier9 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded10 : NoPlan 7 frontier10 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded11 : NoPlan 7 frontier11 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded12 : NoPlan 7 frontier12 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded13 : NoPlan 7 frontier13 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded14 : NoPlan 7 frontier14 := banBySearch (by decide +kernel) searched14
theorem excluded15 : NoPlan 7 frontier15 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded16 : NoPlan 7 frontier16 :=
  banByRestriction (mask:=0x3f000000#85) (j:=24) (bank:=bank3) (budget:=3) (by decide +kernel) pool3 (by decide +kernel) (by decide +kernel)
theorem excluded17 : NoPlan 7 frontier17 := banBySearch (by decide +kernel) searched17
theorem excluded18 : NoPlan 7 frontier18 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded19 : NoPlan 7 frontier19 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded20 : NoPlan 7 frontier20 := banBySearch (by decide +kernel) searched20
theorem excluded21 : NoPlan 7 frontier21 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded22 : NoPlan 7 frontier22 :=
  banByRestriction (mask:=0xfc00#85) (j:=10) (bank:=bank4) (budget:=3) (by decide +kernel) pool4 (by decide +kernel) (by decide +kernel)
theorem excluded23 : NoPlan 7 frontier23 := banBySearch (by decide +kernel) searched23
theorem excluded24 : NoPlan 7 frontier24 :=
  banByRestriction (mask:=0x800000000f0c000000000#85) (j:=38) (bank:=bank1) (budget:=3) (by decide +kernel) pool1 (by decide +kernel) (by decide +kernel)
theorem excluded25 : NoPlan 7 frontier25 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded26 : NoPlan 7 frontier26 := banBySearch (by decide +kernel) searched26
theorem excluded27 : NoPlan 7 frontier27 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded28 : NoPlan 7 frontier28 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded29 : NoPlan 7 frontier29 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded30 : NoPlan 7 frontier30 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded31 : NoPlan 7 frontier31 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded32 : NoPlan 7 frontier32 :=
  banByRestriction (mask:=0x3f000000#85) (j:=24) (bank:=bank3) (budget:=3) (by decide +kernel) pool3 (by decide +kernel) (by decide +kernel)
theorem excluded33 : NoPlan 7 frontier33 := banBySearch (by decide +kernel) searched33
theorem excluded34 : NoPlan 7 frontier34 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded35 : NoPlan 7 frontier35 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded36 : NoPlan 7 frontier36 := banBySearch (by decide +kernel) searched36
theorem excluded37 : NoPlan 7 frontier37 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded38 : NoPlan 7 frontier38 :=
  banByRestriction (mask:=0xfc00#85) (j:=10) (bank:=bank4) (budget:=3) (by decide +kernel) pool4 (by decide +kernel) (by decide +kernel)
theorem excluded39 : NoPlan 7 frontier39 := banBySearch (by decide +kernel) searched39
theorem excluded40 : NoPlan 7 frontier40 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded41 : NoPlan 7 frontier41 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded42 : NoPlan 7 frontier42 := banBySearch (by decide +kernel) searched42
theorem excluded43 : NoPlan 7 frontier43 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded44 : NoPlan 7 frontier44 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded45 : NoPlan 7 frontier45 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded46 : NoPlan 7 frontier46 := banBySearch (by decide +kernel) searched46
theorem excluded47 : NoPlan 7 frontier47 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded48 : NoPlan 7 frontier48 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded49 : NoPlan 7 frontier49 := banBySearch (by decide +kernel) searched49
theorem excluded50 : NoPlan 7 frontier50 :=
  banByRestriction (mask:=0x800000000f0c000000000#85) (j:=38) (bank:=bank1) (budget:=3) (by decide +kernel) pool1 (by decide +kernel) (by decide +kernel)
theorem excluded51 : NoPlan 7 frontier51 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded52 : NoPlan 7 frontier52 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded53 : NoPlan 7 frontier53 :=
  banByRestriction (mask:=0x800000000f0c000000000#85) (j:=38) (bank:=bank1) (budget:=3) (by decide +kernel) pool1 (by decide +kernel) (by decide +kernel)
theorem excluded54 : NoPlan 7 frontier54 :=
  banByRestriction (mask:=0x800000000f0c000000000#85) (j:=38) (bank:=bank1) (budget:=3) (by decide +kernel) pool1 (by decide +kernel) (by decide +kernel)
theorem excluded55 : NoPlan 7 frontier55 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded56 : NoPlan 7 frontier56 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded57 : NoPlan 7 frontier57 :=
  banByRestriction (mask:=0x800000000f0c000000000#85) (j:=38) (bank:=bank1) (budget:=3) (by decide +kernel) pool1 (by decide +kernel) (by decide +kernel)
theorem excluded58 : NoPlan 7 frontier58 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded59 : NoPlan 7 frontier59 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded60 : NoPlan 7 frontier60 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded61 : NoPlan 7 frontier61 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded62 : NoPlan 7 frontier62 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded63 : NoPlan 7 frontier63 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded64 : NoPlan 7 frontier64 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded65 : NoPlan 7 frontier65 :=
  banByRestriction (mask:=0x400000003003000c00000#85) (j:=22) (bank:=bank0) (budget:=3) (by decide +kernel) pool0 (by decide +kernel) (by decide +kernel)
theorem excluded66 : NoPlan 7 frontier66 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded67 : NoPlan 7 frontier67 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded68 : NoPlan 7 frontier68 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
theorem excluded69 : NoPlan 7 frontier69 :=
  banByRestriction (mask:=0xfc000000000#85) (j:=38) (bank:=bank2) (budget:=3) (by decide +kernel) pool2 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rootChildren : kids 7 pins = [frontier0,frontier1,frontier2,frontier3,frontier4,frontier5,frontier6,frontier7,frontier8,frontier9,frontier10,frontier11,frontier12,frontier13,frontier14,frontier15,frontier16,frontier17,frontier18,frontier19,frontier20,frontier21,frontier22,frontier23,frontier24,frontier25,frontier26,frontier27,frontier28,frontier29,frontier30,frontier31,frontier32,frontier33,frontier34,frontier35,frontier36,frontier37,frontier38,frontier39,frontier40,frontier41,frontier42,frontier43,frontier44,frontier45,frontier46,frontier47,frontier48,frontier49,frontier50,frontier51,frontier52,frontier53,frontier54,frontier55,frontier56,frontier57,frontier58,frontier59,frontier60,frontier61,frontier62,frontier63,frontier64,frontier65,frontier66,frontier67,frontier68,frontier69] := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rootBound : NoPlan 8 pins := by
  apply banBySplit (k:=7) (by decide +kernel) (by decide +kernel)
  intro ys mem
  rw [rootChildren] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact excluded0
  · exact excluded1
  · exact excluded2
  · exact excluded3
  · exact excluded4
  · exact excluded5
  · exact excluded6
  · exact excluded7
  · exact excluded8
  · exact excluded9
  · exact excluded10
  · exact excluded11
  · exact excluded12
  · exact excluded13
  · exact excluded14
  · exact excluded15
  · exact excluded16
  · exact excluded17
  · exact excluded18
  · exact excluded19
  · exact excluded20
  · exact excluded21
  · exact excluded22
  · exact excluded23
  · exact excluded24
  · exact excluded25
  · exact excluded26
  · exact excluded27
  · exact excluded28
  · exact excluded29
  · exact excluded30
  · exact excluded31
  · exact excluded32
  · exact excluded33
  · exact excluded34
  · exact excluded35
  · exact excluded36
  · exact excluded37
  · exact excluded38
  · exact excluded39
  · exact excluded40
  · exact excluded41
  · exact excluded42
  · exact excluded43
  · exact excluded44
  · exact excluded45
  · exact excluded46
  · exact excluded47
  · exact excluded48
  · exact excluded49
  · exact excluded50
  · exact excluded51
  · exact excluded52
  · exact excluded53
  · exact excluded54
  · exact excluded55
  · exact excluded56
  · exact excluded57
  · exact excluded58
  · exact excluded59
  · exact excluded60
  · exact excluded61
  · exact excluded62
  · exact excluded63
  · exact excluded64
  · exact excluded65
  · exact excluded66
  · exact excluded67
  · exact excluded68
  · exact excluded69

-- A circuit with at least ten gates can use the explicit ten-gate witness. A smaller circuit with a NOT would have at most eight binary gates.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Wire

theorem probe_pos : ∀ i : Fin 85, target (probeP i) = true := by decide +kernel
theorem probe_neg : ∀ i : Fin 85, target (probeN i) = false := by decide +kernel
theorem pinsP : ∀ i : Fin 85, pins.map (side false i) = List.ofFn (probeP i) := by decide +kernel
theorem pinsN : ∀ i : Fin 85, pins.map (side true i) = List.ofFn (probeN i) := by decide +kernel
theorem pinsNodup : pins.Nodup := by decide

theorem circuitHit (C : Circuit) (leg : ∀g∈C.gates,legal g)
    (correct : ∀x,C.eval (List.ofFn x) = target x) : hit ((wordRun C.gates pins).getD C.output zero) := by
  apply (hit_iff _).2
  intro i
  have output (n : Bool) : side n i ((wordRun C.gates pins).getD C.output zero) =
      C.eval (pins.map (side n i)) := by
    have hzero : side n i zero=false := by cases n <;> simp [side,zero]
    rw [←List.getD_map (wordRun C.gates pins) zero (n:=C.output) (side n i),hzero,sideRun n i C.gates pins leg]; rfl
  have m := output false
  have n := output true
  rw [pinsP,correct,probe_pos] at m
  rw [pinsN,correct,probe_neg] at n
  intro eq
  change ((wordRun C.gates pins).getD C.output zero).1[i.val] = true at m
  change ((wordRun C.gates pins).getD C.output zero).2[i.val] = false at n
  rw [eq,n] at m
  contradiction

theorem noSmall (root : NoPlan 8 pins) (C : Circuit) (leg : ∀g∈C.gates,legal g) (small : count C.gates≤8)
    (correct : ∀x,C.eval (List.ofFn x)=target x) : False := by
  obtain ⟨m,mb,S,sub,pl⟩ := fromRun C.gates pins.toFinset pins C.output
    (fun w hw=>Or.inr ⟨w,List.mem_toFinset.mpr hw,Or.inl rfl⟩) leg (circuitHit C leg correct)
  let xs := pins.filter fun w=>w∈S
  have eq : xs.toFinset=S := by
    ext w
    simp only [xs,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun h=>⟨List.mem_toFinset.mp (sub h),h⟩⟩
  have incl : xs∈pins.sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  have closed : pins.sublists.all (fun ys => ys==pins || allSig ys != BitVec.allOnes 85) = true := by decide +kernel
  have all := List.all_eq_true.mp closed xs incl
  have mask : allSig xs=BitVec.allOnes 85 := by
    apply adequate; intro i; obtain ⟨w,hw,sep⟩ := pl.cover i
    exact ⟨w,List.mem_toFinset.mp (eq.symm ▸ hw),sep⟩
  have same : xs=pins := by simpa only [mask,bne_self_eq_false,Bool.or_false,beq_iff_eq] using all
  have e : S=pins.toFinset := eq.symm.trans (congrArg List.toFinset same)
  exact root m (by omega) (e ▸ pl)

theorem count_le (gs : List Gate) : count gs ≤ gs.length := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    have one : cost g ≤ 1 := by cases g with | mk op ins => cases op <;> simp [cost]
    change cost g + count gs ≤ gs.length + 1
    omega

theorem full_cost (gs : List Gate) (leg : ∀g∈gs,legal g) (h : count gs=gs.length) :
    ∀g∈gs, (g.op = GateOp.and ∨ g.op = GateOp.or) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    change cost g + count gs = gs.length+1 at h
    have co : cost g≤1 := by cases g with | mk op ins=> cases op <;> simp [cost]
    have b := count_le gs
    have cg : cost g=1 := by omega
    have tl : count gs=gs.length := by omega
    have og := (leg g (by simp)).1
    have op : g.op=.and ∨ g.op=.or := by
      rcases og with oa|oo|on
      · exact Or.inl oa
      · exact Or.inr oo
      · simp [cost,on] at cg
    intro u hu
    rcases List.mem_cons.mp hu with rfl|mem
    · exact op
    · exact ih (fun z hz=>leg z (by simp [hz])) tl u mem

theorem positiveFromRoot (root : NoPlan 8 pins) : ∀s : ℕ, HasCircuitSize 6 target s → ∃C : Circuit,
    Monotone2 C ∧ C.size ≤ s ∧ ∀x, C.eval (List.ofFn x) = target x := by
  intro s hs
  by_cases hs9 : 10 ≤ s
  · exact ⟨monoTen,tenMono,tenSize.le.trans hs9,tenEval⟩
  obtain ⟨C,fan,sz,correct⟩ := hs
  have leg : ∀g∈C.gates,legal g := fun g h=>fan g h
  by_cases full : count C.gates=C.gates.length
  · exact ⟨C,fun g hg=>⟨full_cost _ leg full g hg,(leg g hg).2⟩,sz,correct⟩
  have cnt := count_le C.gates
  change C.gates.length ≤ s at sz
  exact (noSmall root C leg (by omega) correct).elim

end PEqualNP.Outside.L_meta_15737_aux

theorem PEqualNP.Outside.L_meta_15737 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 3941116584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 3941116584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_15737_aux.positiveFromRoot PEqualNP.Outside.L_meta_15737_aux.rootBound
