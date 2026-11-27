import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6897

variable {α : Type} [DecidableEq α]

def At (l : List α) (d a : α) (i : ℕ) : Prop := i < l.length ∧ l.getD i d = a

omit [DecidableEq α] in
theorem has_iff (l : List α) (d a : α) : (∃ i, At l d a i) ↔ a ∈ l := by
  constructor
  · rintro ⟨i,hi,he⟩
    rw [List.getD_eq_getElem l d hi] at he
    exact he ▸ List.getElem_mem hi
  · intro h
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem h
    exact ⟨i,hi,(List.getD_eq_getElem l d hi).trans he⟩

omit [DecidableEq α] in
theorem at_succ (l : List α) (d a b : α) (i : ℕ) :
    At (b::l) d a (i+1) ↔ At l d a i := by simp [At]

def Pair (l : List α) (d a b : α) := ∃ i j : ℕ, i ≠ j ∧ At l d a i ∧ At l d b j

theorem pair_same (l : List α) (d a : α) : Pair l d a a ↔ 2 ≤ l.count a := by
  induction l with
  | nil => simp [Pair,At]
  | cons b t ih =>
    by_cases h : b = a
    · subst b
      simp only [List.count_cons_self]
      constructor
      · rintro ⟨i,j,hn,hi,hj⟩
        have hmem : a ∈ t := by
          cases i with
          | zero =>
            cases j with
            | zero => exact (hn rfl).elim
            | succ j => exact (has_iff t d a).1 ⟨j,(at_succ ..).1 hj⟩
          | succ i => exact (has_iff t d a).1 ⟨i,(at_succ ..).1 hi⟩
        have hpos := List.count_pos_iff.mpr hmem
        omega
      · intro h2
        have hpos : 0 < t.count a := by omega
        obtain ⟨j,hj⟩ := (has_iff t d a).2 (List.count_pos_iff.mp hpos)
        exact ⟨0,j+1,by omega,by simp [At],(at_succ ..).2 hj⟩
    · simp only [List.count_cons_of_ne h]
      constructor
      · rintro ⟨i,j,hn,hi,hj⟩
        cases i with
        | zero => exact (h (by simpa [At] using hi)).elim
        | succ i =>
          cases j with
          | zero => exact (h (by simpa [At] using hj)).elim
          | succ j =>
            exact ih.mp ⟨i,j,by omega,(at_succ ..).1 hi,(at_succ ..).1 hj⟩
      · intro ht
        obtain ⟨i,j,hn,hi,hj⟩ := ih.mpr ht
        exact ⟨i+1,j+1,by omega,(at_succ ..).2 hi,(at_succ ..).2 hj⟩

theorem pair_diff {l : List α} {d a b : α} (hab : a ≠ b) :
    Pair l d a b ↔ a ∈ l ∧ b ∈ l := by
  constructor
  · rintro ⟨i,j,_,hi,hj⟩
    exact ⟨(has_iff l d a).1 ⟨i,hi⟩,(has_iff l d b).1 ⟨j,hj⟩⟩
  · rintro ⟨ha,hb⟩
    obtain ⟨i,hi⟩ := (has_iff l d a).2 ha
    obtain ⟨j,hj⟩ := (has_iff l d b).2 hb
    refine ⟨i,j,?_,hi,hj⟩
    rintro rfl
    exact hab (hi.2.symm.trans hj.2)

variable (raw : List α) (d : α) (join meet : α → α → α)

def Gate (prev : List α) (v : α) := ∃ a b, Pair (raw ++ prev) d a b ∧
   (v = join a b ∨ 0 < prev.length ∧ v = meet a b)

def Chain (xs : List α) : Prop :=
  ∀ (k : ℕ) (hk : k < xs.length), Gate raw d join meet (xs.take k) xs[k]

theorem Chain.nil : Chain raw d join meet [] := by simp [Chain]

theorem Chain.snoc {raw : List α} {d : α} {join meet : α → α → α}
    {xs : List α} {v : α} (valid : Chain raw d join meet xs) (last : Gate raw d join meet xs v) :
    Chain raw d join meet (xs ++ [v]) := by
  intro k hk
  by_cases h : k < xs.length
  · rw [List.take_append_of_le_length h.le,List.getElem_append_left h]
    exact valid k h
  · have e : k = xs.length := by simp at hk; omega
    subst k
    simpa using last

theorem Chain.split {raw : List α} {d : α} {join meet : α → α → α}
    {xs : List α} {v : α} (hc : Chain raw d join meet (xs ++ [v])) :
    Chain raw d join meet xs ∧ Gate raw d join meet xs v := by
  constructor
  · intro k hk
    have h := hc k (by simp; omega : k < (xs ++ [v]).length)
    rw [List.take_append_of_le_length hk.le,List.getElem_append_left hk] at h
    exact h
  · simpa using hc xs.length (by simp)

def cap (all : List α) (a : α) : ℕ :=
  if meet a a ≠ a ∧ meet a a ∈ all ∧ meet a a ∉ raw then 2 else 1

theorem cap_bounds (all : List α) (a : α) :
    1 ≤ cap raw meet all a ∧ cap raw meet all a ≤ 2 := by
  unfold cap
  split <;> decide

theorem compress (all : List α)
    (initialDistinct : raw.Nodup)
    (initialFresh : ∀ a b, Pair raw d a b → join a b ∉ raw)
    (joinSelf : ∀ a, join a a = a)
    (meetStable : ∀ a, meet (meet a a) (meet a a) = meet a a)
    {old : List α} (hc : Chain raw d join meet old) (included : ∀ v ∈ old, v ∈ all) :
    ∃ new : List α, Chain raw d join meet new ∧ new.length ≤ old.length ∧
      (0 < old.length → 0 < new.length) ∧
      ∀ t, (raw ++ new).count t = min (cap raw meet all t) ((raw ++ old).count t) := by
  induction old using List.reverseRecOn with
  | nil =>
    refine ⟨[], Chain.nil raw d join meet, le_rfl, id, ?_⟩
    intro t
    have h := List.nodup_iff_count_le_one.mp initialDistinct t
    have hc := (cap_bounds raw meet all t).1
    simp only [List.append_nil, Nat.min_eq_right (by omega : raw.count t ≤ cap raw meet all t)]
  | append_singleton prev v ih =>
    obtain ⟨ch,gate⟩ := Chain.split hc
    have inc : ∀ u ∈ prev, u ∈ all := fun u hu => included u (by simp [hu])
    have hvall : v ∈ all := included v (by simp)
    obtain ⟨ys,hy,hlen,hpos,hcount⟩ := ih ch inc
    have mem_forward (u : α) (hu : u ∈ raw ++ prev) : u ∈ raw ++ ys := by
      apply List.count_pos_iff.mp
      have h := List.count_pos_iff.mpr hu
      have hcap := (cap_bounds raw meet all u).1
      rw [hcount]
      omega
    by_cases keep : (raw ++ ys).count v < cap raw meet all v
    · obtain ⟨a,b,hpair,hop⟩ := gate
      have hpair' : Pair (raw ++ ys) d a b := by
        by_cases he : a = b
        · subst b
          apply (pair_same ..).mpr
          have htwo := (pair_same ..).mp hpair
          have hcnt := hcount a
          have hlimit := cap_bounds raw meet all a
          by_contra h
          have hone : cap raw meet all a = 1 := by omega
          have hne : v ≠ a := by rintro rfl; omega
          rcases hop with hor | ⟨_,hand⟩
          · exact hne (hor.trans (joinSelf a))
          · have hdiag : meet a a ≠ a := fun e => hne (hand.trans e)
            have hnot : meet a a ∉ raw := by
              intro hr
              have hb : cap raw meet all v = 1 := by
                rw [hand]
                simp [cap, meetStable a]
              have hv : v ∈ raw ++ ys := List.mem_append.mpr (Or.inl (hand ▸ hr))
              have := List.count_pos_iff.mpr hv
              omega
            have hcap : cap raw meet all a = 2 := by
              unfold cap
              simp [hdiag, show meet a a ∈ all from hand ▸ hvall, hnot]
            omega
        · obtain ⟨ha,hb⟩ := (pair_diff he).mp hpair
          exact (pair_diff he).mpr ⟨mem_forward a ha,mem_forward b hb⟩
      refine ⟨ys ++ [v], .snoc hy ⟨a,b,hpair',hop.imp id (fun h => ⟨hpos h.1,h.2⟩)⟩,
        by simp; omega, by simp, ?_⟩
      intro t
      have hc := hcount t
      by_cases he : v = t
      · subst t
        simp only [← List.append_assoc, List.count_append, List.count_singleton_self] at *
        omega
      · simpa [List.count_append, he, Ne.symm he] using hc
    · refine ⟨ys, hy, by simp; omega, ?_, ?_⟩
      · intro _
        by_cases e : prev = []
        · subst prev
          have y0 : ys = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
          subst ys
          obtain ⟨a,b,hpair,hop⟩ := gate
          have hor : v = join a b := hop.elim id (fun h => by simp at h)
          have hn := initialFresh a b (by simpa using hpair)
          have hzero : raw.count v = 0 := List.count_eq_zero.mpr (hor ▸ hn)
          have hc := (cap_bounds raw meet all v).1
          simp [hzero] at keep
          omega
        · apply hpos
          exact List.length_pos_iff.mpr e
      · intro t
        have hc := hcount t
        by_cases he : v = t
        · subst t
          simp only [← List.append_assoc, List.count_append, List.count_singleton_self] at *
          omega
        · simpa [List.count_append, he, Ne.symm he] using hc

def Indexed (xs : List α) := ∀ k < xs.length,
  ∃ i j, i ≠ j ∧ i < raw.length + k ∧ j < raw.length + k ∧
  let a := (raw ++ xs).getD i d
  let b := (raw ++ xs).getD j d
  xs.getD k d = join a b ∨ 0 < k ∧ xs.getD k d = meet a b

omit [DecidableEq α] in
theorem prefix_read (xs : List α) (k i : ℕ) (hk : k ≤ xs.length) (hi : i < raw.length+k) :
    (raw ++ (xs.take k)).getD i d = (raw ++ xs).getD i d := by
  have hlen : i < (raw ++ xs.take k).length := by simp [Nat.min_eq_left hk, hi]
  rw [← List.getD_append _ (xs.drop k) _ _ hlen, List.append_assoc, List.take_append_drop]

theorem indexed_iff (xs : List α) : Indexed raw d join meet xs ↔
    ∀ (k : ℕ) (hk : k < xs.length), Gate raw d join meet (xs.take k) xs[k] := by
  constructor
  · intro hv k hk
    obtain ⟨i,j,hij,hi,hj,hop⟩ := hv k hk
    let a := (raw++xs).getD i d
    let b := (raw++xs).getD j d
    have tk : (xs.take k).length = k := by simp [Nat.min_eq_left hk.le]
    refine ⟨a,b,⟨i,j,hij,⟨by simpa [tk] using hi, prefix_read raw d xs k i hk.le hi⟩,
      ⟨by simpa [tk] using hj, prefix_read raw d xs k j hk.le hj⟩⟩,?_⟩
    dsimp only at hop
    simpa only [a,b,List.getD_eq_getElem xs d hk,tk] using hop
  · intro hv k hk
    obtain ⟨a,b,⟨i,j,hij,hi,hj⟩,hop⟩ := hv k hk
    have tk : (xs.take k).length = k := by simp [Nat.min_eq_left hk.le]
    have ia : i < raw.length+k := by simpa [tk] using hi.1
    have jb : j < raw.length+k := by simpa [tk] using hj.1
    refine ⟨i,j,hij,ia,jb,?_⟩
    have hea := (prefix_read raw d xs k i hk.le ia).symm.trans hi.2
    have heb := (prefix_read raw d xs k j hk.le jb).symm.trans hj.2
    simpa only [hea,heb,List.getD_eq_getElem xs d hk, tk] using hop


theorem normalize (target : α) (old : List α) (targetMem : target ∈ old)
    (tgt : target ∉ raw) (hg : Indexed raw d join meet old)
    (hd : raw.Nodup) (hf : ∀ a b, Pair raw d a b → join a b ∉ raw)
    (hj : ∀ a, join a a = a) (hm : ∀ a, meet (meet a a) (meet a a) = meet a a) :
    ∃ new : List α, new.length ≤ old.length ∧ target ∈ new ∧ Indexed raw d join meet new ∧
      ∀ t, (raw ++ new).count t ≤ 2 ∧ (1 < (raw ++ new).count t →
        ∃ u ∈ new, u ≠ t ∧ u = meet t t) := by
  have chain : Chain raw d join meet old := (indexed_iff raw d join meet old).mp hg
  obtain ⟨ys,cy,hsize,_,hcounts⟩ := compress raw d join meet old hd hf hj hm chain (fun _ h => h)
  have preserve (a : α) (h : a ∈ old) (hn : a ∉ raw) : a ∈ ys := by
    have hpos := List.count_pos_iff.mpr (List.mem_append.mpr (Or.inr h) : a ∈ raw ++ old)
    have hcap := (cap_bounds raw meet old a).1
    have he := hcounts a
    have hnew : 0 < (raw ++ ys).count a := by omega
    exact (List.mem_append.mp (List.count_pos_iff.mp hnew)).resolve_left hn
  refine ⟨ys,hsize,preserve target targetMem tgt,(indexed_iff raw d join meet ys).mpr cy,?_⟩
  intro t
  have hlim := (cap_bounds raw meet old t).2
  have hc := hcounts t
  refine ⟨by omega,?_⟩
  intro h
  have capTwo : cap raw meet old t = 2 := by omega
  unfold cap at capTwo
  split at capTwo
  · rename_i hs
    exact ⟨meet t t,preserve _ hs.2.1 hs.2.2,hs.1,rfl⟩
  · contradiction

abbrev Sig := Fin 62 → Bool
def words : List ℕ := [2594090156585648135,15270196031782968,58150373818816,94946423956573696,
  54820275478360064,3870282840506368,133412159488,1911954591369396745,218716039641305168,
  189725234880873600,156548607028504576,229736628137050114,270286071509155872,288160007408582916]
def initial : List Sig := words.map fun n i => n.testBit i.val
def zero : Sig := fun _ => false
def accepted : Sig := fun i => decide (i.val < 21)
def plus (a b : Sig) : Sig := fun i => a i || b i
def prod (a b : Sig) : Sig := fun i =>
  if i = 60 then a 58 && b 60 || a 60 && b 58
  else if i = 61 then a 59 && b 61 || a 61 && b 59
  else a i && b i
def constrained (a : Sig) : Sig := fun i =>
  a i && (decide (i.val < 60) || a (i-2))

theorem plus_same (s : Sig) : plus s s = s := by funext i; simp [plus]

theorem prod_fixed (s : Sig) : prod (prod s s) (prod s s) = prod s s := by
  funext i
  by_cases h : i = 60
  · subst i
    simp [prod,Bool.and_comm]
  · by_cases h' : i = 61
    · subst i
      simp [prod,Bool.and_comm]
    · simp [prod,h,h']

theorem prod_diag (s : Sig) : prod s s = constrained s := by
  funext i
  by_cases h : i = 60
  · subst i; simp [prod,constrained,Bool.and_comm]
  · by_cases h' : i = 61
    · subst i; simp [prod,constrained,Bool.and_comm]
    · have hi : i.val < 60 := by
        have ha : i.val ≠ 60 := fun e => h (Fin.ext e)
        have hb : i.val ≠ 61 := fun e => h' (Fin.ext e)
        omega
      simp [prod,constrained,h,h',hi]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem concrete_nodup : initial.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem concrete_target : accepted ∉ initial := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem initial_fresh_aux :
   ∀ i j k : Fin 14, i ≠ j → ∃ r : Fin 62,
     ((initial.getD i.val zero r || initial.getD j.val zero r) ≠ initial.getD k.val zero r) := by
  decide +kernel

theorem initial_fresh (a b : Sig) (hp : Pair initial zero a b) : plus a b ∉ initial := by
  rintro he
  obtain ⟨i,j,hne,hi,hj⟩ := hp
  obtain ⟨k,hk⟩ := (has_iff initial zero (plus a b)).mpr he
  let i' : Fin 14 := ⟨i,hi.1⟩
  let j' : Fin 14 := ⟨j,hj.1⟩
  let k' : Fin 14 := ⟨k,hk.1⟩
  obtain ⟨r,hr⟩ := initial_fresh_aux i' j' k' (fun h => hne (congrArg Fin.val h))
  apply hr
  change (initial.getD i zero r || initial.getD j zero r) = initial.getD k zero r
  rw [hi.2,hj.2,hk.2]
  rfl

end PEqualNP.Outside.L_meta_6897

open PEqualNP.Outside.L_meta_6897 in
theorem PEqualNP.Outside.L_meta_6897 : have x1 : List (Fin (62 : ℕ) → Bool) := List.map (fun (x1 : ℕ) (x2 : Fin (62 : ℕ)) => x1.testBit ↑x2) [(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)]; have x2 : List (Fin (62 : ℕ) → Bool) → Prop := fun (x2 : List (Fin (62 : ℕ) → Bool)) =>   (fun (x3 : Fin (62 : ℕ)) => Decidable.decide (↑x3 < (21 : ℕ))) ∈ x2 ∧     ∀ x3 < x2.length,       ∃ (x5 : ℕ) (x6 : ℕ),         x5 ≠ x6 ∧           x5 < (14 : ℕ) + x3 ∧             x6 < (14 : ℕ) + x3 ∧               have x7 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x5 fun (x7 : Fin (62 : ℕ)) => Bool.false;               have x8 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x6 fun (x8 : Fin (62 : ℕ)) => Bool.false;               ((x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => x7 x9 || x8 x9) ∨ (0 : ℕ) < x3 ∧ (x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => if x9 = (60 : Fin (62 : ℕ)) then x7 (58 : Fin (62 : ℕ)) && x8 (60 : Fin (62 : ℕ)) || x7 (60 : Fin (62 : ℕ)) && x8 (58 : Fin (62 : ℕ)) else if x9 = (61 : Fin (62 : ℕ)) then x7 (59 : Fin (62 : ℕ)) && x8 (61 : Fin (62 : ℕ)) || x7 (61 : Fin (62 : ℕ)) && x8 (59 : Fin (62 : ℕ)) else x7 x9 && x8 x9; ∀ (x3 : List (Fin (62 : ℕ) → Bool)),   x2 x3 →     ∃ (x5 : List (Fin (62 : ℕ) → Bool)),       x5.length ≤ x3.length ∧         x2 x5 ∧           ∀ (x6 : Fin (62 : ℕ) → Bool),             have x7 : ℕ := List.count x6 (x1 ++ x5);             x7 ≤ (2 : ℕ) ∧ ((1 : ℕ) < x7 → ∃ x9 ∈ x5, x9 ≠ x6 ∧ x9 = fun (x10 : Fin (62 : ℕ)) => x6 x10 && (Decidable.decide (↑x10 < (60 : ℕ)) || x6 (x10 - (2 : Fin (62 : ℕ))))) := by
  change ∀ old : List Sig, accepted ∈ old ∧ Indexed initial zero plus prod old →
      ∃ new : List Sig, new.length ≤ old.length ∧ (accepted ∈ new ∧ Indexed initial zero plus prod new) ∧
        ∀ t : Sig, (initial ++ new).count t ≤ 2 ∧
          (1 < (initial ++ new).count t → ∃ u ∈ new, u ≠ t ∧ u = constrained t)
  intro old h
  obtain ⟨ys, hs, ht, hg, hdup⟩ :=
    normalize initial zero plus prod accepted old h.1 concrete_target h.2
      concrete_nodup initial_fresh plus_same prod_fixed
  refine ⟨ys,hs,⟨ht,hg⟩,?_⟩
  intro t
  refine ⟨(hdup t).1,?_⟩
  intro htwo
  obtain ⟨u,hu,hne,he⟩ := (hdup t).2 htwo
  exact ⟨u,hu,hne,he.trans (prod_diag t)⟩
