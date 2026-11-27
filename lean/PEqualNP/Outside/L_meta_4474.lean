import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4474

def adj (N : ℕ) (inc : Fin N → Fin N → Prop) (u v : ℕ) : Prop :=
  ∃ p l : Fin N, inc p l ∧
    ((u = p.val ∧ v = N + l.val) ∨ (v = p.val ∧ u = N + l.val))

theorem adjSymm {N : ℕ} {inc : Fin N → Fin N → Prop} {u v : ℕ}
    (h : adj N inc u v) : adj N inc v u := by
  obtain ⟨p,l,hp,hv⟩ := h
  exact ⟨p,l,hp,hv.symm⟩

theorem commonUnique {N : ℕ} {inc : Fin N → Fin N → Prop}
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, inc p l ∧ inc p' l)
    {u u' v v' : ℕ} (ne : v ≠ v')
    (huv : adj N inc u v) (huv' : adj N inc u v')
    (hu'v : adj N inc u' v) (hu'v' : adj N inc u' v') : u = u' := by
  obtain ⟨p,l,edge,h⟩ := huv
  obtain ⟨p',l',edge',h'⟩ := huv'
  obtain ⟨r,t,edgeR,k⟩ := hu'v
  obtain ⟨r',t',edgeR',k'⟩ := hu'v'
  have hp := p.isLt
  have hp' := p'.isLt
  have hr := r.isLt
  have hr' := r'.isLt
  rcases h with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · have b1 : u < N := by omega
    have b2 : N ≤ v := by omega
    have b3 : N ≤ v' := by rcases h' with ⟨_,h⟩ | ⟨_,h⟩ <;> omega
    have left' : u = p'.val ∧ v' = N + l'.val := by
      rcases h' with h | ⟨_,h⟩
      · exact h
      · omega
    have right : u' = r.val ∧ v = N + t.val := by
      rcases k with k | ⟨k,_⟩
      · exact k
      · omega
    have right' : u' = r'.val ∧ v' = N + t'.val := by
      rcases k' with k' | ⟨k',_⟩
      · exact k'
      · omega
    have p_eq : p' = p := Fin.ext (left'.1.symm.trans hu)
    have r_eq : r' = r := Fin.ext (right'.1.symm.trans right.1)
    have l_eq : t = l := Fin.ext (by omega)
    have l'_eq : t' = l' := Fin.ext (by omega)
    subst p' r' t t'
    by_contra u_ne
    have p_ne : p ≠ r := fun he => u_ne (by rw [hu,right.1,he])
    obtain ⟨c,_,only⟩ := unique p r p_ne
    have same : l = l' := (only l ⟨edge,edgeR⟩).trans (only l' ⟨edge',edgeR'⟩).symm
    exact ne (by rw [hv,left'.2,same])
  · have b1 : N ≤ u := by omega
    have b2 : v < N := by omega
    have left' : v' = p'.val ∧ u = N + l'.val := by
      rcases h' with ⟨h,_⟩ | h
      · omega
      · exact h
    have right : v = r.val ∧ u' = N + t.val := by
      rcases k with ⟨_,k⟩ | k
      · omega
      · exact k
    have right' : v' = r'.val ∧ u' = N + t'.val := by
      rcases k' with ⟨_,k'⟩ | k'
      · have hv' := left'.1
        omega
      · exact k'
    have p_eq : r = p := Fin.ext (right.1.symm.trans hv)
    have p'_eq : r' = p' := Fin.ext (right'.1.symm.trans left'.1)
    have l_eq : l' = l := Fin.ext (by omega)
    have t_eq : t' = t := Fin.ext (by omega)
    subst r r' l' t'
    have p_ne : p ≠ p' := fun he => ne (by rw [hv,left'.1,he])
    obtain ⟨c,_,only⟩ := unique p p' p_ne
    have same : l = t := (only l ⟨edge,edge'⟩).trans (only t ⟨edgeR,edgeR'⟩).symm
    rw [hu,right.2,same]

theorem singletonOf {U : Finset ℕ} {v : ℕ} (hv : v ∈ U) (small : U.card ≤ 1) :
    U = {v} := by
  symm
  exact Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hv) (by simpa using small)

theorem firstBranch (N s : ℕ) (U : ℕ → Finset ℕ) (a b op : Fin s → ℕ)
    (prior : ∀ j, a j < N+N+j.val ∧ b j < N+N+j.val)
    (tags : ∀ j, op j ≤ 3)
    (raw : ∀ i < N+N, U i = {i})
    (updates : ∀ j, (op j=0 → U (N+N+j.val)=U (a j) ∪ U (b j)) ∧
      (op j=1 → U (N+N+j.val)=U (a j)) ∧ (2≤op j → U (N+N+j.val)=∅)) :
    ∀ r < N+N+s, ∀ v ∈ U r, 2 ≤ (U r).card →
    ∃ (j : Fin s) (dir : Bool), op j=0 ∧ U (N+N+j.val) ⊆ U r ∧
      2 ≤ (U (N+N+j.val)).card ∧ U (if dir then b j else a j) = {v} := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r smaller =>
    intro bound v hv large
    by_cases isRaw : r < N+N
    · rw [raw r isRaw, Finset.card_singleton] at large
      omega
    let j : Fin s := ⟨r-(N+N), by omega⟩
    have hj : N+N+j.val = r := by dsimp [j]; omega
    have a_prior : a j < r := by simpa only [hj] using (prior j).1
    have b_prior : b j < r := by simpa only [hj] using (prior j).2
    by_cases disj : op j=0
    · have parts := (updates j).1 disj
      rw [hj] at parts
      have helper (dir : Bool) (t : ℕ) (ht : t = (if dir then b j else a j))
          (before : t < r) (inside : U t ⊆ U r) (hm : v ∈ U t) :
          ∃ (k : Fin s) (d : Bool), op k=0 ∧ U (N+N+k.val) ⊆ U r ∧
            2 ≤ (U (N+N+k.val)).card ∧ U (if d then b k else a k) = {v} := by
        by_cases deep : 2 ≤ (U t).card
        · obtain ⟨k,d,h1,h2,h3,h4⟩ := smaller t before (by omega) v hm deep
          exact ⟨k,d,h1,h2.trans inside,h3,h4⟩
        · refine ⟨j,dir,disj,by rw [hj],by rwa [hj],?_⟩
          rw [← ht]
          exact singletonOf hm (by omega)
      rw [parts] at hv
      rcases Finset.mem_union.mp hv with ha | hb
      · exact helper false (a j) rfl a_prior (by rw [parts]; exact Finset.subset_union_left) ha
      · exact helper true (b j) rfl b_prior (by rw [parts]; exact Finset.subset_union_right) hb
    · by_cases isCopy : op j=1
      · have eq := (updates j).2.1 isCopy
        rw [hj] at eq
        rw [eq] at hv large ⊢
        exact smaller (a j) a_prior (by omega) v hv large
      · have eq := (updates j).2.2 (by have := tags j; omega)
        rw [hj] at eq
        rw [eq] at hv
        exact (Finset.notMem_empty _ hv).elim

set_option maxHeartbeats 3000000 in
theorem charge (N s : ℕ) (inc : Fin N → Fin N → Prop) [DecidableRel inc]
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, inc p l ∧ inc p' l)
    (U : ℕ → Finset ℕ) (a b op : Fin s → ℕ)
    (prior : ∀ j, a j < N+N+j.val ∧ b j < N+N+j.val)
    (tags : ∀ j, op j ≤ 3)
    (raw : ∀ i < N+N, U i = {i})
    (updates : ∀ j, (op j=0 → U (N+N+j.val)=U (a j) ∪ U (b j)) ∧
      (op j=1 → U (N+N+j.val)=U (a j)) ∧ (2≤op j → U (N+N+j.val)=∅))
    (trace : ∀ p l, inc p l → ∃ j : Fin s, op j=3 ∧
      ((p.val ∈ U (a j) ∧ N+l.val ∈ U (b j)) ∨
       (N+l.val ∈ U (a j) ∧ p.val ∈ U (b j))) ∧
      ∀ u ∈ U (a j), ∀ v ∈ U (b j), adj N inc u v) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter fun e => inc e.1 e.2).card ≤ 2*s := by
  classical
  let E := (Finset.univ : Finset (Fin N × Fin N)).filter fun e => inc e.1 e.2
  let pick (z : Fin s × Bool) := if z.2 then b z.1 else a z.1
  let flip (z : Fin s × Bool) := (z.1,!z.2)
  let certificate (z : Fin s × Bool) (u v : ℕ) :=
    (op z.1=0 ∧ U (pick z)={v} ∧ 2 ≤ (U (N+N+z.1.val)).card ∧
      ∀ w ∈ U (N+N+z.1.val), adj N inc u w) ∨
    (op z.1=3 ∧ U (pick z)={v} ∧ U (pick (flip z))={u})
  let endpoints (e : Fin N × Fin N) (u v : ℕ) :=
    (u = e.1.val ∧ v = N+e.2.val) ∨ (v = e.1.val ∧ u = N+e.2.val)
  have place (j : Fin s) (dir : Bool) (u v : ℕ) (hj : op j=3)
      (hv : v ∈ U (pick (j,dir))) (small : U (pick (flip (j,dir))) = {u})
      (neighbors : ∀ w ∈ U (pick (j,dir)), adj N inc u w) :
      ∃ z, certificate z u v := by
    by_cases multi : 2 ≤ (U (pick (j,dir))).card
    · have hk : pick (j,dir) < N+N+s := by
        have h := prior j
        have hj' := j.isLt
        cases dir <;> simp [pick] <;> omega
      obtain ⟨k,d,hk0,hsub,hlarge,hv⟩ :=
        firstBranch N s U a b op prior tags raw updates (pick (j,dir)) hk v hv multi
      exact ⟨(k,d), Or.inl ⟨hk0,hv,hlarge,fun w hw => neighbors w (hsub hw)⟩⟩
    · exact ⟨(j,dir), Or.inr ⟨hj,singletonOf hv (by omega),small⟩⟩
  have orient (j : Fin s) (u v : ℕ) (hj : op j=3) (hu : u ∈ U (a j)) (hv : v ∈ U (b j))
      (rectangle : ∀ t ∈ U (a j), ∀ w ∈ U (b j), adj N inc t w) :
      (∃ z, certificate z u v) ∨ (∃ z, certificate z v u) := by
    by_cases small : (U (a j)).card ≤ 1
    · exact Or.inl (place j true u v hj hv (singletonOf hu small) (rectangle u hu))
    · have hsmall : (U (b j)).card ≤ 1 := by
        by_contra not_small
        obtain ⟨u₁,hu₁,u₂,hu₂,ne_u⟩ := Finset.one_lt_card.mp (show 1 < (U (a j)).card by omega)
        obtain ⟨v₁,hv₁,v₂,hv₂,ne_v⟩ := Finset.one_lt_card.mp (show 1 < (U (b j)).card by omega)
        exact ne_u (commonUnique unique ne_v
          (rectangle u₁ hu₁ v₁ hv₁) (rectangle u₁ hu₁ v₂ hv₂)
          (rectangle u₂ hu₂ v₁ hv₁) (rectangle u₂ hu₂ v₂ hv₂))
      exact Or.inr (place j false v u hj hu (singletonOf hv hsmall)
        (fun w hw => adjSymm (rectangle w hw v hv)))
  have cover (e : E) : ∃ z, ∃ u v, endpoints e.val u v ∧ certificate z u v := by
    obtain ⟨j,hj,hab,cross⟩ := trace e.val.1 e.val.2 (Finset.mem_filter.mp e.property).2
    rcases hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rcases orient j _ _ hj ha hb cross with ⟨z,cert⟩ | ⟨z,cert⟩
      · exact ⟨z,_,_,Or.inl ⟨rfl,rfl⟩,cert⟩
      · exact ⟨z,_,_,Or.inr ⟨rfl,rfl⟩,cert⟩
    · rcases orient j _ _ hj ha hb cross with ⟨z,cert⟩ | ⟨z,cert⟩
      · exact ⟨z,_,_,Or.inr ⟨rfl,rfl⟩,cert⟩
      · exact ⟨z,_,_,Or.inl ⟨rfl,rfl⟩,cert⟩
  have uniqueEnd (z : Fin s × Bool) (u v u' v' : ℕ)
      (h : certificate z u v) (h' : certificate z u' v') : u = u' ∧ v = v' := by
    rcases h with ⟨h₀,leaf,large,neigh⟩ | ⟨h₃,leaf,cent⟩
    · rcases h' with ⟨_,leaf',_,neigh'⟩ | ⟨h₃,_,_⟩
      · obtain ⟨w,hw,t,ht,ne⟩ := Finset.one_lt_card.mp
          (show 1 < (U (N+N+z.1.val)).card by omega)
        refine ⟨commonUnique unique ne (neigh w hw) (neigh t ht) (neigh' w hw) (neigh' t ht),?_⟩
        simpa using leaf.symm.trans leaf'
      · omega
    · rcases h' with ⟨h₀,_,_,_⟩ | ⟨_,leaf',cent'⟩
      · omega
      · constructor
        · simpa using cent.symm.trans cent'
        · simpa using leaf.symm.trans leaf'
  have ordered (e : Fin N × Fin N) (u v : ℕ) (h : endpoints e u v) :
      min u v = e.1.val ∧ max u v = N+e.2.val := by
    have bound := e.1.isLt
    rcases h with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · rw [hu,hv,min_eq_left (by omega),max_eq_right (by omega)]
      exact ⟨rfl,rfl⟩
    · rw [hu,hv,min_eq_right (by omega),max_eq_left (by omega)]
      exact ⟨rfl,rfl⟩
  choose code hc using cover
  have injective : Function.Injective code := by
    intro x y he
    obtain ⟨u,v,hx,hcert⟩ := hc x
    obtain ⟨u',v',hy,hcert'⟩ := hc y
    rw [← he] at hcert'
    obtain ⟨sameU,sameV⟩ := uniqueEnd (code x) u v u' v' hcert hcert'
    subst u' v'
    obtain ⟨hx1,hx2⟩ := ordered x.val u v hx
    obtain ⟨hy1,hy2⟩ := ordered y.val u v hy
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext (hx1.symm.trans hy1)
    · exact Fin.ext (Nat.add_left_cancel (hx2.symm.trans hy2))
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Nat.mul_comm] using Fintype.card_le_of_injective code injective

abbrev Family := Set (Finset ℕ)

def hits (F : Family) (S : Finset ℕ) : Prop :=
  ∀ c ∈ F, ∃ i ∈ c, i ∈ S

abbrev joinFamily (A B : Family) : Family := Set.image2 (fun c d => c ∪ d) A B

theorem hits_raw (r : ℕ) (S : Finset ℕ) : hits {{r}} S ↔ r ∈ S := by
  simp [hits]

theorem hits_zero (S : Finset ℕ) : ¬ hits {∅} S := by
  simp [hits]

theorem hits_union (A B : Family) (S : Finset ℕ) :
    hits (A ∪ B) S ↔ hits A S ∧ hits B S := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc), fun d hd => h d (Or.inr hd)⟩
  · rintro ⟨ha,hb⟩ c (hc | hc)
    · exact ha c hc
    · exact hb c hc

theorem hits_or (A B : Family) (S : Finset ℕ) :
    hits (joinFamily A B) S ↔ hits A S ∨ hits B S := by
  classical
  constructor
  · intro h
    by_cases ha : hits A S
    · exact Or.inl ha
    by_cases hb : hits B S
    · exact Or.inr hb
    exfalso
    obtain ⟨a, hna⟩ := not_forall.mp ha
    have hac : a ∈ A ∧ ¬ ∃ i ∈ a, i ∈ S := not_imp.mp hna
    obtain ⟨b, hnb⟩ := not_forall.mp hb
    have hbc : b ∈ B ∧ ¬ ∃ i ∈ b, i ∈ S := not_imp.mp hnb
    obtain ⟨i, hi, hs⟩ := h (a ∪ b) ⟨a, hac.1, b, hbc.1, rfl⟩
    rcases Finset.mem_union.mp hi with hia | hib
    · exact hac.2 ⟨i, hia, hs⟩
    · exact hbc.2 ⟨i, hib, hs⟩
  · intro h c hc
    obtain ⟨a,ha,b,hb,rfl⟩ := hc
    rcases h with h | h
    · obtain ⟨i, hi, hs⟩ := h a ha
      exact ⟨i, Finset.mem_union_left _ hi, hs⟩
    · obtain ⟨i, hi, hs⟩ := h b hb
      exact ⟨i, Finset.mem_union_right _ hi, hs⟩

theorem one_of_pair {F : Family} {u v : ℕ} (hF : hits F {u,v})
    (hu : ∀ c ∈ F, u ∉ c) : hits F {v} := by
  intro c hc
  obtain ⟨i, hi, hp⟩ := hF c hc
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact (hu c hc hi).elim
  · exact ⟨i,hi,hp⟩

theorem singleton_mem {F : Family} {u : ℕ} (h : hits F {u}) {c : Finset ℕ} (hc : c ∈ F) :
    u ∈ c := by
  obtain ⟨i,hi,hu⟩ := h c hc
  rwa [Finset.mem_singleton.mp hu] at hi

theorem pair_comm (u v : ℕ) : ({u,v} : Finset ℕ) = {v,u} := by
  ext i
  simp [or_comm]

theorem split_pair {A B : Family} {u v : ℕ} (hA : A.Nonempty) (hB : B.Nonempty)
    (d : ∀ a ∈ A, ∀ b ∈ B, Disjoint a b) (h : hits (A ∪ B) {u,v}) :
    (hits A {u} ∧ hits B {v}) ∨ (hits A {v} ∧ hits B {u}) := by
  obtain ⟨ha,hb⟩ := (hits_union A B _).mp h
  have from_left {c : Finset ℕ} {i j : ℕ} (hc : c ∈ A) (hi : i ∈ c)
      (ha' : hits A {i,j}) (hb' : hits B {i,j}) : hits A {i} ∧ hits B {j} := by
    have hbs := one_of_pair hb' (fun b hbb hib => (Finset.disjoint_left.mp (d c hc b hbb)) hi hib)
    obtain ⟨b,hbb⟩ := hB
    have hbj := singleton_mem hbs hbb
    rw [pair_comm] at ha'
    have has := one_of_pair ha' (fun a haa hja => (Finset.disjoint_left.mp (d a haa b hbb)) hja hbj)
    exact ⟨has,hbs⟩
  obtain ⟨c,hc⟩ := hA
  obtain ⟨i,hi,hip⟩ := ha c hc
  rcases Finset.mem_insert.mp hip with rfl | hip
  · exact Or.inl (from_left hc hi ha hb)
  · obtain rfl := Finset.mem_singleton.mp hip
    rw [pair_comm] at ha hb
    exact Or.inr (from_left hc hi ha hb)

theorem no_and_single {A B : Family} {u : ℕ} (hA : A.Nonempty) (hB : B.Nonempty)
    (d : ∀ a ∈ A, ∀ b ∈ B, Disjoint a b) : ¬ hits (A ∪ B) {u} := by
  intro h
  obtain ⟨a,ha⟩ := hA
  obtain ⟨b,hb⟩ := hB
  obtain ⟨hut,huu⟩ := (hits_union A B _).mp h
  exact (Finset.disjoint_left.mp (d a ha b hb)) (singleton_mem hut ha) (singleton_mem huu hb)

theorem hits_and_pair {A B : Family} {u v : ℕ} (ha : hits A {u}) (hb : hits B {v}) :
    hits (A ∪ B) {u,v} := by
  refine (hits_union A B _).mpr ⟨?_,?_⟩
  · exact fun a h => ⟨u, singleton_mem ha h, Finset.mem_insert_self _ _⟩
  · exact fun b h => ⟨v, singleton_mem hb h, Finset.mem_insert_of_mem (by simp)⟩

theorem misses_pair {F : Family} {u v : ℕ} {c : Finset ℕ}
    (hc : c ∈ F) (hu : u ∉ c) (hv : v ∉ c) : ¬ hits F {u,v} := by
  intro h
  obtain ⟨i,hi,hS⟩ := h c hc
  rcases Finset.mem_insert.mp hS with rfl | hS
  · exact hu hi
  · exact hv (Finset.mem_singleton.mp hS ▸ hi)

theorem output_sound (q N : ℕ) (inc : Fin N → Fin N → Prop) (F : Family) (hq : 2 ≤ q)
    (tests : ∀ Y : Finset (Fin N), Y.card ≤ q → ∃ c ∈ F, ∀ i : Fin N,
      (i.val ∈ c ↔ ∃ l ∈ Y, inc i l) ∧ (N+i.val ∈ c ↔ i ∉ Y)) :
    ∀ u < N+N, ∀ v < N+N, hits F {u,v} → adj N inc u v := by
  classical
  have side (u : ℕ) (hu : u < N+N) : (∃ p : Fin N, u = p.val) ∨ (∃ l : Fin N, u = N+l.val) := by
    by_cases h : u < N
    · exact Or.inl ⟨⟨u,h⟩,rfl⟩
    · exact Or.inr ⟨⟨u-N,by omega⟩,by dsimp; omega⟩
  have cross (p l : Fin N) (h : hits F {p.val,N+l.val}) : inc p l := by
    by_contra e
    obtain ⟨c,hc,ht⟩ := tests {l} (by simp; omega)
    have hp : p.val ∉ c := by
      intro hmem
      obtain ⟨r,hr,hir⟩ := (ht p).1.mp hmem
      exact e (Finset.mem_singleton.mp hr ▸ hir)
    have hl : N+l.val ∉ c := by simp [(ht l).2]
    exact misses_pair hc hp hl h
  intro u hu v hv hh
  rcases side u hu with ⟨p,rfl⟩ | ⟨l,rfl⟩ <;> rcases side v hv with ⟨p',rfl⟩ | ⟨l',rfl⟩
  · obtain ⟨c,hc,ht⟩ := tests ∅ (by simp)
    have hn (p : Fin N) : p.val ∉ c := by simp [(ht p).1]
    exact (misses_pair hc (hn p) (hn p') hh).elim
  · exact ⟨p,l',cross p l' hh,Or.inl ⟨rfl,rfl⟩⟩
  · rw [pair_comm] at hh
    exact ⟨p',l,cross p' l hh,Or.inr ⟨rfl,rfl⟩⟩
  · have hsmall : ({l,l'} : Finset (Fin N)).card ≤ q := by
      have hcard := Finset.card_insert_le l ({l'} : Finset (Fin N))
      rw [Finset.card_singleton] at hcard
      omega
    obtain ⟨c,hc,ht⟩ := tests {l,l'} hsmall
    have hl : N+l.val ∉ c := by simp [(ht l).2]
    have hl' : N+l'.val ∉ c := by simp [(ht l').2]
    exact (misses_pair hc hl hl' hh).elim

def stepSpec (F A B : Family) (op : ℕ) : Prop :=
  (op = 0 ∧ F = joinFamily A B) ∨
  (op = 1 ∧ F = A) ∨
  (op = 2 ∧ F = {∅}) ∨
  (op = 3 ∧ F = A ∪ B ∧ ∀ a ∈ A, ∀ b ∈ B, Disjoint a b)

theorem semantic (q N : ℕ) (inc : Fin N → Fin N → Prop) (s o : ℕ)
    (F : ℕ → Family) (hq : 2 ≤ q) (hOut : o < N+N+s)
    (hRaw : ∀ i < N+N, F i = {{i}})
    (hStep : ∀ j < s, ∃ a < N+N+j, ∃ b < N+N+j,
      F (N+N+j) = joinFamily (F a) (F b) ∨ F (N+N+j) = F a ∨
      F (N+N+j) = {∅} ∨
      F (N+N+j) = F a ∪ F b ∧ ∀ c ∈ F a, ∀ d ∈ F b, Disjoint c d)
    (hCover : ∀ c ∈ F o, ∀ p l : Fin N, inc p l → p.val ∈ c ∨ N+l.val ∈ c)
    (hTests : ∀ Y : Finset (Fin N), Y.card ≤ q → ∃ c ∈ F o, ∀ i : Fin N,
      (i.val ∈ c ↔ ∃ l ∈ Y, inc i l) ∧ (N+i.val ∈ c ↔ i ∉ Y)) :
    ∃ (U : ℕ → Finset ℕ) (a b op : Fin s → ℕ),
      (∀ j, a j < N+N+j.val ∧ b j < N+N+j.val) ∧
      (∀ j, op j ≤ 3) ∧
      (∀ i < N+N, U i = {i}) ∧
      (∀ j, (op j = 0 → U (N+N+j.val) = U (a j) ∪ U (b j)) ∧
        (op j = 1 → U (N+N+j.val) = U (a j)) ∧ (2 ≤ op j → U (N+N+j.val) = ∅)) ∧
      ∀ p l : Fin N, inc p l → ∃ j : Fin s, op j = 3 ∧
        ((p.val ∈ U (a j) ∧ N+l.val ∈ U (b j)) ∨ (N+l.val ∈ U (a j) ∧ p.val ∈ U (b j))) ∧
        ∀ u ∈ U (a j), ∀ v ∈ U (b j), adj N inc u v := by
  classical
  have choices (j : Fin s) : ∃ a < N+N+j.val, ∃ b < N+N+j.val, ∃ op,
        stepSpec (F (N+N+j.val)) (F a) (F b) op := by
    obtain ⟨a,ha,b,hb,hor|halias|hzero|hand⟩ := hStep j.val j.isLt
    · exact ⟨a,ha,b,hb,0,Or.inl ⟨rfl,hor⟩⟩
    · exact ⟨a,ha,b,hb,1,Or.inr (Or.inl ⟨rfl,halias⟩)⟩
    · exact ⟨a,ha,b,hb,2,Or.inr (Or.inr (Or.inl ⟨rfl,hzero⟩))⟩
    · exact ⟨a,ha,b,hb,3,Or.inr (Or.inr (Or.inr ⟨rfl,hand⟩))⟩
  choose a ha b hb op hOp using choices
  have asGate {w : ℕ} (h1 : N+N ≤ w) (h2 : w < N+N+s) : ∃ j : Fin s, w = N+N+j.val := by
    exact ⟨⟨w-(N+N),by omega⟩,by dsimp; omega⟩
  have nonempty (w : ℕ) (hw : w < N+N+s) : (F w).Nonempty := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases h : w < N+N
      · rw [hRaw w h]
        exact ⟨{w}, by simp⟩
      · obtain ⟨j,rfl⟩ := asGate (by omega) hw
        have hA := ih (a j) (ha j) ((ha j).trans hw)
        have hB := ih (b j) (hb j) ((hb j).trans hw)
        rcases hOp j with ⟨_,he⟩ | ⟨_,he⟩ | ⟨_,he⟩ | ⟨_,he,_⟩
        · obtain ⟨c,hc⟩ := hA
          obtain ⟨d,hd⟩ := hB
          rw [he]
          exact ⟨c ∪ d, ⟨c,hc,d,hd,rfl⟩⟩
        · exact he ▸ hA
        · rw [he]
          exact ⟨∅,by simp⟩
        · obtain ⟨c,hc⟩ := hA
          rw [he]
          exact ⟨c,Or.inl hc⟩
  let U (w : ℕ) : Finset ℕ := (Finset.range (N+N)).filter (fun u => hits (F w) {u})
  have memU {w u : ℕ} : u ∈ U w ↔ u < N+N ∧ hits (F w) {u} := by
    simp [U]
  have rules (j : Fin s) :
      (op j = 0 → U (N+N+j.val) = U (a j) ∪ U (b j)) ∧
      (op j = 1 → U (N+N+j.val) = U (a j)) ∧ (2 ≤ op j → U (N+N+j.val) = ∅) := by
    have hA := nonempty (a j) (by have := ha j; have := j.isLt; omega)
    have hB := nonempty (b j) (by have := hb j; have := j.isLt; omega)
    rcases hOp j with ⟨hcode,he⟩ | ⟨hcode,he⟩ | ⟨hcode,he⟩ | ⟨hcode,he,dis⟩
    · refine ⟨fun _ => ?_,fun h => by omega,fun h => by omega⟩
      ext u
      simp only [Finset.mem_union, memU, he, hits_or]
      tauto
    · exact ⟨fun h => by omega,fun _ => by simp [U,he],fun h => by omega⟩
    · refine ⟨fun h => by omega,fun h => by omega,fun _ => ?_⟩
      ext u
      simp [memU,he,hits_zero]
    · refine ⟨fun h => by omega,fun h => by omega,fun _ => ?_⟩
      ext u
      simp [memU,he,no_and_single hA hB dis]
  have trace (w : ℕ) (hw : w < N+N+s) (u v : ℕ)
      (h : hits (F w) {u,v}) (hu : ¬ hits (F w) {u}) (hv : ¬ hits (F w) {v}) :
      ∃ j : Fin s, op j = 3 ∧ F (N+N+j.val) = F (a j) ∪ F (b j) ∧
        ((hits (F (a j)) {u} ∧ hits (F (b j)) {v}) ∨ (hits (F (a j)) {v} ∧ hits (F (b j)) {u})) ∧
        ∀ S, hits (F (N+N+j.val)) S → hits (F w) S := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases isRaw : w < N+N
      · rw [hRaw w isRaw, hits_raw] at h hu hv
        exfalso
        exact (Finset.mem_insert.mp h).elim (fun e => hu (by simp [e])) hv
      · obtain ⟨j,rfl⟩ := asGate (by omega) hw
        rcases hOp j with ⟨hcode,he⟩ | ⟨hcode,he⟩ | ⟨hcode,he⟩ | ⟨hcode,he,dis⟩
        · rw [he, hits_or] at h hu hv
          rcases h with h | h
          · obtain ⟨k,hk,heq,hpair,hcon⟩ := ih (a j) (ha j) ((ha j).trans hw)
              h (fun bad => hu (Or.inl bad)) (fun bad => hv (Or.inl bad))
            exact ⟨k,hk,heq,hpair,fun S hS => he.symm ▸ (hits_or _ _ S).mpr (Or.inl (hcon S hS))⟩
          · obtain ⟨k,hk,heq,hpair,hcon⟩ := ih (b j) (hb j) ((hb j).trans hw)
              h (fun bad => hu (Or.inr bad)) (fun bad => hv (Or.inr bad))
            exact ⟨k,hk,heq,hpair,fun S hS => he.symm ▸ (hits_or _ _ S).mpr (Or.inr (hcon S hS))⟩
        · rw [he] at h hu hv ⊢
          exact ih (a j) (ha j) ((ha j).trans hw) h hu hv
        · exact (hits_zero _ (he ▸ h)).elim
        · refine ⟨j,hcode,he,?_,fun _ hS => hS⟩
          exact split_pair (nonempty _ ((ha j).trans hw)) (nonempty _ ((hb j).trans hw)) dis (he ▸ h)
  have sound := output_sound q N inc (F o) hq hTests
  have noSingle (u : ℕ) (hu : u < N+N) : ¬ hits (F o) {u} := by
    intro h
    have hp : hits (F o) {u,u} := by simpa using h
    obtain ⟨p,l,_,⟨h1,h2⟩|⟨h1,h2⟩⟩ := sound u hu u hu hp
    all_goals have := p.isLt; omega
  refine ⟨U,a,b,op,fun j => ⟨ha j,hb j⟩,?_,?_,rules,?_⟩
  · intro j
    rcases hOp j with ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ <;> omega
  · intro i hi
    ext u
    rw [memU,hRaw i hi,hits_raw]
    simp only [Finset.mem_singleton]
    omega
  · intro p l hI
    have hu : p.val < N+N := by have := p.isLt; omega
    have hv : N+l.val < N+N := by have := l.isLt; omega
    have h : hits (F o) {p.val,N+l.val} := by
      intro c hc
      rcases hCover c hc p l hI with h | h
      · exact ⟨p.val,h,Finset.mem_insert_self _ _⟩
      · exact ⟨N+l.val,h,Finset.mem_insert_of_mem (by simp)⟩
    obtain ⟨j,hj,he,hpair,hreach⟩ := trace o hOut p.val (N+l.val) h (noSingle _ hu) (noSingle _ hv)
    refine ⟨j,hj,?_,?_⟩
    · rcases hpair with ⟨hpa,hlb⟩ | ⟨hla,hpb⟩
      · exact Or.inl ⟨memU.mpr ⟨hu,hpa⟩,memU.mpr ⟨hv,hlb⟩⟩
      · exact Or.inr ⟨memU.mpr ⟨hv,hla⟩,memU.mpr ⟨hu,hpb⟩⟩
    · intro u hU v hV
      obtain ⟨hu,hhu⟩ := memU.mp hU
      obtain ⟨hv,hhv⟩ := memU.mp hV
      apply sound u hu v hv
      apply hreach
      rw [he]
      exact hits_and_pair hhu hhv

open scoped BigOperators in
theorem incidence_card (q N : ℕ) (inc : Fin N → Fin N → Prop) [DecidableRel inc]
    (h : ∀ l, Fintype.card {p : Fin N // inc p l} = q+1) :
    (Finset.univ.filter (fun e : Fin N × Fin N => inc e.1 e.2)).card = N*(q+1) := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  calc
    (∑ l : Fin N, ∑ p : Fin N, if inc p l then 1 else 0) = ∑ _l : Fin N, (q+1) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simpa only [Fintype.card_subtype,Finset.card_filter] using h l
    _ = _ := by simp

end PEqualNP.Outside.L_meta_4474

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.L_meta_4474 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17 ∧ ∀ x18 ∈ x11 x16, ∀ x20 ∈ x11 x17, Disjoint x18 x20) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q N inc _ qLarge _ degree unique s o F hout hraw hstep hcover htests
  have hq : 2 ≤ q := by omega
  obtain ⟨U,a,b,op,prior,tags,raw,updates,trace⟩ :=
    PEqualNP.Outside.L_meta_4474.semantic q N inc s o F hq hout hraw hstep hcover htests
  have charged :=
    PEqualNP.Outside.L_meta_4474.charge N s inc unique U a b op prior tags raw updates trace
  have counted := PEqualNP.Outside.L_meta_4474.incidence_card q N inc degree
  rw [counted] at charged
  exact (Nat.mul_le_mul_left N (by omega : q ≤ q+1)).trans
    (charged.trans (Nat.mul_le_mul_right s (by decide : 2 ≤ 100)))
