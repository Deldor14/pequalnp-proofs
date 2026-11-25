import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PEqualNP.Defs

open PEqualNP.ProofComplexity

namespace PEqualNP.Outside.L_pcx_112

abbrev V := Fin 3 × Fin 2
abbrev I := Fin 9
abbrev LC := LinClause V

def src : I → Clause V
  | 0 => {((0,0),true), ((0,1),true)}
  | 1 => {((1,0),true), ((1,1),true)}
  | 2 => {((2,0),true), ((2,1),true)}
  | 3 => {((0,0),false), ((1,0),false)}
  | 4 => {((0,1),false), ((1,1),false)}
  | 5 => {((0,0),false), ((2,0),false)}
  | 6 => {((0,1),false), ((2,1),false)}
  | 7 => {((1,0),false), ((2,0),false)}
  | 8 => {((1,1),false), ((2,1),false)}

lemma listed {C : Clause V} (h : C ∈ PHP 3 2) : ∃ i, C = src i := by
  rcases h with ⟨p,rfl⟩ | ⟨p,q,j,h,rfl⟩
  · fin_cases p <;> decide
  · fin_cases p <;> fin_cases q <;> fin_cases j <;> first | contradiction | decide

def okA (a : V → Bool) (i : I) : Bool :=
  decide (∃ l ∈ src i, a l.1 = l.2)

lemma satSrc {a : V → Bool} {i : I} (h : okA a i) :
    LinClauseSat a (linOfClause (src i)) := by
  obtain ⟨⟨v,b⟩,hv,hab⟩ := of_decide_eq_true h
  refine ⟨({v},b), Finset.mem_image.mpr ⟨(v,b),hv,rfl⟩, ?_⟩
  have hab' : a v = b := by simpa using hab
  cases b <;> simp_all [LinEqSat, Finset.filter_singleton]

def others (a : V → Bool) (i : I) : Bool :=
  decide (∀ j : I, j ≠ i → okA a j = true)

def assignments : List (V → Bool) :=
  (List.range 64).map fun n v => n.testBit (v.1.val * 2 + v.2.val)

lemma crit : ∀ i : I, assignments.any (fun a => others a i) = true := by decide

lemma splitCrit : ∀ v : V, ∃ i : I, ∀ b : Bool,
    assignments.any (fun a => (a v == b) && others a i) = true := by decide


abbrev Block := Finset I
abbrev Family := Finset Block

def covers (s : Block) (C : LC) : Prop :=
  ∀ a : V → Bool, (∀ i ∈ s, okA a i = true) → LinClauseSat a C

lemma coversMono {s t : Block} {C : LC} (h : covers s C) (hst : s ⊆ t) : covers t C :=
  fun a ha => h a (fun i hi => ha i (hst hi))

lemma coversAx (i : I) : covers {i} (linOfClause (src i)) := by
  intro a ha
  exact satSrc (ha i (by simp))

lemma resSound {C D R : LC} (hr : IsLinResolvent C D R) (a : V → Bool)
    (hc : LinClauseSat a C) (hd : LinClauseSat a D) : LinClauseSat a R := by
  obtain ⟨f,_,_,rfl⟩ := hr
  obtain ⟨q,hq,sq⟩ := hc
  obtain ⟨r,hr,sr⟩ := hd
  by_cases hx : q = (f,false)
  · subst q
    have hy : r ≠ (f,true) := by
      intro h
      subst r
      simp [LinEqSat] at sq sr
      exact (Nat.not_even_iff_odd.mpr sr) sq
    exact ⟨r,Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hy,hr⟩),sr⟩
  · exact ⟨q,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hx,hq⟩),sq⟩

def plain (C : LC) : Prop := ∀ q ∈ C, ∃ v : V, q.1 = {v}

lemma plainAx (i : I) : plain (linOfClause (src i)) := by
  intro q hq
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
  exact ⟨_,rfl⟩

lemma plainRes {C D R : LC} (hr : IsLinResolvent C D R) (hc : plain C) (hd : plain D) :
    plain R := by
  obtain ⟨f,_,_,rfl⟩ := hr
  intro q hq
  rcases Finset.mem_union.mp hq with h | h
  · exact hc q (Finset.mem_of_mem_erase h)
  · exact hd q (Finset.mem_of_mem_erase h)

-- Each block collects source axioms whose conjunction suffices for a line.
-- Joining two blocks raises their total cost by at most one.
def cost (F : Family) : ℕ := ∑ s ∈ F, (s.card - 1)

lemma costErase {F : Family} {s : Block} (hs : s ∈ F) :
    cost (F.erase s) + (s.card - 1) = cost F := by
  exact Finset.sum_erase_add _ _ hs

lemma costInsert (F : Family) (s : Block) :
    cost (insert s F) ≤ cost F + (s.card - 1) := by
  by_cases h : s ∈ F
  · simp [Finset.insert_eq_of_mem h]
  · simp [cost,Finset.sum_insert h,Nat.add_comm]

lemma beforeMerge {F : Family} {s t : Block} (hs : s ∈ F) (ht : t ∈ F) (hne : s ≠ t) :
    cost ((F.erase s).erase t) + (s.card - 1) + (t.card - 1) = cost F := by
  have h := costErase (Finset.mem_erase.mpr ⟨Ne.symm hne,ht⟩ : t ∈ F.erase s)
  have h' := costErase hs
  omega

def merged (F : Family) (s t : Block) := insert (s ∪ t) ((F.erase s).erase t)

lemma costMerge {F : Family} {s t : Block} (hs : s ∈ F) (ht : t ∈ F) (hne : s ≠ t) :
    cost (merged F s t) ≤ cost F + 1 := by
  have h := costInsert ((F.erase s).erase t) (s ∪ t)
  have he := beforeMerge hs ht hne
  have hu := Finset.card_union_le s t
  unfold merged
  omega

lemma moveBlock {F : Family} {s t u : Block} (hu : u ∈ F) :
    ∃ w ∈ merged F s t, u ⊆ w := by
  by_cases h : u = s
  · subst u
    exact ⟨_,Finset.mem_insert_self ..,Finset.subset_union_left⟩
  by_cases h' : u = t
  · subst u
    exact ⟨_,Finset.mem_insert_self ..,Finset.subset_union_right⟩
  exact ⟨u,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h',Finset.mem_erase.mpr ⟨h,hu⟩⟩),Finset.Subset.rfl⟩


def baseAxioms := (fun C : Clause V => linOfClause C) '' PHP 3 2

lemma account {π : List LC} (d : IsLinDerivation baseAxioms π) :
    ∃ (A : Block) (F : Family), (∀ s ∈ F, s ⊆ A) ∧
      (∀ C ∈ π, ∃ s ∈ F, covers s C) ∧
      A.card + cost F ≤ π.length ∧
      (π.length ≤ A.card + cost F → ∀ C ∈ π, plain C) := by
  induction d with
  | nil =>
    exact ⟨∅,∅,by simp,by simp,by simp [cost],by simp⟩
  | @ax π C d h ih =>
    obtain ⟨A,F,hsub,hcov,hbudget,hplain⟩ := ih
    obtain ⟨K,hK,rfl⟩ := h
    obtain ⟨i,rfl⟩ := listed hK
    have hb := costInsert F {i}
    simp only [Finset.card_singleton,Nat.sub_self,Nat.add_zero] at hb
    have hi := Finset.card_insert_le i A
    refine ⟨insert i A,insert {i} F,?_,?_,?_,?_⟩
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · simp
      · exact (hsub s hs).trans (Finset.subset_insert ..)
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hX
      · exact ⟨_,Finset.mem_insert_self .., coversAx i⟩
      · obtain ⟨s,hs,hc⟩ := hcov X hX
        exact ⟨s,Finset.mem_insert_of_mem hs,hc⟩
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      intro he X hX
      rcases List.mem_cons.mp hX with rfl | hX
      · exact plainAx i
      · exact hplain (by omega) X hX
  | @weak π C D d hc hw ih =>
    obtain ⟨A,F,hsub,hcov,hbudget,hplain⟩ := ih
    refine ⟨A,F,hsub,?_,by simp only [List.length_cons]; omega,?_⟩
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hX
      · obtain ⟨s,hs,hc'⟩ := hcov C hc
        exact ⟨s,hs,fun a ha => hw a (hc' a ha)⟩
      · exact hcov X hX
    · simp only [List.length_cons]
      omega
  | @res π C D R d hc hd hr ih =>
    obtain ⟨A,F,hsub,hcov,hbudget,hplain⟩ := ih
    obtain ⟨s,hs,hC⟩ := hcov C hc
    obtain ⟨t,ht,hD⟩ := hcov D hd
    have hb : cost (merged F s t) ≤ cost F + 1 := by
      by_cases h : s = t
      · subst t
        simp [merged,Finset.insert_erase hs]
      · exact costMerge hs ht h
    refine ⟨A,merged F s t,?_,?_,?_,?_⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | h
      · exact Finset.union_subset (hsub s hs) (hsub t ht)
      · exact hsub _ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hX
      · refine ⟨s ∪ t,Finset.mem_insert_self .., fun a ha => resSound hr a ?_ ?_⟩
        · exact coversMono hC Finset.subset_union_left a ha
        · exact coversMono hD Finset.subset_union_right a ha
      · obtain ⟨u,hu,hU⟩ := hcov X hX
        obtain ⟨w,hw,huw⟩ := moveBlock (s := s) (t := t) hu
        exact ⟨w,hw,coversMono hU huw⟩
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      intro he X hX
      have hp := hplain (by omega)
      rcases List.mem_cons.mp hX with rfl | hX
      · exact plainRes hr (hp C hc) (hp D hd)
      · exact hp X hX


lemma passOthers {s : Block} {i : I} {a : V → Bool} (h : others a i) (hi : i ∉ s) :
    ∀ j ∈ s, okA a j = true := by
  intro j hj
  exact (of_decide_eq_true h : ∀ k : I, k ≠ i → okA a k = true) j
    (fun he => hi (he ▸ hj))

lemma full {s : Block} {C : LC} (h : covers s C) (hn : ∀ a, ¬ LinClauseSat a C) :
    s = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hi
  obtain ⟨a,_,ha⟩ := List.any_eq_true.mp (crit i)
  exact hn a (h a (passOthers ha hi))

lemma crossing {s t : Block} (v : V)
    (hc : covers s {(({v} : Finset V),false)}) (hd : covers t {(({v} : Finset V),true)}) :
    (s ∩ t).Nonempty := by
  obtain ⟨i,hi⟩ := splitCrit v
  refine ⟨i,Finset.mem_inter.mpr ⟨?_,?_⟩⟩
  · by_contra hx
    obtain ⟨a,_,ha⟩ := List.any_eq_true.mp (hi true)
    simp only [Bool.and_eq_true] at ha
    obtain ⟨hav,hoth⟩ := ha
    have hxv : a v = true := by simpa using hav
    have hh := hc a (passOthers hoth hx)
    simp [LinClauseSat,LinEqSat,Finset.filter_singleton,hxv] at hh
  · by_contra hx
    obtain ⟨a,_,ha⟩ := List.any_eq_true.mp (hi false)
    simp only [Bool.and_eq_true] at ha
    obtain ⟨hav,hoth⟩ := ha
    have hxv : a v = false := by simpa using hav
    have hh := hd a (passOthers hoth hx)
    simp [LinClauseSat,LinEqSat,Finset.filter_singleton,hxv] at hh

lemma universeCard : (Finset.univ : Block).card = 9 := by decide

lemma falseBudget {π : List LC} (d : IsLinDerivation baseAxioms π) {C : LC} (hc : C ∈ π)
    (hn : ∀ a, ¬ LinClauseSat a C) : 17 ≤ π.length := by
  obtain ⟨A,F,hsub,hcov,hb,_⟩ := account d
  obtain ⟨s,hs,hC⟩ := hcov C hc
  have he := full hC hn
  subst s
  have hA := Finset.card_le_card (hsub _ hs)
  have hF := costErase hs
  rw [universeCard] at hA hF
  omega

lemma emptyImpossible (a : V → Bool) : ¬ LinClauseSat a (∅ : LC) := by simp [LinClauseSat]

lemma eraseToSingleton {C : LC} {q : LinEq V} (hq : q ∈ C) (he : C.erase q = ∅) :
    C = {q} := by
  rw [← Finset.insert_erase hq,he]
  rfl

-- In a tight derivation every pivot is an original variable. Two assignments
-- on opposite sides of that pivot force its two supporting blocks to overlap.
lemma lastRes {π : List LC} (d : IsLinDerivation baseAxioms π) {C D : LC}
    (hC : C ∈ π) (hD : D ∈ π) (hr : IsLinResolvent C D ∅) : 17 ≤ π.length := by
  by_contra! hshort
  obtain ⟨A,F,hsub,hcov,hb,hp⟩ := account d
  obtain ⟨s,hs,sc⟩ := hcov C hC
  obtain ⟨t,ht,td⟩ := hcov D hD
  have hu : s ∪ t = Finset.univ := by
    apply full (C := ∅) _ emptyImpossible
    intro a ha
    exact resSound hr a (coversMono sc Finset.subset_union_left a ha)
      (coversMono td Finset.subset_union_right a ha)
  have hA := Finset.card_le_card (Finset.union_subset (hsub s hs) (hsub t ht))
  rw [hu,universeCard] at hA
  by_cases heq : s = t
  · subst t
    simp only [Finset.union_idempotent] at hu
    have hF := costErase hs
    rw [hu,universeCard] at hF
    omega
  have hsum := beforeMerge hs ht heq
  have hcount := Finset.card_union_add_card_inter s t
  rw [hu,universeCard] at hcount
  have hp' := hp (by omega)
  obtain ⟨f,hf,hg,he⟩ := hr
  have hf' := hp' C hC (f,false) hf
  obtain ⟨v,hv⟩ := hf'
  change f = {v} at hv
  subst f
  obtain ⟨hc',hd'⟩ := Finset.union_eq_empty.mp he.symm
  rw [eraseToSingleton hf hc'] at sc
  rw [eraseToSingleton hg hd'] at td
  have hi := Finset.card_pos.mpr (crossing v sc td)
  omega


lemma lower {π : List LC} (d : IsLinDerivation baseAxioms π) (h : (∅ : LC) ∈ π) :
    18 ≤ π.length := by
  induction d with
  | nil => simp at h
  | @ax π C d ha ih =>
    rcases List.mem_cons.mp h with he | h
    · obtain ⟨K,hK,rfl⟩ := ha
      obtain ⟨i,rfl⟩ := listed hK
      change (∅ : LC) = linOfClause (src i) at he
      have hf := full (coversAx i) (fun a => by rw [← he]; exact emptyImpossible a)
      have hc := congrArg Finset.card hf
      simp at hc
    · simp only [List.length_cons]
      have hh := ih h
      omega
  | @weak π C D d hc hw ih =>
    simp only [List.length_cons]
    rcases List.mem_cons.mp h with he | h
    · subst D
      have hh := falseBudget d hc (fun a ha => emptyImpossible a (hw a ha))
      omega
    · have hh := ih h
      omega
  | @res π C D R d hc hd hr ih =>
    simp only [List.length_cons]
    rcases List.mem_cons.mp h with he | h
    · subst R
      have hh := lastRes d hc hd hr
      omega
    · have hh := ih h
      omega

end PEqualNP.Outside.L_pcx_112

theorem PEqualNP.Outside.L_pcx_112 : ¬ (∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 3 × Fin 2)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 3 2) π ∧ π.length ≤ 17) := by
  rintro ⟨π,⟨d,he⟩,hb⟩
  have h := PEqualNP.Outside.L_pcx_112.lower d he
  omega
