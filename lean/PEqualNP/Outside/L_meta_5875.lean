import PEqualNP.Defs

-- The first active AND argument is adapted from the checked L-meta-4039.
-- A backward zero certificate and the fourteen incidence rows give the new bound.

namespace PEqualNP.Outside.L_meta_5875_support_aux

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (h : Gate) (x : List Bool) :
    W (gs ++ [h]) x = W gs x ++ [h.op.eval (h.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs h ih => rw [W_snoc]; simp [ih]; omega

theorem W_low (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs h ih =>
    rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_len]; omega), ih]

theorem W_high (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (W gs x).getD i false = false := by
  apply List.getD_eq_default
  rw [W_len]; exact hi

theorem W_key (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate) (hg : gs[j]? = some g) :
    (W gs x).getD (x.length + j) false
      = g.op.eval (g.inputs.map fun i => if i < x.length + j then (W gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hg
  | append_singleton gs h ih =>
    rw [W_snoc]
    by_cases hj : j < gs.length
    · rw [List.getElem?_append_left hj] at hg
      rw [List.getD_append _ _ _ _ (by rw [W_len]; omega), ih hg]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < x.length + j
      · simp only [hi, ite_true]
        rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
      · simp [hi]
    · have hlen := (List.getElem?_eq_some_iff.mp hg).1
      simp at hlen
      have hj2 : j = gs.length := by omega
      subst hj2
      simp at hg
      subst hg
      have e : x.length + gs.length = (W gs x).length := by rw [W_len]
      rw [e, List.getD_append_right _ _ _ _ (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < (W gs x).length
      · simp only [hi, ite_true]
        rw [List.getD_append _ _ _ _ hi]
      · simp only [hi, ite_false]
        exact List.getD_eq_default _ _ (by omega)

def inp {n : ℕ} (S : Finset (Fin n)) : List Bool := List.ofFn fun (i : Fin n) => decide (i ∈ S)

def P {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i : ℕ) : Prop :=
  (W gs (inp S)).getD i false = true

theorem P_low {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    P gs S i ↔ (⟨i, hi⟩ : Fin n) ∈ S := by
  unfold P
  rw [W_low _ _ _ (by simp [inp]; exact hi)]
  simp [inp, List.getD_eq_getElem?_getD, hi]

theorem P_and {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (j : ℕ) (g : Gate)
    (hg : gs[j]? = some g) (ho : g.op = GateOp.and) :
    P gs S (n + j) ↔ ∀ i ∈ g.inputs, i < n + j ∧ P gs S i := by
  unfold P
  have h := W_key gs (inp S) j g hg
  have e : (inp S).length = n := by simp [inp]
  rw [e] at h
  rw [h, ho]
  simp [GateOp.eval, List.all_eq_true]

theorem P_or {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (j : ℕ) (g : Gate)
    (hg : gs[j]? = some g) (ho : g.op = GateOp.or) :
    P gs S (n + j) ↔ ∃ i ∈ g.inputs, i < n + j ∧ P gs S i := by
  unfold P
  have h := W_key gs (inp S) j g hg
  have e : (inp S).length = n := by simp [inp]
  rw [e] at h
  rw [h, ho]
  simp [GateOp.eval, List.any_eq_true]

theorem P_none {n : ℕ} (gs : List Gate) (S : Finset (Fin n)) (j : ℕ)
    (hg : gs[j]? = none) : ¬ P gs S (n + j) := by
  unfold P
  rw [W_high _ _ _ (by simp [inp]; exact List.getElem?_eq_none_iff.mp hg)]
  simp

theorem P_mono {n : ℕ} (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (S T : Finset (Fin n)) (hST : S ⊆ T) : ∀ i, P gs S i → P gs T i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases hi : i < n
    · rw [P_low _ _ _ hi] at h ⊢
      exact hST h
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      cases hg : gs[j]? with
      | none => exact absurd h (P_none gs S j hg)
      | some g =>
        rcases hm g (List.mem_of_getElem? hg) with ho | ho
        · rw [P_and _ _ _ _ hg ho] at h ⊢
          intro k hk
          exact ⟨(h k hk).1, ih k (h k hk).1 (h k hk).2⟩
        · rw [P_or _ _ _ _ hg ho] at h ⊢
          obtain ⟨k, hk, hlt, hp⟩ := h
          exact ⟨k, hk, hlt, ih k hlt hp⟩

theorem P_trace {n : ℕ} (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (S : Finset (Fin n)) : ∀ i, P gs S i →
      (∃ T ⊆ S, T.card ≤ 1 ∧ P gs T i) ∨
      (∃ j g, gs[j]? = some g ∧ g.op = GateOp.and ∧ n + j ≤ i ∧ P gs S (n + j)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases hi : i < n
    · left
      refine ⟨{⟨i, hi⟩}, ?_, by simp, ?_⟩
      · rw [P_low _ _ _ hi] at h
        simpa using h
      · rw [P_low _ _ _ hi]; simp
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      cases hg : gs[j]? with
      | none => exact absurd h (P_none gs S j hg)
      | some g =>
        rcases hm g (List.mem_of_getElem? hg) with ho | ho
        · right
          exact ⟨j, g, hg, ho, le_refl _, h⟩
        · rw [P_or _ _ _ _ hg ho] at h
          obtain ⟨k, hk, hlt, hp⟩ := h
          rcases ih k hlt hp with ⟨T, hTS, hc, hT⟩ | ⟨j2, g2, h1, h2, h3, h4⟩
          · left
            refine ⟨T, hTS, hc, ?_⟩
            rw [P_or _ _ _ _ hg ho]
            exact ⟨k, hk, hlt, hT⟩
          · right
            exact ⟨j2, g2, h1, h2, by omega, h4⟩

theorem P_union {n : ℕ} (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (S : Finset (Fin n)) : ∀ l : List ℕ, (∀ i ∈ l, ∃ T ⊆ S, T.card ≤ 1 ∧ P gs T i) →
      ∃ U ⊆ S, U.card ≤ l.length ∧ ∀ i ∈ l, P gs U i := by
  classical
  intro l
  induction l with
  | nil => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | cons a l ih =>
    intro h
    obtain ⟨T, hTS, hc, hT⟩ := h a (by simp)
    obtain ⟨U, hUS, hUc, hU⟩ := ih (fun i hi => h i (by simp [hi]))
    refine ⟨T ∪ U, Finset.union_subset hTS hUS, ?_, ?_⟩
    · have := Finset.card_union_le T U
      simp only [List.length_cons]
      omega
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact P_mono gs hm T _ Finset.subset_union_left _ hT
      · exact P_mono gs hm U _ Finset.subset_union_right _ (hU i hi)

end PEqualNP.Outside.L_meta_5875_support_aux

open PEqualNP.Outside.L_meta_5875_support_aux in
theorem PEqualNP.Outside.L_meta_5875_support : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     have x4 : Finset (Fin x1) → Prop := fun (x4 : Finset (Fin x1)) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 ∈ x4))).getD (x1 + x5) Bool.false = Bool.true;     ∀ (x5 : Finset (Fin x1)), x4 x5 → ∃ x7 ⊆ x5, x7.card ≤ (2 : ℕ) ∧ x4 x7 := by
  classical
  intro n C hM
  have hm : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have := (hM g hg).1
    simpa using this
  intro x4 S hS
  have hS2 : ∃ j, ∃ g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      P C.gates S (n + j) := hS
  have hmin := @Nat.find_min _ _ hS2
  obtain ⟨g, hg, ho, hp⟩ := Nat.find_spec hS2
  generalize Nat.find hS2 = j0 at hmin hg hp
  have hin := (P_and _ _ _ _ hg ho).mp hp
  have hall : ∀ i ∈ g.inputs, ∃ T ⊆ S, T.card ≤ 1 ∧ P C.gates T i := by
    intro i hi
    rcases P_trace C.gates hm S i (hin i hi).2 with h | ⟨j, g2, h1, h2, h3, h4⟩
    · exact h
    · exfalso
      have hlt : j < j0 := by have := (hin i hi).1; omega
      exact hmin hlt ⟨g2, h1, h2, h4⟩
  obtain ⟨U, hUS, hUc, hU⟩ := P_union C.gates hm S g.inputs hall
  have hlen := (hM g (List.mem_of_getElem? hg)).2
  refine ⟨U, hUS, by omega, ?_⟩
  show ∃ j, ∃ g, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      P C.gates U (n + j)
  refine ⟨j0, g, hg, ho, ?_⟩
  rw [P_and _ _ _ _ hg ho]
  intro i hi
  exact ⟨(hin i hi).1, hU i hi⟩


namespace PEqualNP.Outside.L_meta_5875_zero
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_5875_support_aux

def bit (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map (fun j => w.getD j false))

def isOr (g : Gate) : Bool := match g.op with
  | .or => true
  | _ => false

def dead (g : Gate) (w : List Bool) : Bool := isOr g && !(bit g w)

def count : List Gate → List Bool → Nat
  | [], _ => 0
  | g :: gs, w => (if dead g w then 1 else 0) + count gs (w ++ [bit g w])

lemma count_append (gs : List Gate) (g : Gate) (x : List Bool) :
    count (gs++[g]) x = count gs x + (if dead g (W gs x) then 1 else 0) := by
  induction gs generalizing x with
  | nil => simp [count,W]
  | cons a gs ih =>
    simp only [List.cons_append,count,ih,Nat.add_assoc]
    rfl

lemma wire_snoc (w : List Bool) (b : Bool) (i : Nat) :
    (w++[b]).getD i false = if i=w.length then b else w.getD i false := by
  rcases lt_trichotomy i w.length with h|rfl|h
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h,h.ne]
  · simp [List.getD_eq_getElem?_getD]
  · have h1 : w.length ≤ i := by omega
    have h2 : (w++[b]).length ≤ i := by simp; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none h1,List.getElem?_eq_none h2,h.ne']

lemma read_new (gs : List Gate) (g : Gate) (x : List Bool) (i : Nat) :
    (W (gs++[g]) x).getD i false =
      if i=x.length+gs.length then bit g (W gs x) else (W gs x).getD i false := by
  rw [W_snoc,wire_snoc,W_len]
  rfl

lemma gate_support (g : Gate) (w : List Bool) (shape : g.op = .and ∨ g.op = .or)
    (fan : g.inputs.length ≤ 2) (off : bit g w = false) :
    ∃ S : Finset Nat, S.card ≤ 1 + (if dead g w then 1 else 0) ∧
      (∀ i ∈ S, w.getD i false = false) ∧
      ∀ v : List Bool, (∀ i ∈ S, v.getD i false = false) → bit g v = false := by
  rcases shape with ha|ho
  · have ex : ∃ i ∈ g.inputs, w.getD i false = false := by
      by_contra! none
      have on : bit g w = true := by simpa [bit,ha,GateOp.eval,List.all_eq_true] using none
      rw [off] at on
      cases on
    obtain ⟨i,hi,offi⟩ := ex
    refine ⟨{i},by simp [dead,isOr,ha],by simpa using offi,?_⟩
    intro v hv
    have zero := hv i (Finset.mem_singleton_self i)
    apply Bool.eq_false_of_not_eq_true
    intro on
    have all : ∀ j ∈ g.inputs, v.getD j false = true := by
      simpa [bit,ha,GateOp.eval,List.all_eq_true] using on
    exact Bool.false_ne_true (zero.symm.trans (all i hi))
  · refine ⟨g.inputs.toFinset,?_,?_,?_⟩
    · have le := List.toFinset_card_le (l := g.inputs)
      simpa [dead,isOr,ho,off] using (show g.inputs.toFinset.card ≤ 2 by omega)
    · simpa [bit,ho,GateOp.eval,List.any_eq_false] using off
    · intro v hv
      simpa [bit,ho,GateOp.eval,List.any_eq_false] using hv

theorem support (gs : List Gate) (x : List Bool)
    (mono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (S : Finset Nat) (z : ∀ i ∈ S, (W gs x).getD i false = false) :
    ∃ T : Finset Nat, T.card ≤ S.card + count gs x ∧
      (∀ i ∈ T, x.getD i false = false) ∧
      ∀ y : List Bool, y.length = x.length → (∀ i ∈ T, y.getD i false = false) →
        ∀ i ∈ S, (W gs y).getD i false = false := by
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S,by simp [count],z,fun _ _ same => same⟩
  | append_singleton gs g ih =>
    have prior := fun a (h : a ∈ gs) => mono a (List.mem_append_left _ h)
    obtain ⟨shape,fan⟩ := mono g (List.mem_append_right _ (List.mem_singleton_self _))
    let iNew := x.length + gs.length
    by_cases used : iNew ∈ S
    · have off : bit g (W gs x) = false := by
        have v := z iNew used
        rw [read_new,ite_eq_left (show iNew = x.length+gs.length by rfl)] at v
        exact v
      obtain ⟨D,bound,offD,works⟩ := gate_support g (W gs x) shape fan off
      let U := S.erase iNew ∪ D
      have zeroU : ∀ i ∈ U, (W gs x).getD i false = false := by
        intro i hi
        rcases Finset.mem_union.mp hi with old|dep
        · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp old
          have v := z i mem
          rw [read_new,ite_eq_right (show i ≠ x.length+gs.length from ne)] at v
          exact v
        · exact offD i dep
      obtain ⟨T,small,zero,valid⟩ := ih prior U zeroU
      refine ⟨T,?_,zero,?_⟩
      · rw [count_append]
        have s1 := Finset.card_union_le (S.erase iNew) D
        have s2 := Finset.card_erase_add_one used
        change T.card ≤ (S.erase iNew ∪ D).card + count gs x at small
        omega
      · intro y len eq i hi
        have old := valid y len eq
        rw [read_new,len]
        by_cases same : i = iNew
        · rw [ite_eq_left same]
          exact works _ (fun j hj => old j (Finset.mem_union_right _ hj))
        · rw [ite_eq_right same]
          exact old i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨same,hi⟩))
    · have prev : ∀ i ∈ S, (W gs x).getD i false = false := by
        intro i hi
        have ne : i ≠ iNew := by rintro rfl; exact used hi
        have v := z i hi
        rw [read_new,ite_eq_right (show i ≠ x.length+gs.length from ne)] at v
        exact v
      obtain ⟨T,small,zero,valid⟩ := ih prior S prev
      refine ⟨T,by rw [count_append]; omega,zero,?_⟩
      intro y len eq i hi
      have ne : i ≠ iNew := by rintro rfl; exact used hi
      rw [read_new,len,ite_eq_right (show i ≠ x.length+gs.length from ne)]
      exact valid y len eq i hi


theorem sensitivity {n : Nat} (C : Circuit) (mono : Monotone2 C) (x : Fin n → Bool)
    (B : Finset (Fin n)) (off : C.eval (List.ofFn x) = false)
    (on : ∀ b ∈ B, C.eval (List.ofFn fun i => if i=b then true else x i) = true) :
    B.card ≤ count C.gates (List.ofFn x) + 1 := by
  classical
  have shape : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g h
    exact ⟨by simpa [Set.mem_insert_iff] using (mono g h).1, (mono g h).2⟩
  have stop : ∀ i ∈ ({C.output} : Finset Nat), (W C.gates (List.ofFn x)).getD i false = false := by
    intro i hi
    have same := Finset.mem_singleton.mp hi
    subst i
    exact off
  obtain ⟨T,small,zero,valid⟩ := support C.gates (List.ofFn x) shape {C.output} stop
  have lookup (f : Fin n → Bool) (j : Nat) (h : j<n) :
      (List.ofFn f).getD j false = f ⟨j,h⟩ := by simp [List.getD_eq_getElem?_getD,h]
  have hp (b : Fin n) (hb : b ∈ B) : b.val ∈ T := by
    by_contra absent
    let y := fun i => if i=b then true else x i
    have keep : ∀ j ∈ T, (List.ofFn y).getD j false = false := by
      intro j hj
      by_cases bound : j<n
      · have ne : (⟨j,bound⟩ : Fin n) ≠ b := by
          intro same
          exact absent ((congrArg Fin.val same) ▸ hj)
        rw [lookup y j bound]
        have hz := zero j hj
        rw [lookup x j bound] at hz
        simpa [y,ne] using hz
      · exact List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt bound)
    have v := valid (List.ofFn y) (by simp) keep C.output (Finset.mem_singleton_self _)
    exact Bool.false_ne_true (v.symm.trans (on b hb))
  have sub : B.image Fin.val ⊆ T := by
    intro j hj
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hj
    exact hp b hb
  have bd := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at bd
  simp only [Finset.card_singleton] at small
  omega

def flag (gs : List Gate) (x : List Bool) (j : Nat) : Bool :=
  (gs[j]?.map isOr).getD false && !(W gs x).getD (x.length+j) false

def byIndex (gs : List Gate) (x : List Bool) : Nat :=
  ((Finset.range gs.length).filter (fun j => flag gs x j = true)).card

theorem byIndex_eq (gs : List Gate) (x : List Bool) : byIndex gs x = count gs x := by
  induction gs using List.reverseRecOn with
  | nil => simp [byIndex,count]
  | append_singleton gs g ih =>
    let n := gs.length
    have old (j : Nat) (hj : j < n) : flag (gs++[g]) x j = flag gs x j := by
      have ne : x.length+j ≠ x.length+gs.length := by change j < gs.length at hj; omega
      simp only [flag,List.getElem?_append_left (show j < gs.length from hj),read_new,ite_eq_right ne]
    have last : flag (gs++[g]) x n = dead g (W gs x) := by
      simp only [flag,read_new,n]
      simp [dead]
    let L := fun j => flag (gs++[g]) x j = true
    have same : (Finset.range n).filter L = (Finset.range n).filter (fun j => flag gs x j = true) := by
      apply Finset.filter_congr
      intro j hj
      exact congrArg (fun b => b = true) (old j (Finset.mem_range.mp hj)) |>.to_iff
    have fresh : n ∉ (Finset.range n).filter L := by simp
    have curr : byIndex (gs++[g]) x = ((insert n (Finset.range n)).filter L).card := by
      change ((Finset.range (gs++[g]).length).filter L).card = _
      rw [List.length_append,List.length_singleton,Finset.range_add_one]
    rw [curr,Finset.filter_insert,count_append,←ih]
    by_cases ld : L n
    · rw [ite_eq_left ld,Finset.card_insert_of_notMem fresh,same]
      have v : dead g (W gs x) = true := last ▸ ld
      simp [v,byIndex,n]
    · rw [ite_eq_right ld,same]
      have v : dead g (W gs x) = false := Bool.eq_false_of_not_eq_true (fun h => ld (last.trans h))
      simp [v,byIndex,n]

end PEqualNP.Outside.L_meta_5875_zero

namespace PEqualNP.Outside.L_meta_5875_Family
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_5875_zero

def ms : List Nat := [693637218693,214750724172,43100670213,2201724715076,429513539622,
  10838245382,1718003696225,1387274437386,3436007392450,214756769811,412337856832,
  3436108316976,154640061441,1168315262978]

def bits (m : Nat) : Finset (Fin 42) := Finset.univ.filter (fun i => m.testBit i.val = true)

def positions : List Nat := [0,1,2,6,8,18,24,31,33,37]
def designated : Finset (Fin 42) := Finset.univ.filter (fun i => i.val ∈ positions)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem pairs_covered : ∀ u v : Fin 42, u ∈ designated → v ∈ designated →
    ∃ k : Fin 14, (ms.get k).testBit u.val = true ∧ (ms.get k).testBit v.val = true := by
  decide +kernel

lemma small_in_row (Y : Finset (Fin 42)) (inside : Y ⊆ designated) (small : Y.card ≤ 2) :
    ∃ k : Fin 14, Y ⊆ bits (ms.get k) := by
  classical
  by_cases empty : Y = ∅
  · exact ⟨0, by simp [empty]⟩
  obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  by_cases single : Y.card ≤ 1
  · obtain ⟨k,hk,_⟩ := pairs_covered a a (inside ha) (inside ha)
    refine ⟨k,?_⟩
    intro b hb
    have eq : b = a := Finset.card_le_one.mp single b hb a ha
    simpa [bits,eq] using hk
  · obtain ⟨u,v,_,heq⟩ := Finset.card_eq_two.mp (show Y.card = 2 by omega)
    have hu : u ∈ Y := by simp [heq]
    have hv : v ∈ Y := by simp [heq]
    obtain ⟨k,ku,kv⟩ := pairs_covered u v (inside hu) (inside hv)
    refine ⟨k,?_⟩
    rw [heq]
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ku⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,kv⟩


def active (C : Circuit) (Y : Finset (Fin 42)) : Prop := ∃ j g,
  C.gates[j]? = some g ∧ g.op = .and ∧
  (C.wires (List.ofFn fun i => decide (i ∈ Y))).getD (42+j) false = true

theorem active_transfers (C : Circuit) (hC : Monotone2 C) (ha : active C designated) :
    ∃ k, active C (bits (ms.get k)) := by
  obtain ⟨Y,inside,small,j,g,hj,hg,hval⟩ := PEqualNP.Outside.L_meta_5875_support 42 C hC designated ha
  obtain ⟨k,cover⟩ := small_in_row Y inside small
  refine ⟨k,j,g,hj,hg,?_⟩
  have shape : ∀ a ∈ C.gates, a.op = .and ∨ a.op = .or := by
    intro a h
    simpa [Set.mem_insert_iff] using (hC a h).1
  exact PEqualNP.Outside.L_meta_5875_support_aux.P_mono C.gates shape Y (bits (ms.get k)) cover (42+j) hval



abbrev E (u v : Fin 42) : Prop := u.val < 21 ∧ 21 ≤ v.val ∧
    (v.val+21-u.val)%21 ∈ ([0,5,7,17,20] : List Nat)

def good (x : Fin 42 → Bool) : Prop := ∃ u v : Fin 42, E u v ∧ x u=true ∧ x v=true

def r (m : Nat) (i : Fin 42) : Bool := m.testBit i.val
def outsideBits (m : Nat) : Finset (Fin 42) := Finset.univ.filter fun i => r m i = false

theorem size_out : ∀ k : Fin 14, (outsideBits (ms.get k)).card = 34 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem noedge : ∀ k : Fin 14, ¬ good (r (ms.get k)) := by unfold good; decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem dominates : ∀ (k : Fin 14) (b : Fin 42), r (ms.get k) b = false →
    ∃ j : Fin 42, r (ms.get k) j = true ∧ (E b j ∨ E j b) := by decide +kernel

noncomputable def counted (C : Circuit) (m : Nat) : Finset Nat := (Finset.range C.size).filter fun j =>
  ((C.gates[j]?.map (fun g => GateOp.rec false true false (fun _ => false) false g.op)).getD false &&
    !(C.wires (List.ofFn (r m))).getD (42+j) false) = true

def hit (C : Circuit) (x : Fin 42 → Bool) : Prop := ∃ j g, C.gates[j]? = some g ∧ g.op = .and ∧
  (C.wires (List.ofFn x)).getD (42+j) false = true

theorem card_bound (C : Circuit) (hm : Monotone2 C)
    (correct : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x)=true ↔ good x) (k : Fin 14) :
    33 ≤ (counted C (ms.get k)).card := by
  let m := ms.get k
  have off : C.eval (List.ofFn (r m))=false :=
    Bool.eq_false_of_not_eq_true (fun h => noedge k ((correct _).mp h))
  have on (b : Fin 42) (hb : b ∈ outsideBits m) :
      C.eval (List.ofFn fun i => if i=b then true else r m i) = true := by
    obtain ⟨j,hj,adj⟩ := dominates k b (Finset.mem_filter.mp hb).2
    apply (correct _).mpr
    have hj' : (if j=b then true else r m j) = true := by simp [show r m j=true from hj]
    rcases adj with bj|jb
    · exact ⟨b,j,bj,by simp,hj'⟩
    · exact ⟨j,b,jb,hj',by simp⟩
  have lower := sensitivity C hm (r m) (outsideBits m) off on
  rw [show (outsideBits m).card = 34 from size_out k,← byIndex_eq] at lower
  have tagEq (g : Gate) : isOr g = GateOp.rec false true false (fun _ => false) false g.op := by
    cases g with | mk op reads => cases op <;> rfl
  have tagF : isOr = (fun g => GateOp.rec false true false (fun _ => false) false g.op) := funext tagEq
  have same : byIndex C.gates (List.ofFn (r m)) = (counted C m).card := by
    unfold byIndex counted
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro j _
    unfold flag
    rw [List.length_ofFn,tagF]
    rfl
  rw [same] at lower
  change 33 ≤ (counted C m).card
  omega

theorem result : ∀ (C : Circuit), Monotone2 C →
    (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔ good x) →
    hit C (fun i : Fin 42 => decide (i.val ∈ positions)) →
    (∃ m ∈ ms, hit C (r m)) ∧ ∀ m ∈ ms, 33 ≤ (counted C m).card := by
  intro C mono ok ha
  have plain : (fun i : Fin 42 => decide (i ∈ designated)) =
      (fun i : Fin 42 => decide (i.val ∈ positions)) := by funext i; simp [designated]
  have hx : active C designated := by
    change hit C (fun i : Fin 42 => decide (i ∈ designated))
    rw [plain]
    exact ha
  obtain ⟨k,hk⟩ := active_transfers C mono hx
  constructor
  · refine ⟨ms.get k,List.get_mem _ _,?_⟩
    have bitsEq : (fun i : Fin 42 => decide (i ∈ bits (ms.get k))) = r (ms.get k) := by
      funext i
      simp [bits,r]
    change hit C (fun i : Fin 42 => decide (i ∈ bits (ms.get k))) at hk
    rwa [bitsEq] at hk
  · intro m mem
    obtain ⟨i,ei⟩ := List.mem_iff_get.mp mem
    exact ei ▸ card_bound C mono ok i

end PEqualNP.Outside.L_meta_5875_Family

theorem PEqualNP.Outside.L_meta_5875 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) →       have x4 : List ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (3436108316976 : ℕ), (154640061441 : ℕ), (1168315262978 : ℕ)];       have x5 : ℕ → Fin (42 : ℕ) → Bool := fun (x5 : ℕ) (x6 : Fin (42 : ℕ)) => x5.testBit ↑x6;       have x6 : (Fin (42 : ℕ) → Bool) → Prop := fun (x6 : Fin (42 : ℕ) → Bool) => ∃ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x7]? = Option.some x8 ∧ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn x6)).getD ((42 : ℕ) + x7) Bool.false = Bool.true;       have x7 : ℕ → Finset ℕ := fun (x7 : ℕ) => {x8 ∈ Finset.range x1.size | ((Option.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (x10 : ℕ) => Bool.false) Bool.false x9.op) x1.gates[x8]?).getD Bool.false && !(x1.wires (List.ofFn (x5 x7))).getD ((42 : ℕ) + x8) Bool.false) = Bool.true};       (x6 fun (x8 : Fin (42 : ℕ)) => Decidable.decide (↑x8 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)])) → (∃ x9 ∈ x4, x6 (x5 x9)) ∧ ∀ x9 ∈ x4, (33 : ℕ) ≤ (x7 x9).card := by
  exact PEqualNP.Outside.L_meta_5875_Family.result
