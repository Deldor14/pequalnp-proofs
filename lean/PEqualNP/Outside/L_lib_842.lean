import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_842

theorem allocate (q : ℕ) (M : Fin q → ℕ) (d : ℕ) (enough : d ≤ ∑ j, M j) :
    ∃ x : Fin q → ℕ, (∀ j, x j ≤ M j) ∧ (∑ j, x j) = d := by
  induction q generalizing d with
  | zero =>
    have hd : d=0 := by simpa using enough
    exact ⟨M,fun _ => le_rfl,by simp [hd]⟩
  | succ n ih =>
    rw [Fin.sum_univ_succ] at enough
    let k := min d (M 0)
    have rem : d-k ≤ ∑ j : Fin n, M j.succ := by dsimp [k]; omega
    obtain ⟨y,hy,sy⟩ := ih (fun j => M j.succ) (d-k) rem
    refine ⟨Fin.cases k y,?_,?_⟩
    · intro i; refine Fin.cases (min_le_right ..) (fun j => hy j) i
    · rw [Fin.sum_univ_succ]; simp only [Fin.cases_zero,Fin.cases_succ,sy]; dsimp [k]; omega

theorem splitRows {q : ℕ} (E n : ℕ) (v : Fin q → ℕ) (hv : ∑ j, v j = n * E) :
    ∃ h : Fin n → Fin q → ℕ, (∀ i, ∑ j, h i j = E) ∧ ∀ j, ∑ i, h i j = v j := by
  induction n generalizing v with
  | zero =>
    simp only [Nat.zero_mul] at hv
    refine ⟨Fin.elim0,fun i => Fin.elim0 i,fun j => ?_⟩
    have le : v j ≤ ∑ i, v i := Finset.single_le_sum (f:=v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp [hv] at le; simp [le]
  | succ n ih =>
    rw [Nat.succ_mul] at hv
    obtain ⟨x,hx,sx⟩ := allocate q v E (by omega)
    let r (j : Fin q) := v j-x j
    have sr : ∑ j, r j = n * E := by
      have eq := Finset.sum_congr (s₁:=Finset.univ) (f:=v) (g:=fun j => x j+r j) rfl (fun j _ => (Nat.add_sub_of_le (hx j)).symm)
      rw [Finset.sum_add_distrib,sx] at eq
      have eq2 : (∑ j, v j) = E + ∑ j, r j := eq
      exact Nat.add_left_cancel (eq2.symm.trans (hv.trans (Nat.add_comm _ _)))
    obtain ⟨h,hs,hc⟩ := ih r sr
    refine ⟨Fin.cases x h,?_,?_⟩
    · intro i; exact Fin.cases sx (fun j => hs j) i
    · intro j; rw [Fin.sum_univ_succ]; simp only [Fin.cases_zero,Fin.cases_succ,hc]; exact Nat.add_sub_of_le (hx j)

def load (D : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => 2*load D n + D n

theorem load_congr {a b : ℕ → ℕ} (n : ℕ) (eq : ∀ i<n, a i=b i) : load a n = load b n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [load,load,ih (fun i hi => eq _ (by omega)),eq n (by omega)]

theorem load_sum {q : ℕ} (A : ℕ → Fin q → ℕ) (n : ℕ) :
    (∑ j, load (fun i => A i j) n) = load (fun i => ∑ j, A i j) n := by
  induction n with
  | zero => simp [load]
  | succ n ih => simp only [load,Finset.sum_add_distrib,←Finset.mul_sum,ih]

theorem prefix_le (D : ℕ → ℕ) (a d : ℕ) : 2^d * load D a ≤ load D (a+d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      2^(d+1)*load D a = 2*(2^d*load D a) := by rw [pow_succ]; ring
      _ ≤ 2*load D (a+d)+D (a+d) := by omega
      _ = load D (a+(d+1)) := rfl

theorem dyadic_pack {q : ℕ} (n : ℕ) (D : ℕ → ℕ) (M : Fin q → ℕ)
    (cuts : ∀ b ≤ n, load D b ≤ ∑ j, M j / 2^(n-b)) :
    ∃ A : ℕ → Fin q → ℕ, (∀ b<n, ∑ j, A b j = D b) ∧
      ∀ j, load (fun i => A i j) n ≤ M j := by
  induction n generalizing M with
  | zero => exact ⟨fun _ _ => 0,by simp,by simp [load]⟩
  | succ n ih =>
    have subcuts : ∀ b ≤ n, load D b ≤ ∑ j, (M j/2) / 2^(n-b) := by
      intro b hb
      have h := cuts b (by omega)
      simpa only [Nat.succ_sub hb,pow_succ,Nat.div_div_eq_div_mul,Nat.mul_comm 2] using h
    obtain ⟨A,rows,cols⟩ := ih (fun j => M j/2) subcuts
    let U (j : Fin q) := load (fun i => A i j) n
    have le (j) : 2*U j ≤ M j := by have := cols j; dsimp [U]; omega
    have su : ∑ j, U j = load D n := (load_sum A n).trans (load_congr _ rows)
    have S := cuts (n+1) (by omega)
    simp only [Nat.sub_self,pow_zero,Nat.div_one,load] at S
    let R (j : Fin q) := M j - 2*U j
    have tot : ∑ j, M j = 2*load D n + ∑ j, R j := by
      rw [←su,Finset.mul_sum,←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => (Nat.add_sub_of_le (le j)).symm)
    obtain ⟨x,hx,sx⟩ := allocate q R (D n) (by omega)
    let B (i : ℕ) := if i=n then x else A i
    refine ⟨B,?_,?_⟩
    · intro b hb; by_cases he : b=n
      · simpa [B,he] using sx
      · simpa [B,he] using rows b (by omega)
    · intro j
      have hU : load (fun i => B i j) n = U j := load_congr n (fun i hi => by simp [B,show i ≠ n by omega])
      rw [load,hU]; simp only [B,ite_true]; have h := hx j; change x j ≤ M j - 2*U j at h; have := le j; omega
theorem load_fin (D : ℕ → ℕ) (n : ℕ) : load D n = ∑ i : Fin n, 2^(n-1-i.val)*D i.val := by
  induction n with
  | zero => simp [load]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc,load,ih,Finset.mul_sum]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.add_one_sub_one,Nat.sub_self,pow_zero,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show n-i.val=(n-1-i.val)+1 by have := i.isLt; omega,pow_succ]; ring

def cap {q} (p : ℕ) (M : Fin q → ℕ) (b : ℕ) := ∑ j, M j / 2^(p-b)
def best {q} (p E : ℕ) (M : Fin q → ℕ) (b : ℕ) := 2^b-cap p M b/E
def Shape (p : ℕ) (u : ℕ → ℕ) := u 0=1 ∧ u p=1 ∧ ∀ b<p, u (b+1)≤2*u b
def exits (u : ℕ → ℕ) (i : ℕ) := 2*u i-u (i+1)
def Fits {q} (p E : ℕ) (M : Fin q → ℕ) (u : ℕ → ℕ) :=
  ∃ h : (i : Fin p) → Fin (exits u i.val) → Fin q → ℕ,
    (∀ i w, (∑ j, h i w j)=E) ∧ ∀ j, (∑ i : Fin p, 2^(p-1-i.val) * ∑ w, h i w j)=M j

theorem shape_pow {p u} (hu : Shape p u) (b) (hb : b≤p) : u b≤2^b := by
  induction b with
  | zero => simp [hu.1]
  | succ b ih => have := ih (by omega); have := hu.2.2 b (by omega); rw [pow_succ]; omega

theorem load_exits {p u} (hu : Shape p u) (E b : ℕ) (hb : b≤p) :
    load (fun i => exits u i * E) b = (2^b-u b)*E := by
  induction b with
  | zero => simp [load,hu.1]
  | succ b ih =>
    have ub := shape_pow hu b (by omega)
    have next := hu.2.2 b (by omega)
    have eq : 2^(b+1)-u (b+1) = 2*(2^b-u b)+exits u b := by rw [pow_succ]; unfold exits; omega
    rw [load,ih (by omega),eq]; ring

theorem cuts_iff {q p E u} (M : Fin q → ℕ) (hE : 0<E) (hu : Shape p u) (b) (hb : b≤p) :
    load (fun i => exits u i * E) b ≤ cap p M b ↔ best p E M b ≤ u b := by
  rw [load_exits hu E b hb,←Nat.le_div_iff_mul_le hE]
  change (2^b-u b ≤ cap p M b/E) ↔ (2^b-cap p M b/E ≤ u b)
  simp only [Nat.sub_le_iff_le_add]; rw [Nat.add_comm (cap p M b/E)]

theorem shape_best {q p E} (M : Fin q → ℕ) (hE : 0<E) (total : ∑ j, M j=(2^p-1)*E) :
    Shape p (best p E M) := by
  have P : 0 < 2^p := by positivity
  have low : cap p M 0 * 2^p ≤ ∑ j, M j := by
    simp only [cap,Nat.sub_zero,Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => Nat.div_mul_le_self _ _)
  have lt : cap p M 0 < E := by
    by_contra! hh
    have a := Nat.mul_le_mul_right (2^p) hh
    have s := Nat.mul_lt_mul_of_pos_right (show 2^p-1<2^p by omega) hE
    rw [Nat.mul_comm E] at a
    omega
  refine ⟨by simp [best,Nat.div_eq_of_lt lt],?_,?_⟩
  · simp [best,cap,total,Nat.mul_div_cancel _ hE]; omega
  · intro b hb
    have scale : 2*cap p M b ≤ cap p M (b+1) := by
      simp only [cap,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [show p-b=(p-(b+1))+1 by omega,pow_succ,←Nat.div_div_eq_div_mul]
      omega
    have d := Nat.div_mul_le_self (cap p M b) E
    have h : 2 * (cap p M b/E) ≤ cap p M (b+1)/E := (Nat.le_div_iff_mul_le hE).mpr (by
      rw [Nat.mul_assoc]; omega)
    unfold best
    rw [pow_succ]; omega
theorem fits_iff {q p E u} (M : Fin q → ℕ) (hE : 0<E) (total : ∑ j, M j=(2^p-1)*E)
    (hu : Shape p u) : Fits p E M u ↔ ∀ b ≤ p, best p E M b ≤ u b := by
  let D (i : ℕ) := exits u i * E
  constructor
  · rintro ⟨h,hs,ht⟩ b hb
    let A (i : ℕ) (j : Fin q) := if hi : i<p then ∑ w, h ⟨i,hi⟩ w j else 0
    have rows (i) (hi : i<p) : ∑ j, A i j = D i := by
      simp only [A,dite_eq_left hi]; rw [Finset.sum_comm]; simp [hs,D]
    have cols (j) : load (fun i => A i j) p = M j := by
      rw [load_fin]; simpa only [A,dite_eq_left (Fin.isLt _)] using ht j
    apply (cuts_iff M hE hu b hb).mp
    change load D b ≤ _
    rw [←load_congr b (a:=fun i => ∑ j, A i j) (fun i hi => rows i (by omega)),←load_sum]
    apply Finset.sum_le_sum
    intro j _
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    have h := prefix_le (fun i => A i j) b (p-b)
    rw [show b+(p-b)=p by omega,cols,Nat.mul_comm] at h
    exact h
  · intro fits
    obtain ⟨A,rows,cols⟩ := dyadic_pack p D M (fun b hb => (cuts_iff M hE hu b hb).mpr (fits b hb))
    have tot : ∑ j, load (fun i => A i j) p = ∑ j, M j := by
      rw [load_sum,load_congr p rows]; change load (fun i => exits u i * E) p = _
      rw [load_exits hu E p le_rfl,hu.2.1,total]
    have each := (Finset.sum_eq_sum_iff_of_le (s:=Finset.univ) (fun j _ => cols j)).mp tot
    have hh (i : Fin p) := splitRows E (exits u i.val) (A i.val) (rows i.val i.isLt)
    choose h hs ht using hh
    refine ⟨h,hs,?_⟩
    intro j
    simp_rw [ht]; exact (load_fin (fun i => A i j) p).symm.trans (each j (Finset.mem_univ _))
end PEqualNP.Outside.L_lib_842

open PEqualNP.Outside.L_lib_842

theorem PEqualNP.Outside.L_lib_842 : ∀ (p E q : ℕ), 0 < p → 0 < E → ∀ M : Fin q → ℕ,
  (∑ j, M j) = (2^p-1)*E →
  let cap := fun b : ℕ => ∑ j, M j / 2^(p-b)
  let best := fun b : ℕ => 2^b-cap b/E
  let shape := fun u : ℕ → ℕ =>
    u 0 = 1 ∧ u p = 1 ∧ ∀ b < p, u (b+1) ≤ 2*u b
  let fits := fun u : ℕ → ℕ =>
    ∃ h : (i : Fin p) → Fin (2*u i.val-u (i.val+1)) → Fin q → ℕ,
      (∀ i w, (∑ j, h i w j) = E) ∧
      ∀ j, (∑ i : Fin p, 2^(p-1-i.val) * ∑ w, h i w j) = M j
  (∀ u, shape u → (fits u ↔ ∀ b ≤ p, best b ≤ u b)) ∧ shape best ∧ fits best := by
  intro p E q _ hE M total
  change (∀ u, Shape p u → (Fits p E M u ↔ ∀ b ≤ p, best p E M b ≤ u b)) ∧ Shape p (best p E M) ∧ Fits p E M (best p E M)
  have sh := shape_best M hE total
  exact ⟨fun u hu => fits_iff M hE total hu,sh,(fits_iff M hE total sh).mpr (fun _ _ => le_rfl)⟩
