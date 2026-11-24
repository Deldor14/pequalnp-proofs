import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1916_1
    (nand : ∀ (D : Circuit) (i j : ℕ), D.size ≤ 12 → FanInTwo D →
      ∃ x : Fin 9 → Bool, let w := D.wires (List.ofFn x ++ [x 4 && x 6]);
        (!(w.getD i false && w.getD j false)) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (nor : ∀ (D : Circuit) (i j : ℕ), D.size ≤ 12 → FanInTwo D →
      ∃ x : Fin 9 → Bool, let w := D.wires (List.ofFn x ++ [x 4 && x 6]);
        (!(w.getD i false || w.getD j false)) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (tap : ∀ (D : Circuit) (i : ℕ), D.size ≤ 12 → FanInTwo D →
      ∃ x : Fin 9 → Bool, let w := D.wires (List.ofFn x ++ [x 4 && x 6]);
        (w.getD i false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let seed := fun x : Fin 9 → Bool => List.ofFn x ++ [x 4 && x 6]
  intro gs pins size fan _ _
  change ∃ x, GateOp.not.eval (pins.map fun i => (Circuit.wires ⟨gs,0⟩ (seed x)).getD i.val false) ≠ F x
  have zero : F (fun _ => false) = false := rfl
  have one : F (fun _ => true) = true := rfl
  cases pins with
  | nil => exact ⟨(fun _ => false), by change true ≠ F (fun _ => false); rw [zero]; decide⟩
  | cons p tail =>
    change ∃ x, (!((Circuit.wires ⟨gs,0⟩ (seed x)).getD p.val false)) ≠ F x
    obtain rfl | ⟨pre,g,rfl⟩ := List.eq_nil_or_concat' gs
    · have h := nand ⟨[],0⟩ p.val p.val (by decide) (by intro t ht; cases ht)
      simpa only [Bool.and_self] using h
    · let D : Circuit := ⟨pre,0⟩
      have hs : D.size ≤ 12 := by
        change pre.length ≤ 12
        simp only [List.length_append,List.length_cons,List.length_nil] at size
        omega
      have hf : FanInTwo D := by
        intro q hq
        exact fan q (List.mem_append_left _ hq)
      let w := fun x => D.wires (seed x)
      let v := fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)
      have ext (x) : Circuit.wires ⟨pre ++ [g],0⟩ (seed x) = w x ++ [v x] := by
        simp only [D,w,v,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
      have len (x) : (w x).length = 10 + pre.length := by
        have aux (ts : List Gate) (z : List Bool) :
            (Circuit.wires ⟨ts,0⟩ z).length = z.length + ts.length := by
          induction ts generalizing z with
          | nil => simp [Circuit.wires]
          | cons t ts ih =>
            change (Circuit.wires ⟨ts,0⟩ (z ++ [_])).length = _
            rw [ih]
            simp only [List.length_append,List.length_cons,List.length_nil]
            omega
        simpa [w,D,seed] using aux pre (seed x)
      by_cases hp : p.val = 10 + pre.length
      · have atp (x) : (Circuit.wires ⟨pre ++ [g],0⟩ (seed x)).getD p.val false = v x := by
          rw [ext, List.getD_append_right _ _ _ _ (by simp only [len,hp,Nat.le_refl]),len,hp,Nat.sub_self]
          rfl
        simp only [atp]
        obtain ⟨hop,arity⟩ := fan g (by simp)
        have ops : g.op = .and ∨ g.op = .or ∨ g.op = .not := hop
        rcases g with ⟨op,ins⟩
        change op = .and ∨ op = .or ∨ op = .not at ops
        change ins.length ≤ 2 at arity
        change ∃ x, (!(op.eval (ins.map fun i => (w x).getD i false))) ≠ F x
        rcases ops with rfl | rfl | rfl
        · cases ins with
          | nil => exact ⟨(fun _ => true), by change false ≠ F (fun _ => true); rw [one]; decide⟩
          | cons i rest =>
            cases rest with
            | nil => simpa [GateOp.eval,Bool.and_self,F,w,seed] using nand D i i hs hf
            | cons j rem =>
              have hrem : rem = [] := by
                cases rem with
                | nil => rfl
                | cons a l => simp only [List.length_cons] at arity; omega
              subst rem
              simpa [GateOp.eval,F,w,seed] using nand D i j hs hf
        · cases ins with
          | nil => exact ⟨(fun _ => false), by change true ≠ F (fun _ => false); rw [zero]; decide⟩
          | cons i rest =>
            cases rest with
            | nil => simpa [GateOp.eval,Bool.or_self,F,w,seed] using nor D i i hs hf
            | cons j rem =>
              have hrem : rem = [] := by
                cases rem with
                | nil => rfl
                | cons a l => simp only [List.length_cons] at arity; omega
              subst rem
              simpa [GateOp.eval,F,w,seed] using nor D i j hs hf
        · cases ins with
          | nil => exact ⟨(fun _ => true), by change false ≠ F (fun _ => true); rw [one]; decide⟩
          | cons i rest => simpa [GateOp.eval,F,w,seed] using tap D i hs hf
      · obtain ⟨x,hx⟩ := nand D p.val p.val hs hf
        refine ⟨x, ?_⟩
        rw [ext]
        have same : (w x ++ [v x]).getD p.val false = (w x).getD p.val false := by
          by_cases e : p.val < (w x).length
          · exact List.getD_append _ _ _ _ e
          · have beyond : (w x).length < p.val := by rw [len] at *; omega
            rw [List.getD_eq_default _ false (by simp; omega),List.getD_eq_default _ false (by omega)]
        rw [same]
        simpa only [Bool.and_self] using hx
