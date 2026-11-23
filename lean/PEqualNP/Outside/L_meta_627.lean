import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_627_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [step, ih]; omega

private def keepWire (m i : ℕ) : ℕ := if i < m then i else m + 8

private def extra (m u v o₁ o₂ : ℕ) : List Gate :=
  [⟨.or, [u, v]⟩,
   ⟨.and, [u, v]⟩,
   ⟨.not, [m + 1]⟩,
   ⟨.and, [m, m + 2]⟩,
   ⟨.not, [m + 3]⟩,
   ⟨.and, [keepWire m o₁, m + 4]⟩,
   ⟨.and, [keepWire m o₂, m + 3]⟩,
   ⟨.or, [m + 5, m + 6]⟩]

private lemma read_old (w tail : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ tail).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma read_new (w tail : List Bool) (j : ℕ) :
    (w ++ tail).getD (w.length + j) false = tail.getD j false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp

private lemma read_kept (w tail : List Bool) (i : ℕ) (h : tail.length ≤ 8) :
    (w ++ tail).getD (keepWire w.length i) false = w.getD i false := by
  by_cases hi : i < w.length
  · simp only [keepWire, ite_eq_left hi, read_old w tail i hi]
  · rw [keepWire, ite_eq_right hi, read_new, List.getD_eq_default _ _ h,
      List.getD_eq_default _ _ (by omega)]

private lemma run_extra (w : List Bool) (u v o₁ o₂ : ℕ) (hu : u < w.length) (hv : v < w.length) :
    ((extra w.length u v o₁ o₂).foldl step w).getD (w.length + 7) false =
      if w.getD u false = w.getD v false then w.getD o₁ false else w.getD o₂ false := by
  have head (tail : List Bool) : (w ++ tail).getD w.length false = tail.getD 0 false := by
    simpa using read_new w tail 0
  simp only [extra, List.foldl_cons, List.foldl_nil, step,
    List.append_assoc, List.singleton_append, List.map_cons, List.map_nil, GateOp.eval,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons,
    id_eq, Bool.and_true, Bool.or_false, read_old w _ u hu, read_old w _ v hv, head,
    read_new, List.getD_cons_zero, List.getD_cons_succ]
  cases w.getD u false <;> cases w.getD v false <;> simp
  all_goals exact read_kept w _ _ (by decide)

private lemma wire_prefix (gs : List Gate) (w : List Bool) : w <+: gs.foldl step w := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => exact (List.prefix_append _ _).trans (ih (step w g))

private lemma input_read {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    (C.wires (List.ofFn x)).getD u.val false = x u := by
  have h := List.prefix_iff_getElem?.1 (wire_prefix C.gates (List.ofFn x)) u.val (by simp)
  change ((C.gates.foldl step (List.ofFn x)).getD u.val false) = x u
  rw [List.getD_eq_getElem?_getD, h, List.getElem_ofFn]
  rfl

private lemma update_self_value {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    Function.update x u (x u) = x := by
  funext j
  by_cases h : j = u
  · subst j; simp
  · exact Function.update_of_ne h _ _

end PEqualNP.Outside.L_meta_627_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_627_aux

theorem PEqualNP.Outside.L_meta_627 :
    ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n),
      (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
        ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool,
          (C.wires (List.ofFn x)).getD o1 false = F (Function.update x u (x v)) ∧
          (C.wires (List.ofFn x)).getD o2 false = F (Function.update x u (!(x v)))) →
      PEqualNP.MetaComplexity.HasCircuitSize n F (s + 8) := by
  intro n s F u v h
  obtain ⟨C, hC, hs, o₁, o₂, he⟩ := h
  let m := n + C.gates.length
  let D : Circuit := ⟨C.gates ++ extra m u.val v.val o₁ o₂, m + 7⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ C.gates ++ extra m u.val v.val o₁ o₂ at hg
    rcases List.mem_append.mp hg with h | h
    · exact hC g h
    · simp only [extra, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · change (C.gates ++ extra m u.val v.val o₁ o₂).length ≤ s + 8
    change C.gates.length ≤ s at hs
    simpa [extra] using Nat.add_le_add_right hs 8
  · intro x
    let w := C.wires (List.ofFn x)
    have hw : w.length = m := by
      change (C.gates.foldl step (List.ofFn x)).length = m
      simp [fold_length, m]
    have h₁ : w.getD u.val false = x u := input_read C x u
    have h₂ : w.getD v.val false = x v := input_read C x v
    change ((C.gates ++ extra m u.val v.val o₁ o₂).foldl step (List.ofFn x)).getD (m + 7) false = F x
    rw [List.foldl_append]
    change ((extra m u.val v.val o₁ o₂).foldl step w).getD (m + 7) false = F x
    rw [← hw, run_extra w u.val v.val o₁ o₂ (by rw [hw]; have := u.isLt; dsimp [m]; omega)
      (by rw [hw]; have := v.isLt; dsimp [m]; omega), h₁, h₂]
    by_cases eq : x u = x v
    · rw [ite_eq_left eq, (he x).1, ← eq, update_self_value]
    · have ne : Bool.not (x v) = x u := by cases hu : x u <;> cases hv : x v <;> simp_all
      rw [ite_eq_right eq, (he x).2, ne, update_self_value]
