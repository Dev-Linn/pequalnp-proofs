import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765

open PEqualNP.MetaComplexity

def gk : (Fin 4 → Bool) → Bool := fun x : Fin 4 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)

theorem nonconst : ∃ y y' : Fin 4 → Bool, gk y ≠ gk y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

theorem mono {m : ℕ} {f : (Fin m → Bool) → Bool} {s t : ℕ} (h : HasCircuitSize m f s)
    (hst : s ≤ t) : HasCircuitSize m f t := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  exact ⟨C, hfan, le_trans hsz hst, hev⟩

theorem fun_eq : ∀ x : Fin (2 + 4) → Bool,
    ((x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) =
      ((x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || gk (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
  decide

theorem base (t : ℕ) : HasCircuitSize 4 gk t ↔ 3 ≤ t := L112 t

theorem main (s : ℕ) :
    HasCircuitSize (2 + 4) (fun x : Fin (2 + 4) → Bool =>
      (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || gk (fun j : Fin 4 => x (Fin.natAdd 2 j))) s
      ↔ 5 ≤ s := by
  rcases Nat.lt_or_ge s 2 with hs | hs
  · constructor
    · intro h
      have h2 := mono h (show s ≤ 2 by omega)
      have h3 := (PEqualNP.MetaComplexity.L153 4 0 gk nonconst).1 h2
      have h4 := (base 0).1 h3
      omega
    · intro h
      omega
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    rw [PEqualNP.MetaComplexity.L153 4 t gk nonconst, base t]
    omega

end PEqualNP.Outside.L_meta_765

theorem PEqualNP.Outside.L_meta_765 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s := by
  intro s
  have hf : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) =
      (fun x : Fin (2 + 4) → Bool =>
        (x (Fin.castAdd 4 0) && x (Fin.castAdd 4 1)) || PEqualNP.Outside.L_meta_765.gk (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
    funext x
    exact PEqualNP.Outside.L_meta_765.fun_eq x
  rw [hf]
  exact PEqualNP.Outside.L_meta_765.main s
