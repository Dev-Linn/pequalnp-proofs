import PEqualNP.Defs
import PEqualNP.MetaComplexity.L100
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_764

open PEqualNP.MetaComplexity

def gk : (Fin 3 → Bool) → Bool := fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

theorem nonconst : ∃ y y' : Fin 3 → Bool, gk y ≠ gk y' :=
  ⟨fun _ => false, fun _ => true, by decide⟩

theorem mono {m : ℕ} {f : (Fin m → Bool) → Bool} {s t : ℕ} (h : HasCircuitSize m f s)
    (hst : s ≤ t) : HasCircuitSize m f t := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  exact ⟨C, hfan, le_trans hsz hst, hev⟩

theorem fun_eq : ∀ x : Fin (2 + 3) → Bool,
    ((x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) =
      ((x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || gk (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
  decide

theorem base (t : ℕ) : HasCircuitSize 3 gk t ↔ 4 ≤ t := L100 t

theorem main (s : ℕ) :
    HasCircuitSize (2 + 3) (fun x : Fin (2 + 3) → Bool =>
      (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || gk (fun j : Fin 3 => x (Fin.natAdd 2 j))) s
      ↔ 6 ≤ s := by
  rcases Nat.lt_or_ge s 2 with hs | hs
  · constructor
    · intro h
      have h2 := mono h (show s ≤ 2 by omega)
      have h3 := (PEqualNP.MetaComplexity.L153 3 0 gk nonconst).1 h2
      have h4 := (base 0).1 h3
      omega
    · intro h
      omega
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    rw [PEqualNP.MetaComplexity.L153 3 t gk nonconst, base t]
    omega

end PEqualNP.Outside.L_meta_764

theorem PEqualNP.Outside.L_meta_764 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s := by
  intro s
  have hf : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) =
      (fun x : Fin (2 + 3) → Bool =>
        (x (Fin.castAdd 3 0) && x (Fin.castAdd 3 1)) || PEqualNP.Outside.L_meta_764.gk (fun j : Fin 3 => x (Fin.natAdd 2 j))) := by
    funext x
    exact PEqualNP.Outside.L_meta_764.fun_eq x
  rw [hf]
  exact PEqualNP.Outside.L_meta_764.main s
