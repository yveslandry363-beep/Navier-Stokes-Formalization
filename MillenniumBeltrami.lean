import Mathlib

namespace MillenniumRigorous

def crossProduct (v w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i =>
    if h0 : i.val = 0 then v 1 * w 2 - v 2 * w 1
    else if h1 : i.val = 1 then v 2 * w 0 - v 0 * w 2
    else v 0 * w 1 - v 1 * w 0

theorem cross_product_self (v : Fin 3 → ℂ) :
    ∀ i, crossProduct v v i = 0 := by
  intro i
  unfold crossProduct
  split_ifs with h0
  · ring
  · split_ifs with h1
    · ring
    · ring

theorem lamb_force_annihilation (u : Fin 3 → ℂ) (c : ℂ) :
    ∀ i, crossProduct u (fun j => c * u j) i = 0 := by
  intro i
  unfold crossProduct
  split_ifs with h0
  · ring
  · split_ifs with h1
    · ring
    · ring

theorem beltrami_nonlinear_collapse
    (u ω : Fin 3 → ℂ) (c : ℂ)
    (h_align : ∀ j, ω j = c * u j) :
    ∀ i, crossProduct u ω i = 0 := by
  have h_subst : crossProduct u ω = crossProduct u (fun j => c * u j) := by
    ext i
    have h_eq : (fun j => ω j) = (fun j => c * u j) := by
      ext j
      exact h_align j
    rw [h_eq]
  rw [h_subst]
  exact lamb_force_annihilation u c

end MillenniumRigorous
