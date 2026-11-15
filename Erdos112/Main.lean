import Erdos112.Lower
import Erdos112.Upper

/-!
# Main theorem: `30 ≤ k(6,3) ≤ 32` (paper, Theorem 1)
-/

namespace Erdos112

/-- From the relative form to graphs on a finite vertex type: if `Bound n N` holds, no
oriented graph on at least `N` vertices is `{I_n, L_3}`-free. -/
theorem not_free_of_bound {n N : ℕ} (h : Bound n N) {V : Type} [Fintype V]
    (hV : N ≤ Fintype.card V) (D : OGraph V) : ¬ D.Free n := by
  rintro ⟨hTT, hI⟩
  have hS : D.NoIndep Finset.univ n := by
    intro T _ hT
    by_contra hc
    obtain ⟨T', hT', hc'⟩ := Finset.exists_subset_card_eq (show n ≤ T.card by omega)
    exact hI T' (D.isIndep_mono hT hT') hc'
  have h1 := h V D hTT Finset.univ hS
  rw [Finset.card_univ] at h1
  omega

/-- **Theorem 10 of the paper**: there is no `{I_6, L_3}`-free oriented graph on 32 vertices
(or more). Depends on the two `native_decide` runs of Lemma 8. -/
theorem upper_bound {V : Type} [Fintype V] (hV : 32 ≤ Fintype.card V) (D : OGraph V) :
    ¬ D.Free 6 := not_free_of_bound bound_6_32 hV D

/-- **Theorem 5 of the paper**: there is an `{I_6, L_3}`-free oriented graph on 29 vertices.
Kernel-checked. -/
theorem lower_bound : ∃ D : OGraph (Fin 29), D.Free 6 := ⟨G29, G29_free⟩

/-- Restricting `G_29` to its first `k` vertices: `{I_6, L_3}`-free oriented graphs exist on
every number of vertices up to 29. -/
theorem exists_free_of_le {k : ℕ} (hk : k ≤ 29) : ∃ D : OGraph (Fin k), D.Free 6 := by
  have hf : Function.Injective (Fin.castLE hk) := Fin.castLE_injective hk
  refine ⟨⟨fun i j => G29.arc (Fin.castLE hk i) (Fin.castLE hk j),
    fun i j h => G29.asymm _ _ h⟩, ?_, ?_⟩
  · rintro ⟨x, y, z, h1, h2, h3⟩
    exact G29_free.1 ⟨Fin.castLE hk x, Fin.castLE hk y, Fin.castLE hk z, h1, h2, h3⟩
  · intro T hT h6
    refine G29_free.2 (T.image (Fin.castLE hk)) ?_
      (by rw [Finset.card_image_of_injective T hf]; exact h6)
    intro p hp q hq hpq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
    exact hT i hi j hj hpq

/-- The recursion `k(n+1,3) ≤ k(n,3) + 2n + 1` alone gives `k(6,3) ≤ 36`. This is used only
to know, without any computation, that the set defining `k3 6` is not empty. -/
theorem bound_6_36 : Bound 6 36 := bound_succ (bound_succ (bound_succ bound_3_9))

/-- `k(6,3) ≥ 30`. Kernel-checked (no `native_decide`). -/
theorem k63_ge : 30 ≤ k3 6 := by
  unfold k3
  apply le_csInf
  · exact ⟨36, fun D => not_free_of_bound bound_6_36 (by simp) D⟩
  · intro k hk
    by_contra hlt
    obtain ⟨D, hD⟩ := exists_free_of_le (show k ≤ 29 by omega)
    exact hk D hD

/-- `k(6,3) ≤ 32`. Depends on the two `native_decide` runs of Lemma 8. -/
theorem k63_le : k3 6 ≤ 32 :=
  Nat.sInf_le (fun D => upper_bound (by simp) D)

/-- **Theorem 1 of the paper**: `30 ≤ k(6,3) ≤ 32`. -/
theorem k63_bounds : 30 ≤ k3 6 ∧ k3 6 ≤ 32 := ⟨k63_ge, k63_le⟩

end Erdos112
