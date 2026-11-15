module

public import Erdos112.KSound

@[expose] public section

/-!
# Lemma 8 of the paper: `{I_4, L_3}`-free oriented graphs on 14 vertices are 6-regular

The paper's proof renames the vertices so that a vertex `u` of degree 5 is `0`, its
neighbours are `1, ..., 5`, and its eight non-neighbours induce Bermond's graph `B_8` on
`6, ..., 13`; this uses the uniqueness of `B_8` (Lemma 3.1 of Ihringer, Rajendraprasad and
Weinert), which the paper cites.

Here the uniqueness of `B_8` is not used. Inside the eight non-neighbours of `u` we only
name one vertex `w` (vertex 6), its two out-neighbours (7, 8), its two in-neighbours (9, 10)
and its three non-neighbours (11, 12, 13); these numbers 2, 2, 3 are forced
(`OGraph.type8`). All other pairs inside `{7, ..., 13}` are left to the search. So the Lean
search covers the paper's search (which fixes all of `B_8`) and re-derives what it needs
about graphs on 8 vertices.
-/

namespace Erdos112

open scoped Classical
open Search

namespace OGraph

/-- In an `{I_3, L_3}`-free oriented graph on 8 vertices every vertex has type (2,2) and
three non-neighbours. -/
theorem type8 {V : Type} (D : OGraph V) (hTT : ¬ D.HasTT) {S : Finset V}
    (hS : D.NoIndep S 3) (hc : S.card = 8) (v : V) (hv : v ∈ S) :
    (D.outN S v).card = 2 ∧ (D.inN S v).card = 2 ∧ (D.nonN S v).card = 3 := by
  have h1 := D.card_split hv
  have h2 := D.card_outN_lt hTT hS v
  have h3 := D.card_inN_lt hTT hS v
  have h4 := bound_2_4 V D hTT _ (D.noIndep_nonN hv hS)
  omega

/-- The oriented graph on `Fin 14` obtained by naming 14 vertices of `D`. -/
def pull {V : Type} (D : OGraph V) (f : Fin 14 → V) : OGraph (Fin 14) where
  arc i j := D.arc (f i) (f j)
  asymm _ _ h := D.asymm _ _ h

theorem nn {V : Type} {D : OGraph V} {a b : V} (h : ¬ D.adj a b) :
    ¬ D.arc a b ∧ ¬ D.arc b a := ⟨fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩

end OGraph

/-- The naming of 14 vertices. -/
def relabel {V : Type} (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : V) (i : Fin 14) : V :=
  match i.val with
  | 0 => v0 | 1 => v1 | 2 => v2 | 3 => v3 | 4 => v4 | 5 => v5 | 6 => v6 | 7 => v7
  | 8 => v8 | 9 => v9 | 10 => v10 | 11 => v11 | 12 => v12 | _ => v13

/-- If the 14 vertices of `S` are named by `f` (every vertex of `S` gets a name), and no
`{I_4, L_3}`-free oriented graph on `Fin 14` agrees with the list `fixed`, while the named
graph does agree with it, we have a contradiction. -/
theorem relabel_core {V : Type} (D : OGraph V) (hTT : ¬ D.HasTT) (S : Finset V)
    (hS : D.NoIndep S 4) (hc : S.card = 14) (f : Fin 14 → V)
    (hsurj : ∀ z ∈ S, ∃ i, f i = z) (fixed : List (Fin 14 × Fin 14 × PS))
    (hfix : ∀ e ∈ fixed, Agree (D.pull f) e.1 e.2.1 e.2.2)
    (hno : ∀ D' : OGraph (Fin 14), ¬ D'.HasTT →
      (∀ T : Finset (Fin 14), D'.IsIndep T → T.card ≠ 4) →
      (∀ e ∈ fixed, Agree D' e.1 e.2.1 e.2.2) → False) : False := by
  have hsub : S ⊆ Finset.univ.image f := fun z hz => by
    obtain ⟨i, hi⟩ := hsurj z hz
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hle : (Finset.univ.image f).card ≤ 14 := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 14))) (f := f)
  have himg : S = Finset.univ.image f := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hinj : Function.Injective f := by
    have h1 : (Finset.univ.image f).card = (Finset.univ : Finset (Fin 14)).card := by
      rw [← himg, hc]; simp
    have h2 := Finset.card_image_iff.1 h1
    exact fun a b hab => h2 (by simp) (by simp) hab
  apply hno (D.pull f)
  · rintro ⟨x, y, z, h1, h2, h3⟩
    exact hTT ⟨f x, f y, f z, h1, h2, h3⟩
  · intro T hT hT4
    have hI : D.IsIndep (T.image f) := by
      intro p hp q hq hpq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hq
      exact hT i hi j hj hpq
    have h4 := hS (T.image f)
      (by rw [himg]; exact Finset.image_subset_image (Finset.subset_univ T)) hI
    rw [Finset.card_image_of_injective T hinj, hT4] at h4
    omega
  · exact hfix

/-- Lemma 8, the case of a vertex `u` of type (3,2). -/
theorem lemmaB32 {V : Type} (D : OGraph V) (hTT : ¬ D.HasTT) (S : Finset V)
    (hS : D.NoIndep S 4) (hc : S.card = 14) (u : V) (hu : u ∈ S)
    (ho : (D.outN S u).card = 3) (hi : (D.inN S u).card = 2) : False := by
  have hJ8 : (D.nonN S u).card = 8 := by have := D.card_split hu; omega
  have hJ3 : D.NoIndep (D.nonN S u) 3 := D.noIndep_nonN hu hS
  obtain ⟨w, hw⟩ : (D.nonN S u).Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨hwo, hwi, hwn⟩ := D.type8 hTT hJ3 hJ8 w hw
  obtain ⟨p1, p2, p3, -, -, -, hP⟩ := Finset.card_eq_three.1 ho
  obtain ⟨q1, q2, -, hQ⟩ := Finset.card_eq_two.1 hi
  obtain ⟨x1, x2, -, hX⟩ := Finset.card_eq_two.1 hwo
  obtain ⟨y1, y2, -, hY⟩ := Finset.card_eq_two.1 hwi
  obtain ⟨t1, t2, t3, -, -, -, hT⟩ := Finset.card_eq_three.1 hwn
  have mp1 : p1 ∈ D.outN S u := by rw [hP]; simp
  have mp2 : p2 ∈ D.outN S u := by rw [hP]; simp
  have mp3 : p3 ∈ D.outN S u := by rw [hP]; simp
  have mq1 : q1 ∈ D.inN S u := by rw [hQ]; simp
  have mq2 : q2 ∈ D.inN S u := by rw [hQ]; simp
  have mx1 : x1 ∈ D.outN (D.nonN S u) w := by rw [hX]; simp
  have mx2 : x2 ∈ D.outN (D.nonN S u) w := by rw [hX]; simp
  have my1 : y1 ∈ D.inN (D.nonN S u) w := by rw [hY]; simp
  have my2 : y2 ∈ D.inN (D.nonN S u) w := by rw [hY]; simp
  have mt1 : t1 ∈ D.nonN (D.nonN S u) w := by rw [hT]; simp
  have mt2 : t2 ∈ D.nonN (D.nonN S u) w := by rw [hT]; simp
  have mt3 : t3 ∈ D.nonN (D.nonN S u) w := by rw [hT]; simp
  have jx1 : x1 ∈ D.nonN S u := (OGraph.mem_outN.1 mx1).1
  have jx2 : x2 ∈ D.nonN S u := (OGraph.mem_outN.1 mx2).1
  have jy1 : y1 ∈ D.nonN S u := (OGraph.mem_inN.1 my1).1
  have jy2 : y2 ∈ D.nonN S u := (OGraph.mem_inN.1 my2).1
  have jt1 : t1 ∈ D.nonN S u := (OGraph.mem_nonN.1 mt1).1
  have jt2 : t2 ∈ D.nonN S u := (OGraph.mem_nonN.1 mt2).1
  have jt3 : t3 ∈ D.nonN S u := (OGraph.mem_nonN.1 mt3).1
  have hPi := D.indep_outN hTT S u
  have hQi := D.indep_inN hTT S u
  have hXi := D.indep_outN hTT (D.nonN S u) w
  have hYi := D.indep_inN hTT (D.nonN S u) w
  refine relabel_core D hTT S hS hc (relabel u p1 p2 p3 q1 q2 w x1 x2 y1 y2 t1 t2 t3) ?_ fixed32 ?_ no_graph32
  · intro z hz
    by_cases hzu : z = u
    · exact ⟨0, by rw [hzu]; rfl⟩
    by_cases h1 : D.arc u z
    · have hm : z ∈ D.outN S u := OGraph.mem_outN.2 ⟨hz, h1⟩
      rw [hP] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h
      · exact ⟨1, by rw [h]; rfl⟩
      · exact ⟨2, by rw [h]; rfl⟩
      · exact ⟨3, by rw [h]; rfl⟩
    by_cases h2 : D.arc z u
    · have hm : z ∈ D.inN S u := OGraph.mem_inN.2 ⟨hz, h2⟩
      rw [hQ] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h
      · exact ⟨4, by rw [h]; rfl⟩
      · exact ⟨5, by rw [h]; rfl⟩
    have hzJ : z ∈ D.nonN S u := OGraph.mem_nonN.2 ⟨hz, hzu, fun h => h.elim h1 h2⟩
    by_cases hzw : z = w
    · exact ⟨6, by rw [hzw]; rfl⟩
    by_cases h3 : D.arc w z
    · have hm : z ∈ D.outN (D.nonN S u) w := OGraph.mem_outN.2 ⟨hzJ, h3⟩
      rw [hX] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h
      · exact ⟨7, by rw [h]; rfl⟩
      · exact ⟨8, by rw [h]; rfl⟩
    by_cases h4 : D.arc z w
    · have hm : z ∈ D.inN (D.nonN S u) w := OGraph.mem_inN.2 ⟨hzJ, h4⟩
      rw [hY] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h
      · exact ⟨9, by rw [h]; rfl⟩
      · exact ⟨10, by rw [h]; rfl⟩
    have hm : z ∈ D.nonN (D.nonN S u) w := OGraph.mem_nonN.2 ⟨hzJ, hzw, fun h => h.elim h3 h4⟩
    rw [hT] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h
    · exact ⟨11, by rw [h]; rfl⟩
    · exact ⟨12, by rw [h]; rfl⟩
    · exact ⟨13, by rw [h]; rfl⟩
  · intro e he
    simp only [fixed32, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (OGraph.mem_outN.1 mp1).2
    · exact (OGraph.mem_outN.1 mp2).2
    · exact (OGraph.mem_outN.1 mp3).2
    · exact (OGraph.mem_inN.1 mq1).2
    · exact (OGraph.mem_inN.1 mq2).2
    · exact OGraph.nn (OGraph.mem_nonN.1 hw).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jx1).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jx2).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jy1).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jy2).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jt1).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jt2).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jt3).2.2
    · exact ⟨hPi p1 mp1 p2 mp2, hPi p2 mp2 p1 mp1⟩
    · exact ⟨hPi p1 mp1 p3 mp3, hPi p3 mp3 p1 mp1⟩
    · exact ⟨hPi p2 mp2 p3 mp3, hPi p3 mp3 p2 mp2⟩
    · exact ⟨hQi q1 mq1 q2 mq2, hQi q2 mq2 q1 mq1⟩
    · exact (OGraph.mem_outN.1 mx1).2
    · exact (OGraph.mem_outN.1 mx2).2
    · exact (OGraph.mem_inN.1 my1).2
    · exact (OGraph.mem_inN.1 my2).2
    · exact OGraph.nn (OGraph.mem_nonN.1 mt1).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 mt2).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 mt3).2.2
    · exact ⟨hXi x1 mx1 x2 mx2, hXi x2 mx2 x1 mx1⟩
    · exact ⟨hYi y1 my1 y2 my2, hYi y2 my2 y1 my1⟩

/-- Lemma 8, the case of a vertex `u` of type (2,3). -/
theorem lemmaB23 {V : Type} (D : OGraph V) (hTT : ¬ D.HasTT) (S : Finset V)
    (hS : D.NoIndep S 4) (hc : S.card = 14) (u : V) (hu : u ∈ S)
    (ho : (D.outN S u).card = 2) (hi : (D.inN S u).card = 3) : False := by
  have hJ8 : (D.nonN S u).card = 8 := by have := D.card_split hu; omega
  have hJ3 : D.NoIndep (D.nonN S u) 3 := D.noIndep_nonN hu hS
  obtain ⟨w, hw⟩ : (D.nonN S u).Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨hwo, hwi, hwn⟩ := D.type8 hTT hJ3 hJ8 w hw
  obtain ⟨p1, p2, -, hP⟩ := Finset.card_eq_two.1 ho
  obtain ⟨q1, q2, q3, -, -, -, hQ⟩ := Finset.card_eq_three.1 hi
  obtain ⟨x1, x2, -, hX⟩ := Finset.card_eq_two.1 hwo
  obtain ⟨y1, y2, -, hY⟩ := Finset.card_eq_two.1 hwi
  obtain ⟨t1, t2, t3, -, -, -, hT⟩ := Finset.card_eq_three.1 hwn
  have mp1 : p1 ∈ D.outN S u := by rw [hP]; simp
  have mp2 : p2 ∈ D.outN S u := by rw [hP]; simp
  have mq1 : q1 ∈ D.inN S u := by rw [hQ]; simp
  have mq2 : q2 ∈ D.inN S u := by rw [hQ]; simp
  have mq3 : q3 ∈ D.inN S u := by rw [hQ]; simp
  have mx1 : x1 ∈ D.outN (D.nonN S u) w := by rw [hX]; simp
  have mx2 : x2 ∈ D.outN (D.nonN S u) w := by rw [hX]; simp
  have my1 : y1 ∈ D.inN (D.nonN S u) w := by rw [hY]; simp
  have my2 : y2 ∈ D.inN (D.nonN S u) w := by rw [hY]; simp
  have mt1 : t1 ∈ D.nonN (D.nonN S u) w := by rw [hT]; simp
  have mt2 : t2 ∈ D.nonN (D.nonN S u) w := by rw [hT]; simp
  have mt3 : t3 ∈ D.nonN (D.nonN S u) w := by rw [hT]; simp
  have jx1 : x1 ∈ D.nonN S u := (OGraph.mem_outN.1 mx1).1
  have jx2 : x2 ∈ D.nonN S u := (OGraph.mem_outN.1 mx2).1
  have jy1 : y1 ∈ D.nonN S u := (OGraph.mem_inN.1 my1).1
  have jy2 : y2 ∈ D.nonN S u := (OGraph.mem_inN.1 my2).1
  have jt1 : t1 ∈ D.nonN S u := (OGraph.mem_nonN.1 mt1).1
  have jt2 : t2 ∈ D.nonN S u := (OGraph.mem_nonN.1 mt2).1
  have jt3 : t3 ∈ D.nonN S u := (OGraph.mem_nonN.1 mt3).1
  have hPi := D.indep_outN hTT S u
  have hQi := D.indep_inN hTT S u
  have hXi := D.indep_outN hTT (D.nonN S u) w
  have hYi := D.indep_inN hTT (D.nonN S u) w
  refine relabel_core D hTT S hS hc (relabel u p1 p2 q1 q2 q3 w x1 x2 y1 y2 t1 t2 t3) ?_ fixed23 ?_ no_graph23
  · intro z hz
    by_cases hzu : z = u
    · exact ⟨0, by rw [hzu]; rfl⟩
    by_cases h1 : D.arc u z
    · have hm : z ∈ D.outN S u := OGraph.mem_outN.2 ⟨hz, h1⟩
      rw [hP] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h
      · exact ⟨1, by rw [h]; rfl⟩
      · exact ⟨2, by rw [h]; rfl⟩
    by_cases h2 : D.arc z u
    · have hm : z ∈ D.inN S u := OGraph.mem_inN.2 ⟨hz, h2⟩
      rw [hQ] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h
      · exact ⟨3, by rw [h]; rfl⟩
      · exact ⟨4, by rw [h]; rfl⟩
      · exact ⟨5, by rw [h]; rfl⟩
    have hzJ : z ∈ D.nonN S u := OGraph.mem_nonN.2 ⟨hz, hzu, fun h => h.elim h1 h2⟩
    by_cases hzw : z = w
    · exact ⟨6, by rw [hzw]; rfl⟩
    by_cases h3 : D.arc w z
    · have hm : z ∈ D.outN (D.nonN S u) w := OGraph.mem_outN.2 ⟨hzJ, h3⟩
      rw [hX] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h
      · exact ⟨7, by rw [h]; rfl⟩
      · exact ⟨8, by rw [h]; rfl⟩
    by_cases h4 : D.arc z w
    · have hm : z ∈ D.inN (D.nonN S u) w := OGraph.mem_inN.2 ⟨hzJ, h4⟩
      rw [hY] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h
      · exact ⟨9, by rw [h]; rfl⟩
      · exact ⟨10, by rw [h]; rfl⟩
    have hm : z ∈ D.nonN (D.nonN S u) w := OGraph.mem_nonN.2 ⟨hzJ, hzw, fun h => h.elim h3 h4⟩
    rw [hT] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h
    · exact ⟨11, by rw [h]; rfl⟩
    · exact ⟨12, by rw [h]; rfl⟩
    · exact ⟨13, by rw [h]; rfl⟩
  · intro e he
    simp only [fixed23, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (OGraph.mem_outN.1 mp1).2
    · exact (OGraph.mem_outN.1 mp2).2
    · exact (OGraph.mem_inN.1 mq1).2
    · exact (OGraph.mem_inN.1 mq2).2
    · exact (OGraph.mem_inN.1 mq3).2
    · exact OGraph.nn (OGraph.mem_nonN.1 hw).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jx1).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jx2).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jy1).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jy2).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jt1).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jt2).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 jt3).2.2
    · exact ⟨hPi p1 mp1 p2 mp2, hPi p2 mp2 p1 mp1⟩
    · exact ⟨hQi q1 mq1 q2 mq2, hQi q2 mq2 q1 mq1⟩
    · exact ⟨hQi q1 mq1 q3 mq3, hQi q3 mq3 q1 mq1⟩
    · exact ⟨hQi q2 mq2 q3 mq3, hQi q3 mq3 q2 mq2⟩
    · exact (OGraph.mem_outN.1 mx1).2
    · exact (OGraph.mem_outN.1 mx2).2
    · exact (OGraph.mem_inN.1 my1).2
    · exact (OGraph.mem_inN.1 my2).2
    · exact OGraph.nn (OGraph.mem_nonN.1 mt1).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 mt2).2.2
    · exact OGraph.nn (OGraph.mem_nonN.1 mt3).2.2
    · exact ⟨hXi x1 mx1 x2 mx2, hXi x2 mx2 x1 mx1⟩
    · exact ⟨hYi y1 my1 y2 my2, hYi y2 my2 y1 my1⟩

/-- **Lemma 8 of the paper.** Every vertex of an `{I_4, L_3}`-free oriented graph on 14
vertices has degree 6. (Uses the kernel-checked search through `no_graph32`, `no_graph23` of
`KSound.lean`; no `native_decide`.) -/
theorem lemmaB {V : Type} (D : OGraph V) (hTT : ¬ D.HasTT) {S : Finset V}
    (hS : D.NoIndep S 4) (hc : S.card = 14) (v : V) (hv : v ∈ S) : D.deg S v = 6 := by
  have h1 := D.card_split hv
  have h2 := D.card_outN_lt hTT hS v
  have h3 := D.card_inN_lt hTT hS v
  have h4 := bound_3_9 V D hTT _ (D.noIndep_nonN hv hS)
  rw [D.deg_eq]
  by_contra hne
  have h5 : ((D.outN S v).card = 3 ∧ (D.inN S v).card = 2)
      ∨ ((D.outN S v).card = 2 ∧ (D.inN S v).card = 3) := by omega
  rcases h5 with ⟨ho, hi⟩ | ⟨ho, hi⟩
  · exact lemmaB32 D hTT S hS hc v hv ho hi
  · exact lemmaB23 D hTT S hS hc v hv ho hi

end Erdos112
