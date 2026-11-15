import Erdos112.Basic
import Erdos112Search

/-!
# Soundness of the pair-by-pair search of Lemma 8

`search_sound`: if an oriented graph `D` on `Fin 14` has no transitive triangle and no
independent set of 4 vertices, and agrees with the table `a` on every decided pair, then
`search ps a = false` for every list of pairs `ps`. So `search ps a = true` proves that no
such graph agrees with `a`. The proof is checked by the Lean kernel.

In this folder (`lean_kernel`) the two runs of this search are no longer part of the proof:
they took about 27 seconds of native code and needed `native_decide`. Lemma 8 is proved
instead by the smaller search of `KSearch.lean`, which the kernel evaluates (`KSound.lean`).
This file is kept for `Agree` (used by `KSound.lean` and `LemmaB.lean`) and as the
kernel-checked soundness proof of the paper's search, which the stand-alone program `lemmab`
still runs as a cross-check.
-/

namespace Erdos112.Search

open Erdos112

/-- What a pair state says about the graph `D`. -/
def Agree (D : OGraph (Fin 14)) (i j : Fin 14) : PS → Prop
  | .undec => True
  | .non => ¬ D.arc i j ∧ ¬ D.arc j i
  | .fwd => D.arc i j
  | .bwd => D.arc j i

/-- `D` agrees with the table `a` on every decided pair. -/
structure Ext (D : OGraph (Fin 14)) (a : Tab) : Prop where
  agree : ∀ i j : Fin 14, Agree D i j (get a i j)

theorem agree_flip {D : OGraph (Fin 14)} {i j : Fin 14} {s : PS} (h : Agree D i j s) :
    Agree D j i s.flip := by
  cases s
  · exact h
  · exact ⟨h.2, h.1⟩
  · exact h
  · exact h

theorem getD_set (a : Tab) (k m : Nat) (v : PS) :
    (a.setIfInBounds k v).getD m .undec = a.getD m .undec
      ∨ (k = m ∧ (a.setIfInBounds k v).getD m .undec = v) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : k = m
  · subst h
    by_cases h2 : k < a.size
    · right; simp [h2]
    · left
      have := Array.getElem?_eq_none (xs := a) (i := k) (by omega)
      simp [h2]
  · left; simp [h]

theorem get_set (a : Tab) (x y i j : Fin 14) (s : PS) :
    get (set a x y s) i j = get a i j
      ∨ (i = x ∧ j = y ∧ get (set a x y s) i j = s)
      ∨ (i = y ∧ j = x ∧ get (set a x y s) i j = s.flip) := by
  have hi := i.isLt
  have hj := j.isLt
  have hx := x.isLt
  have hy := y.isLt
  unfold get set
  rcases getD_set (a.setIfInBounds (idx x y) s) (idx y x) (idx i j) s.flip with h | ⟨hk, h⟩
  · rw [h]
    rcases getD_set a (idx x y) (idx i j) s with h' | ⟨hk', h'⟩
    · left; exact h'
    · right; left
      unfold idx at hk'
      exact ⟨Fin.ext (by omega), Fin.ext (by omega), h'⟩
  · right; right
    unfold idx at hk
    exact ⟨Fin.ext (by omega), Fin.ext (by omega), h⟩

theorem ext_set {D : OGraph (Fin 14)} {a : Tab} (h : Ext D a) {x y : Fin 14} {s : PS}
    (hs : Agree D x y s) : Ext D (set a x y s) := by
  refine ⟨fun i j => ?_⟩
  rcases get_set a x y i j s with h1 | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [h1]; exact h.agree i j
  · rw [h3, h1, h2]; exact hs
  · rw [h3, h1, h2]; exact agree_flip hs

theorem ttBad_sound {D : OGraph (Fin 14)} {a : Tab} (h : Ext D a) {u v : Fin 14}
    (huv : D.arc u v) (hb : ttBad a u v = true) : D.HasTT := by
  unfold ttBad at hb
  rw [List.any_eq_true] at hb
  obtain ⟨z, _, hz⟩ := hb
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hz
  have h1 := h.agree u z
  have h2 := h.agree v z
  rcases hz with (⟨a1, a2⟩ | ⟨a1, a2⟩) | ⟨a1, a2⟩ <;> rw [a1] at h1 <;> rw [a2] at h2
  · exact ⟨u, v, z, huv, h2, h1⟩
  · exact ⟨z, u, v, h1, huv, h2⟩
  · exact ⟨u, z, v, h1, h2, huv⟩

theorem indepBad_sound {D : OGraph (Fin 14)} {a : Tab} (h : Ext D a) {x y : Fin 14}
    (hb : indepBad a x y = true) : ∃ T : Finset (Fin 14), D.IsIndep T ∧ T.card = 4 := by
  unfold indepBad at hb
  simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq,
    ne_eq] at hb
  obtain ⟨⟨hxy, nxy⟩, z, _, ⟨⟨⟨hzx, hzy⟩, nxz⟩, nyz⟩, w, _,
    ⟨⟨⟨⟨hzw, hwx⟩, hwy⟩, nxw⟩, nyw⟩, nzw⟩ := hb
  have a1 := h.agree x y; rw [nxy] at a1
  have a2 := h.agree x z; rw [nxz] at a2
  have a3 := h.agree y z; rw [nyz] at a3
  have a4 := h.agree x w; rw [nxw] at a4
  have a5 := h.agree y w; rw [nyw] at a5
  have a6 := h.agree z w; rw [nzw] at a6
  refine ⟨{x, y, z, w}, ?_, ?_⟩
  · intro p hp q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      first
        | exact D.arc_irrefl _ | exact a1.1 | exact a1.2 | exact a2.1 | exact a2.2
        | exact a3.1 | exact a3.2 | exact a4.1 | exact a4.2 | exact a5.1 | exact a5.2
        | exact a6.1 | exact a6.2
  · have hzw' : z ≠ w := ne_of_lt hzw
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hzw'
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => hzy e.symm, fun e => hwy e.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, fun e => hzx e.symm, fun e => hwx e.symm⟩

/-- Soundness of the search. -/
theorem search_sound (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT)
    (hI : ∀ T : Finset (Fin 14), D.IsIndep T → T.card ≠ 4) :
    ∀ (ps : List (Fin 14 × Fin 14)) (a : Tab), Ext D a → search ps a = false := by
  intro ps
  induction ps with
  | nil => intro a _; rfl
  | cons p ps ih =>
    intro a ha
    obtain ⟨x, y⟩ := p
    unfold search
    by_cases h1 : D.arc x y
    · have he : Ext D (set a x y .fwd) := ext_set ha (s := .fwd) h1
      have hb : ttBad (set a x y .fwd) x y = false := by
        by_contra hc
        exact hTT (ttBad_sound he h1 (by simpa using hc))
      simp [hb, ih _ he]
    · by_cases h2 : D.arc y x
      · have he : Ext D (set a x y .bwd) := ext_set ha (s := .bwd) h2
        have hb : ttBad (set a x y .bwd) y x = false := by
          by_contra hc
          exact hTT (ttBad_sound he h2 (by simpa using hc))
        simp [hb, ih _ he]
      · have he : Ext D (set a x y .non) := ext_set ha (s := .non) ⟨h1, h2⟩
        have hb : indepBad (set a x y .non) x y = false := by
          by_contra hc
          obtain ⟨T, hT, hT4⟩ := indepBad_sound he (by simpa using hc)
          exact hI T hT hT4
        simp [hb, ih _ he]

theorem ext_empty (D : OGraph (Fin 14)) : Ext D (Array.replicate 196 PS.undec) := by
  refine ⟨fun i j => ?_⟩
  have : get (Array.replicate 196 PS.undec) i j = .undec := by
    unfold get
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  rw [this]; trivial

theorem ext_init (D : OGraph (Fin 14)) (l : List (Fin 14 × Fin 14 × PS))
    (h : ∀ e ∈ l, Agree D e.1 e.2.1 e.2.2) : Ext D (init l) := by
  unfold init
  have gen : ∀ (l : List (Fin 14 × Fin 14 × PS)) (a : Tab), Ext D a →
      (∀ e ∈ l, Agree D e.1 e.2.1 e.2.2) →
      Ext D (l.foldl (fun a e => set a e.1 e.2.1 e.2.2) a) := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons e l ih =>
      intro a ha hl
      rw [List.foldl_cons]
      exact ih _ (ext_set ha (hl e (List.mem_cons_self))) (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
  have h0 := ext_empty D
  exact gen l (Array.replicate 196 PS.undec) h0 h

end Erdos112.Search
