import Mathlib

#check Fintype.sum_equiv
#check Equiv.sum_comp
#check Finset.sum_bij
#check Finset.sum_comm
#check Finset.sum_product
#check Fintype.sum_prod_type

private theorem sum_swap_first_fourth
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, f d b c a := by
  let swap : (Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (Fin 4 × Fin 4 × Fin 4 × Fin 4) :=
    { toFun := fun (a, b, c, d) => (d, b, c, a)
      invFun := fun (a, b, c, d) => (d, b, c, a)
      left_inv := by rintro ⟨a, b, c, d⟩; rfl
      right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  let source : (Fin 4 × Fin 4 × Fin 4 × Fin 4) → Real :=
    fun (a, b, c, d) => f a b c d
  let target : (Fin 4 × Fin 4 × Fin 4 × Fin 4) → Real :=
    fun (a, b, c, d) => f d b c a
  have h := Fintype.sum_equiv swap source target (by
    rintro ⟨a, b, c, d⟩
    rfl)
  simpa only [source, target, Fintype.sum_prod_type] using h

private theorem sum_swap_second_fourth
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, f a d c b := by
  let swap : (Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃
      (Fin 4 × Fin 4 × Fin 4 × Fin 4) :=
    { toFun := fun (a, b, c, d) => (a, d, c, b)
      invFun := fun (a, b, c, d) => (a, d, c, b)
      left_inv := by rintro ⟨a, b, c, d⟩; rfl
      right_inv := by rintro ⟨a, b, c, d⟩; rfl }
  let source : (Fin 4 × Fin 4 × Fin 4 × Fin 4) → Real :=
    fun (a, b, c, d) => f a b c d
  let target : (Fin 4 × Fin 4 × Fin 4 × Fin 4) → Real :=
    fun (a, b, c, d) => f a d c b
  have h := Fintype.sum_equiv swap source target (by
    rintro ⟨a, b, c, d⟩
    rfl)
  simpa only [source, target, Fintype.sum_prod_type] using h

theorem scratch_gauss_weingarten_fin4_algebra
    (normal normalDerivative : Fin 4 → Real)
    (metric : Fin 4 → Fin 4 → Real)
    (outerTangent innerTangent spatialDerivative : Fin 4 → Real)
    (christoffel : Fin 4 → Fin 4 → Fin 4 → Real)
    (hMetricSymmetric : ∀ row column, metric row column = metric column row)
    (hZero :
      (∑ row : Fin 4, ∑ column : Fin 4,
        (normalDerivative row * metric row column * innerTangent column +
          normal row *
            (∑ regular : Fin 4, outerTangent regular *
              ((∑ upper : Fin 4,
                  christoffel upper regular row * metric upper column) +
                ∑ upper : Fin 4,
                  christoffel upper regular column * metric upper row)) *
              innerTangent column +
          normal row * metric row column * spatialDerivative column)) = 0) :
    -(∑ row : Fin 4, ∑ column : Fin 4,
        normal row * metric row column *
          (spatialDerivative column +
            ∑ regular : Fin 4, ∑ inner : Fin 4,
              christoffel column regular inner * outerTangent regular *
                innerTangent inner)) =
      (∑ row : Fin 4, ∑ column : Fin 4,
        normalDerivative row * metric row column * innerTangent column) +
      ∑ row : Fin 4, ∑ column : Fin 4,
        (∑ regular : Fin 4, ∑ upper : Fin 4,
          outerTangent regular * christoffel row regular upper *
            normal upper) * metric row column * innerTangent column := by
  have hFirst := sum_swap_first_fourth
    (fun row column regular upper =>
      normal row * outerTangent regular *
        christoffel upper regular row * metric upper column *
          innerTangent column)
  have hSecond := sum_swap_second_fourth
    (fun row column regular upper =>
      normal row * outerTangent regular *
        christoffel upper regular column * metric upper row *
          innerTangent column)
  have hSecondSymmetric :
      (∑ row, ∑ column, ∑ regular, ∑ upper,
        normal row * outerTangent regular *
          christoffel upper regular column * metric upper row *
            innerTangent column) =
        ∑ row, ∑ column, ∑ regular, ∑ upper,
          normal row * outerTangent regular *
            christoffel column regular upper * metric row column *
              innerTangent upper := by
    calc
      _ = ∑ row, ∑ column, ∑ regular, ∑ upper,
          normal row * outerTangent regular *
            christoffel column regular upper * metric column row *
              innerTangent upper := hSecond
      _ = _ := by
        apply Finset.sum_congr rfl
        intro row _
        apply Finset.sum_congr rfl
        intro column _
        apply Finset.sum_congr rfl
        intro regular _
        apply Finset.sum_congr rfl
        intro upper _
        rw [hMetricSymmetric]
  have hFirstPacked :
      (∑ row, ∑ column,
        (∑ regular, ∑ upper,
          normal row * outerTangent regular *
            christoffel upper regular row * metric upper column) *
              innerTangent column) =
        ∑ row, ∑ column,
          (∑ regular, ∑ upper,
            outerTangent regular * christoffel row regular upper *
              normal upper) * metric row column * innerTangent column := by
    calc
      _ = ∑ row, ∑ column, ∑ regular, ∑ upper,
          normal row * outerTangent regular *
            christoffel upper regular row * metric upper column *
              innerTangent column := by
        simp only [Finset.sum_mul]
      _ = ∑ row, ∑ column, ∑ regular, ∑ upper,
          normal upper * outerTangent regular *
            christoffel row regular upper * metric row column *
              innerTangent column := hFirst
      _ = _ := by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro row _
        apply Finset.sum_congr rfl
        intro column _
        apply Finset.sum_congr rfl
        intro regular _
        apply Finset.sum_congr rfl
        intro upper _
        ring
  have hSecondPacked :
      (∑ row, ∑ column,
        (∑ regular, ∑ upper,
          normal row * outerTangent regular *
            christoffel upper regular column * metric upper row) *
              innerTangent column) =
        ∑ row, ∑ column, ∑ regular, ∑ upper,
          normal row * metric row column *
            christoffel column regular upper * outerTangent regular *
              innerTangent upper := by
    calc
      _ = ∑ row, ∑ column, ∑ regular, ∑ upper,
          normal row * outerTangent regular *
            christoffel column regular upper * metric row column *
              innerTangent upper := by
        simpa only [Finset.sum_mul] using hSecondSymmetric
      _ = _ := by
        apply Finset.sum_congr rfl
        intro row _
        apply Finset.sum_congr rfl
        intro column _
        apply Finset.sum_congr rfl
        intro regular _
        apply Finset.sum_congr rfl
        intro upper _
        ring
  have hZeroExpanded :
      (∑ row, ∑ column,
        normalDerivative row * metric row column * innerTangent column) +
      (∑ row, ∑ column,
        (∑ regular, ∑ upper,
          normal row * outerTangent regular *
            christoffel upper regular row * metric upper column) *
              innerTangent column) +
      (∑ row, ∑ column,
        (∑ regular, ∑ upper,
          normal row * outerTangent regular *
            christoffel upper regular column * metric upper row) *
              innerTangent column) +
      (∑ row, ∑ column,
        normal row * metric row column * spatialDerivative column) = 0 := by
    calc
      _ = ∑ row, ∑ column,
          (normalDerivative row * metric row column * innerTangent column +
            (∑ regular, ∑ upper,
              normal row * outerTangent regular *
                christoffel upper regular row * metric upper column) *
                  innerTangent column +
            (∑ regular, ∑ upper,
              normal row * outerTangent regular *
                christoffel upper regular column * metric upper row) *
                  innerTangent column +
            normal row * metric row column * spatialDerivative column) := by
        simp only [Finset.sum_add_distrib]
      _ = ∑ row, ∑ column,
          (normalDerivative row * metric row column * innerTangent column +
            normal row *
              (∑ regular, outerTangent regular *
                ((∑ upper,
                    christoffel upper regular row * metric upper column) +
                  ∑ upper,
                    christoffel upper regular column * metric upper row)) *
                innerTangent column +
            normal row * metric row column * spatialDerivative column) := by
        apply Finset.sum_congr rfl
        intro row _
        apply Finset.sum_congr rfl
        intro column _
        have hMiddle :
            (∑ regular, ∑ upper,
              normal row * outerTangent regular *
                christoffel upper regular row * metric upper column) +
            (∑ regular, ∑ upper,
              normal row * outerTangent regular *
                christoffel upper regular column * metric upper row) =
              normal row *
                (∑ regular, outerTangent regular *
                  ((∑ upper,
                      christoffel upper regular row * metric upper column) +
                    ∑ upper,
                      christoffel upper regular column * metric upper row)) := by
          calc
            _ = ∑ regular,
                ((∑ upper,
                    normal row * outerTangent regular *
                      christoffel upper regular row * metric upper column) +
                  ∑ upper,
                    normal row * outerTangent regular *
                      christoffel upper regular column * metric upper row) := by
              rw [Finset.sum_add_distrib]
            _ = ∑ regular,
                (normal row * outerTangent regular *
                    (∑ upper,
                      christoffel upper regular row * metric upper column) +
                  normal row * outerTangent regular *
                    (∑ upper,
                      christoffel upper regular column * metric upper row)) := by
              apply Finset.sum_congr rfl
              intro regular _
              congr 1
              · rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro upper _
                ring
              · rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro upper _
                ring
            _ = ∑ regular, normal row *
                (outerTangent regular *
                  ((∑ upper,
                      christoffel upper regular row * metric upper column) +
                    ∑ upper,
                      christoffel upper regular column * metric upper row)) := by
              apply Finset.sum_congr rfl
              intro regular _
              ring
            _ = _ := by rw [Finset.mul_sum]
        rw [← hMiddle]
        ring
      _ = 0 := hZero
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum] at ⊢
  ring_nf at hZeroExpanded hFirstPacked hSecondPacked ⊢
  rw [hFirstPacked, hSecondPacked] at hZeroExpanded
  linear_combination -hZeroExpanded
