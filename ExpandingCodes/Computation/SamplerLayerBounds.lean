import ExpandingCodes.Computation.SamplerTables
import ExpandingCodes.Computation.EncodedSampler

set_option autoImplicit false

namespace ExpandingCodes.Computation.SamplerLayerBounds
open ExpandingCodes.PolynomialStretch
variable {q d k b : ℕ}

theorem table_end {K : ℕ} (width : ℕ) (i : Fin K) :
    1+(i.val+1)*width ≤ 1+K*width :=
  Nat.add_le_add_left (Nat.mul_le_mul_right width i.isLt) 1

theorem form_middle_lt (r : Fin 2) (i : Fin k) (a : Fin q) :
    a.val+(i.val+k*r.val)*q < 2*k*q := by
  have h := (finProdFinEquiv (finProdFinEquiv (r,i),a)).isLt
  simpa [finProdFinEquiv,Nat.mul_comm] using h

theorem form_index_val (r : Fin 2) (i : Fin k) (a : Fin q) (j : Fin d) :
    (SamplerTables.flatFour 2 k q d (((r,i),a),j)).val =
      j.val+d*(a.val+q*(i.val+k*r.val)) := SamplerTables.flatFour_val _ _ _ _

theorem form_index_lt (r : Fin 2) (i : Fin k) (a : Fin q) (j : Fin d) :
    j.val+d*(a.val+q*(i.val+k*r.val)) < 2*k*q*d := by
  rw [← form_index_val]
  exact (SamplerTables.flatFour 2 k q d (((r,i),a),j)).isLt

theorem form_end (r : Fin 2) (i : Fin k) (a : Fin q) (j : Fin d) :
    1+(j.val+d*(a.val+q*(i.val+k*r.val))+1)*q ≤ 1+(2*k*q*d)*q := by
  simpa only [form_index_val] using table_end q (SamplerTables.flatFour 2 k q d (((r,i),a),j))

theorem hash_index_val (i : Fin k) (a u v : Fin q) :
    (SamplerTables.flatFour k q q q (((i,a),u),v)).val =
      v.val+q*(u.val+q*(a.val+q*i.val)) := SamplerTables.flatFour_val _ _ _ _

theorem hash_index_lt (i : Fin k) (a u v : Fin q) :
    v.val+q*(u.val+q*(a.val+q*i.val)) < k*q*q*q := by
  rw [← hash_index_val]
  exact (SamplerTables.flatFour k q q q (((i,a),u),v)).isLt

theorem hash_end (i : Fin k) (a u v : Fin q) :
    1+(v.val+q*(u.val+q*(a.val+q*i.val))+1)*b ≤ 1+(k*q*q*q)*b := by
  simpa only [hash_index_val] using table_end b (SamplerTables.flatFour k q q q (((i,a),u),v))

theorem column_lt (i : Fin k) (u : Fin b) : i.val*b+u.val < k*b := by
  have h := (finProdFinEquiv (i,u)).isLt
  simpa [finProdFinEquiv,Nat.mul_comm,Nat.add_comm] using h

theorem neighbor_cached (O : EncodedGaussian.Operations (Fin q))
    (forms : Fin (2*k*q*d) → Fin q) (hashes : Fin (k*q*q*q) → Fin b)
    (hk : k ≤ q) (i : Fin k) (z : Fin d → Fin q) :
    let alpha : Fin q := ⟨i.val,lt_of_lt_of_le i.isLt hk⟩
    let a := (EncodedSampler.fixed O alpha z).1
    let u := (EncodedSampler.linear O
      (fun j => forms (SamplerTables.flatFour 2 k q d (((0,i),a),j))) z).1
    let v := (EncodedSampler.linear O
      (fun j => forms (SamplerTables.flatFour 2 k q d (((1,i),a),j))) z).1
    EncodedSampler.neighbor O forms hashes i z =
      hashes (SamplerTables.flatFour k q q q (((i,a),u),v)) := by
  simp only [EncodedSampler.neighbor,EncodedSampler.address,dif_pos (lt_of_lt_of_le i.isLt hk)]

#print axioms neighbor_cached
#print axioms form_end
#print axioms hash_end
#print axioms column_lt
end ExpandingCodes.Computation.SamplerLayerBounds
