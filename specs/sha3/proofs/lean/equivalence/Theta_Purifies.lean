import equivalence.Spec_Pure

open hacspec_sha3.keccak_f Spec.Pure

set_option maxHeartbeats 6400000 in
theorem Spec.Pure.theta_purifies_proof (st : RustArray u64 25) :
    theta st = .ok ⟨theta_pure st.toVec⟩ := by
  unfold theta theta_pure
  rw [Spec.Pure.theta_c_purifies st]
  simp only [bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, Option.bind, RustM.ok]
  rw [Spec.Pure.theta_d_purifies st _ rfl]
  simp only [bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, Option.bind, RustM.ok]
  rw [Spec.Pure.theta_apply_purifies st _ _ rfl]
