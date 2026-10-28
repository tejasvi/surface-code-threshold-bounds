import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12596 = true := by
  decide +kernel

theorem tot12596 : totK PD2M8K2 D2M8K2.t12596 = [0, 0, 178976943830, 464306619108, 243466211903, 13908012088, 0, 0] := by
  decide +kernel

theorem rows12597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12597 = true := by
  decide +kernel

theorem tot12597 : totK PD2M8K2 D2M8K2.t12597 = [0, 0, 189512530825, 473755702694, 207419665292, 7902352020, 0, 0] := by
  decide +kernel

theorem rows12598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12598 = true := by
  decide +kernel

theorem tot12598 : totK PD2M8K2 D2M8K2.t12598 = [0, 0, 169668735041, 451318918643, 248862362374, 22828318141, 0, 0] := by
  decide +kernel

theorem rows12599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12599 = true := by
  decide +kernel

theorem tot12599 : totK PD2M8K2 D2M8K2.t12599 = [0, 0, 140384024491, 450623664252, 273492787638, 21551127925, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
