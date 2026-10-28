import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8120 = true := by
  decide +kernel

theorem tot8120 : totK PD2M8K2 D2M8K2.t8120 = [0, 157883578780, 446261638574, 291941732742, 30455970377, 0, 0, 0] := by
  decide +kernel

theorem rows8121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8121 = true := by
  decide +kernel

theorem tot8121 : totK PD2M8K2 D2M8K2.t8121 = [0, 168533124761, 469976446282, 250696163876, 14030300615, 0, 0, 0] := by
  decide +kernel

theorem rows8122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8122 = true := by
  decide +kernel

theorem tot8122 : totK PD2M8K2 D2M8K2.t8122 = [0, 0, 200705699109, 459554246549, 233409791291, 22924788730, 0, 0] := by
  decide +kernel

theorem rows8123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8123 = true := by
  decide +kernel

theorem tot8123 : totK PD2M8K2 D2M8K2.t8123 = [0, 0, 200202120762, 479948561945, 212004470521, 6288651884, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
