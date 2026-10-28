import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11360 = true := by
  decide +kernel

theorem tot11360 : totK PD2M8K2 D2M8K2.t11360 = [89923614195, 392974647572, 360489188508, 75553645600, 10443484490, 0, 0, 0] := by
  decide +kernel

theorem rows11361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11361 = true := by
  decide +kernel

theorem tot11361 : totK PD2M8K2 D2M8K2.t11361 = [0, 173279500951, 461307619920, 242846295920, 14916446703, 0, 0, 0] := by
  decide +kernel

theorem rows11362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11362 = true := by
  decide +kernel

theorem tot11362 : totK PD2M8K2 D2M8K2.t11362 = [17582599337, 169650784792, 455277999496, 245819580168, 12229515597, 0, 0, 0] := by
  decide +kernel

theorem rows11363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11363 = true := by
  decide +kernel

theorem tot11363 : totK PD2M8K2 D2M8K2.t11363 = [193704007209, 459664745428, 243819569218, 23219762177, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
