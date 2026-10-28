import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6472 = true := by
  decide +kernel

theorem tot6472 : totK PD2M8K2 D2M8K2.t6472 = [100567748630, 429491972549, 354014062689, 39611303823, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6473 = true := by
  decide +kernel

theorem tot6473 : totK PD2M8K2 D2M8K2.t6473 = [0, 174103483054, 443475535914, 258508431692, 25373788367, 0, 0, 0] := by
  decide +kernel

theorem rows6474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6474 = true := by
  decide +kernel

theorem tot6474 : totK PD2M8K2 D2M8K2.t6474 = [0, 172413980522, 496542743348, 226476373972, 6616643500, 0, 0, 0] := by
  decide +kernel

theorem rows6475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6475 = true := by
  decide +kernel

theorem tot6475 : totK PD2M8K2 D2M8K2.t6475 = [174361741026, 413075507315, 258067187055, 66439020066, 5618966238, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
