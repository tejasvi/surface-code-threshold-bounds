import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8496 = true := by
  decide +kernel

theorem tot8496 : totK PD2M8K2 D2M8K2.t8496 = [171140408864, 460875493326, 243505713063, 12364676380, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8497 = true := by
  decide +kernel

theorem tot8497 : totK PD2M8K2 D2M8K2.t8497 = [0, 238571976183, 499612001958, 149381425552, 5890129376, 0, 0, 0] := by
  decide +kernel

theorem rows8498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8498 = true := by
  decide +kernel

theorem tot8498 : totK PD2M8K2 D2M8K2.t8498 = [67565028568, 289964775071, 388480987281, 119749526264, 5775380855, 0, 0, 0] := by
  decide +kernel

theorem rows8499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8499 = true := by
  decide +kernel

theorem tot8499 : totK PD2M8K2 D2M8K2.t8499 = [182755202180, 468242734515, 259280958415, 23190855559, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
