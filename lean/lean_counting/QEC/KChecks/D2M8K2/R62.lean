import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t248 = true := by
  decide +kernel

theorem tot248 : totK PD2M8K2 D2M8K2.t248 = [0, 73181852959, 370420017552, 417728385486, 54731263952, 0, 0, 0] := by
  decide +kernel

theorem rows249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t249 = true := by
  decide +kernel

theorem tot249 : totK PD2M8K2 D2M8K2.t249 = [0, 163986592883, 442369735436, 267534566958, 19906737986, 0, 0, 0] := by
  decide +kernel

theorem rows250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t250 = true := by
  decide +kernel

theorem tot250 : totK PD2M8K2 D2M8K2.t250 = [0, 87930784875, 408371528078, 367626618352, 42983413880, 0, 0, 0] := by
  decide +kernel

theorem rows251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t251 = true := by
  decide +kernel

theorem tot251 : totK PD2M8K2 D2M8K2.t251 = [0, 84834164928, 317711691012, 398330039540, 96672199712, 1409560813, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
