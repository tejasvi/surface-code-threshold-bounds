import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4444 = true := by
  decide +kernel

theorem tot4444 : totK PD2M8K2 D2M8K2.t4444 = [0, 82360505463, 312338605574, 386912619158, 100602287777, 3462014130, 0, 0] := by
  decide +kernel

theorem rows4445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4445 = true := by
  decide +kernel

theorem tot4445 : totK PD2M8K2 D2M8K2.t4445 = [0, 176912389090, 460311725460, 256964495545, 22925328448, 0, 0, 0] := by
  decide +kernel

theorem rows4446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4446 = true := by
  decide +kernel

theorem tot4446 : totK PD2M8K2 D2M8K2.t4446 = [0, 156771832691, 458463527137, 253113432062, 16911452575, 0, 0, 0] := by
  decide +kernel

theorem rows4447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4447 = true := by
  decide +kernel

theorem tot4447 : totK PD2M8K2 D2M8K2.t4447 = [0, 0, 285845063026, 507310016445, 94446857432, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
