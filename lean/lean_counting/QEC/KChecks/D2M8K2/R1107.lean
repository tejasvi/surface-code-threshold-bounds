import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4428 = true := by
  decide +kernel

theorem tot4428 : totK PD2M8K2 D2M8K2.t4428 = [0, 0, 156742398351, 396064688586, 287474691459, 73317543707, 1415142070, 0] := by
  decide +kernel

theorem rows4429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4429 = true := by
  decide +kernel

theorem tot4429 : totK PD2M8K2 D2M8K2.t4429 = [0, 0, 184228830559, 464277509593, 244219428931, 16392988126, 0, 0] := by
  decide +kernel

theorem rows4430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4430 = true := by
  decide +kernel

theorem tot4430 : totK PD2M8K2 D2M8K2.t4430 = [0, 0, 71186809760, 405192517813, 383187714874, 51952882875, 0, 0] := by
  decide +kernel

theorem rows4431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4431 = true := by
  decide +kernel

theorem tot4431 : totK PD2M8K2 D2M8K2.t4431 = [0, 0, 0, 212010348245, 515090703921, 155956417142, 2484078857, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
