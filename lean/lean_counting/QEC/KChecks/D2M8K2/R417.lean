import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1668 = true := by
  decide +kernel

theorem tot1668 : totK PD2M8K2 D2M8K2.t1668 = [0, 0, 163960758814, 451303218162, 259353848670, 21689717858, 0, 0] := by
  decide +kernel

theorem rows1669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1669 = true := by
  decide +kernel

theorem tot1669 : totK PD2M8K2 D2M8K2.t1669 = [0, 0, 158219858702, 468664894910, 245442247275, 14144469879, 0, 0] := by
  decide +kernel

theorem rows1670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1670 = true := by
  decide +kernel

theorem tot1670 : totK PD2M8K2 D2M8K2.t1670 = [0, 0, 88983089131, 357257944458, 366467295764, 66405288041, 1107157161, 0] := by
  decide +kernel

theorem rows1671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1671 = true := by
  decide +kernel

theorem tot1671 : totK PD2M8K2 D2M8K2.t1671 = [0, 0, 18514691823, 290504300205, 441896409832, 102900127946, 3824247485, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
