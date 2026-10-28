import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9612 = true := by
  decide +kernel

theorem tot9612 : totK PD2M8K2 D2M8K2.t9612 = [0, 0, 281600083120, 499570069118, 109398806857, 1242138600, 0, 0] := by
  decide +kernel

theorem rows9613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9613 = true := by
  decide +kernel

theorem tot9613 : totK PD2M8K2 D2M8K2.t9613 = [0, 0, 177392706071, 472648304352, 199289274981, 8407946489, 0, 0] := by
  decide +kernel

theorem rows9614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9614 = true := by
  decide +kernel

theorem tot9614 : totK PD2M8K2 D2M8K2.t9614 = [0, 176822738200, 424817173729, 205354529153, 71657028218, 12101082977, 0, 0] := by
  decide +kernel

theorem rows9615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9615 = true := by
  decide +kernel

theorem tot9615 : totK PD2M8K2 D2M8K2.t9615 = [0, 175477775059, 454998124367, 231185313917, 14840817531, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
