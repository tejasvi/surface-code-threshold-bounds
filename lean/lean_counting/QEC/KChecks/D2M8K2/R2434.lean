import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9736 = true := by
  decide +kernel

theorem tot9736 : totK PD2M8K2 D2M8K2.t9736 = [0, 18445043044, 228593118053, 458055192875, 163966027724, 7393276268, 0, 0] := by
  decide +kernel

theorem rows9737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9737 = true := by
  decide +kernel

theorem tot9737 : totK PD2M8K2 D2M8K2.t9737 = [0, 187393059378, 451737294302, 243464024134, 22766485928, 0, 0, 0] := by
  decide +kernel

theorem rows9738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9738 = true := by
  decide +kernel

theorem tot9738 : totK PD2M8K2 D2M8K2.t9738 = [0, 204789322851, 484712729089, 207820489399, 9650676295, 0, 0, 0] := by
  decide +kernel

theorem rows9739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9739 = true := by
  decide +kernel

theorem tot9739 : totK PD2M8K2 D2M8K2.t9739 = [0, 8125304319, 301823286417, 479869113354, 98564365429, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
