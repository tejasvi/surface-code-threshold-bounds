import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15420 = true := by
  decide +kernel

theorem tot15420 : totK PD2M8K2 D2M8K2.t15420 = [0, 190392201481, 461252538017, 249731130601, 23184578135, 0, 0, 0] := by
  decide +kernel

theorem rows15421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15421 = true := by
  decide +kernel

theorem tot15421 : totK PD2M8K2 D2M8K2.t15421 = [0, 200044059041, 485824239898, 220181724046, 14338641010, 0, 0, 0] := by
  decide +kernel

theorem rows15422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15422 = true := by
  decide +kernel

theorem tot15422 : totK PD2M8K2 D2M8K2.t15422 = [0, 0, 297872448265, 490994770316, 107492010523, 1268739303, 0, 0] := by
  decide +kernel

theorem rows15423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15423 = true := by
  decide +kernel

theorem tot15423 : totK PD2M8K2 D2M8K2.t15423 = [0, 0, 217121690833, 483758861040, 184902103025, 7416031382, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
