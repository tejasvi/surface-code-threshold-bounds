import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15148 = true := by
  decide +kernel

theorem tot15148 : totK PD2M8K2 D2M8K2.t15148 = [0, 150233096782, 461160019947, 288384923540, 25164622248, 0, 0, 0] := by
  decide +kernel

theorem rows15149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15149 = true := by
  decide +kernel

theorem tot15149 : totK PD2M8K2 D2M8K2.t15149 = [0, 181212425085, 467584168070, 249790997104, 16173420730, 0, 0, 0] := by
  decide +kernel

theorem rows15150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15150 = true := by
  decide +kernel

theorem tot15150 : totK PD2M8K2 D2M8K2.t15150 = [0, 0, 246548291154, 504870048566, 143066939187, 2303467656, 0, 0] := by
  decide +kernel

theorem rows15151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15151 = true := by
  decide +kernel

theorem tot15151 : totK PD2M8K2 D2M8K2.t15151 = [0, 0, 179976565996, 473397717892, 219472344733, 11163613648, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
