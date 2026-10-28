import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3872 = true := by
  decide +kernel

theorem tot3872 : totK PD2M8K2 D2M8K2.t3872 = [0, 147791837144, 443058229459, 282047832445, 24909969674, 0, 0, 0] := by
  decide +kernel

theorem rows3873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3873 = true := by
  decide +kernel

theorem tot3873 : totK PD2M8K2 D2M8K2.t3873 = [0, 0, 217167654972, 497399609790, 160160171890, 5172807878, 0, 0] := by
  decide +kernel

theorem rows3874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3874 = true := by
  decide +kernel

theorem tot3874 : totK PD2M8K2 D2M8K2.t3874 = [0, 136776095992, 424655637215, 306944844535, 35023965945, 0, 0, 0] := by
  decide +kernel

theorem rows3875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3875 = true := by
  decide +kernel

theorem tot3875 : totK PD2M8K2 D2M8K2.t3875 = [0, 176735811332, 441353275595, 255381681054, 26998748527, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
