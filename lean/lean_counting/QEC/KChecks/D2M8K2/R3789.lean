import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15156 = true := by
  decide +kernel

theorem tot15156 : totK PD2M8K2 D2M8K2.t15156 = [0, 0, 174600732985, 459294366233, 254020238306, 20004329641, 0, 0] := by
  decide +kernel

theorem rows15157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15157 = true := by
  decide +kernel

theorem tot15157 : totK PD2M8K2 D2M8K2.t15157 = [0, 0, 198417831232, 476742962710, 221165138248, 12888528110, 0, 0] := by
  decide +kernel

theorem rows15158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15158 = true := by
  decide +kernel

theorem tot15158 : totK PD2M8K2 D2M8K2.t15158 = [0, 0, 169186533009, 444838343616, 272373686658, 22862741806, 0, 0] := by
  decide +kernel

theorem rows15159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15159 = true := by
  decide +kernel

theorem tot15159 : totK PD2M8K2 D2M8K2.t15159 = [0, 0, 129279043351, 439246347022, 287944094189, 22360307755, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
