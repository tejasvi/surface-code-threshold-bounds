import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3704 = true := by
  decide +kernel

theorem tot3704 : totK PD2M8K2 D2M8K2.t3704 = [180809944048, 462289798456, 239631258057, 16759231668, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3705 = true := by
  decide +kernel

theorem tot3705 : totK PD2M8K2 D2M8K2.t3705 = [56509611388, 326695799219, 423418623566, 97225454125, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows3706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3706 = true := by
  decide +kernel

theorem tot3706 : totK PD2M8K2 D2M8K2.t3706 = [0, 201646628630, 478128784532, 188508320272, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows3707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3707 = true := by
  decide +kernel

theorem tot3707 : totK PD2M8K2 D2M8K2.t3707 = [0, 190313865867, 473661473833, 218591232007, 14707859566, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
