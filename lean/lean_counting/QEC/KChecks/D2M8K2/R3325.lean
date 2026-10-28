import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13300 = true := by
  decide +kernel

theorem tot13300 : totK PD2M8K2 D2M8K2.t13300 = [0, 0, 274758199093, 522301210571, 104003331557, 1096505104, 0, 0] := by
  decide +kernel

theorem rows13301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13301 = true := by
  decide +kernel

theorem tot13301 : totK PD2M8K2 D2M8K2.t13301 = [0, 91794050722, 330907868332, 354930900447, 99317672393, 3884009855, 0, 0] := by
  decide +kernel

theorem rows13302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13302 = true := by
  decide +kernel

theorem tot13302 : totK PD2M8K2 D2M8K2.t13302 = [0, 189500957594, 470107986061, 244079714484, 18567406258, 0, 0, 0] := by
  decide +kernel

theorem rows13303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13303 = true := by
  decide +kernel

theorem tot13303 : totK PD2M8K2 D2M8K2.t13303 = [0, 44832752452, 321963821410, 425120275807, 90970303696, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
