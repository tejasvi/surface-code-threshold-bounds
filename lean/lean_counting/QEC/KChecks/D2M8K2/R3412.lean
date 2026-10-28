import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13648 = true := by
  decide +kernel

theorem tot13648 : totK PD2M8K2 D2M8K2.t13648 = [0, 208908465156, 465126258807, 191557610434, 12045711471, 0, 0, 0] := by
  decide +kernel

theorem rows13649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13649 = true := by
  decide +kernel

theorem tot13649 : totK PD2M8K2 D2M8K2.t13649 = [190740266346, 452901090920, 256962421870, 27623512429, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13650 = true := by
  decide +kernel

theorem tot13650 : totK PD2M8K2 D2M8K2.t13650 = [184276628754, 473465315480, 236180126171, 16684993013, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13651 = true := by
  decide +kernel

theorem tot13651 : totK PD2M8K2 D2M8K2.t13651 = [63891577958, 331799147316, 414716197004, 96199216822, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
