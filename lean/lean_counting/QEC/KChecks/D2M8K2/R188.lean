import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t752 = true := by
  decide +kernel

theorem tot752 : totK PD2M8K2 D2M8K2.t752 = [0, 178732250004, 476189295478, 227956132211, 13491800230, 0, 0, 0] := by
  decide +kernel

theorem rows753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t753 = true := by
  decide +kernel

theorem tot753 : totK PD2M8K2 D2M8K2.t753 = [0, 0, 305187512307, 488346848567, 86722339606, 1107157161, 0, 0] := by
  decide +kernel

theorem rows754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t754 = true := by
  decide +kernel

theorem tot754 : totK PD2M8K2 D2M8K2.t754 = [0, 86161578940, 332564443646, 354771754107, 95207815280, 3824247485, 0, 0] := by
  decide +kernel

theorem rows755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t755 = true := by
  decide +kernel

theorem tot755 : totK PD2M8K2 D2M8K2.t755 = [0, 170865617418, 463445455070, 250684864823, 19771223224, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
