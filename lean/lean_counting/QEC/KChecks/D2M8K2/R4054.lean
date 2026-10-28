import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16216 = true := by
  decide +kernel

theorem tot16216 : totK PD2M8K2 D2M8K2.t16216 = [0, 182497872290, 475922130584, 250167785918, 16684772691, 0, 0, 0] := by
  decide +kernel

theorem rows16217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16217 = true := by
  decide +kernel

theorem tot16217 : totK PD2M8K2 D2M8K2.t16217 = [0, 0, 275417917301, 506729949684, 121063254038, 1268739303, 0, 0] := by
  decide +kernel

theorem rows16218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16218 = true := by
  decide +kernel

theorem tot16218 : totK PD2M8K2 D2M8K2.t16218 = [0, 0, 209727875688, 485529585941, 184335299836, 7442000727, 0, 0] := by
  decide +kernel

theorem rows16219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16219 = true := by
  decide +kernel

theorem tot16219 : totK PD2M8K2 D2M8K2.t16219 = [0, 0, 175737509362, 476962692578, 221820967335, 14707859566, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
