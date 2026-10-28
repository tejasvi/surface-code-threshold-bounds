import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4568 = true := by
  decide +kernel

theorem tot4568 : totK PD2M8K2 D2M8K2.t4568 = [0, 0, 141117616596, 455568470913, 296130265830, 22987543742, 0, 0] := by
  decide +kernel

theorem rows4569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4569 = true := by
  decide +kernel

theorem tot4569 : totK PD2M8K2 D2M8K2.t4569 = [0, 0, 0, 226669139848, 508931959909, 156468728983, 2436510558, 0] := by
  decide +kernel

theorem rows4570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4570 = true := by
  decide +kernel

theorem tot4570 : totK PD2M8K2 D2M8K2.t4570 = [0, 0, 70011012546, 234283209202, 386903280374, 179438533852, 11198162423, 0] := by
  decide +kernel

theorem rows4571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4571 = true := by
  decide +kernel

theorem tot4571 : totK PD2M8K2 D2M8K2.t4571 = [0, 0, 167965455853, 464681984491, 235495980097, 12063790339, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
