import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11744 = true := by
  decide +kernel

theorem tot11744 : totK PD2M8K2 D2M8K2.t11744 = [0, 0, 318935865755, 511777117895, 70566790970, 0, 0, 0] := by
  decide +kernel

theorem rows11745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11745 = true := by
  decide +kernel

theorem tot11745 : totK PD2M8K2 D2M8K2.t11745 = [0, 158898794424, 369608629456, 279413850923, 81279439072, 3820764243, 0, 0] := by
  decide +kernel

theorem rows11746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11746 = true := by
  decide +kernel

theorem tot11746 : totK PD2M8K2 D2M8K2.t11746 = [0, 199671656459, 466378687382, 211515309756, 12543052785, 0, 0, 0] := by
  decide +kernel

theorem rows11747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11747 = true := by
  decide +kernel

theorem tot11747 : totK PD2M8K2 D2M8K2.t11747 = [0, 19692840307, 309802676125, 458056558987, 100899457370, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
