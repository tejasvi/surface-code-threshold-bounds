import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15696 = true := by
  decide +kernel

theorem tot15696 : totK PD2M8K2 D2M8K2.t15696 = [0, 0, 0, 205846557137, 494995723981, 177842211376, 5745690908, 0] := by
  decide +kernel

theorem rows15697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15697 = true := by
  decide +kernel

theorem tot15697 : totK PD2M8K2 D2M8K2.t15697 = [0, 0, 0, 171186672789, 473644945826, 203329145099, 11166525537, 0] := by
  decide +kernel

theorem rows15698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15698 = true := by
  decide +kernel

theorem tot15698 : totK PD2M8K2 D2M8K2.t15698 = [0, 0, 0, 320552906776, 491691584275, 77674174574, 0, 0] := by
  decide +kernel

theorem rows15699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15699 = true := by
  decide +kernel

theorem tot15699 : totK PD2M8K2 D2M8K2.t15699 = [0, 0, 0, 252465587378, 490775937191, 125500173279, 2518061560, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
