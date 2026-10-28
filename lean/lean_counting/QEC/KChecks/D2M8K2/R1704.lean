import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6816 = true := by
  decide +kernel

theorem tot6816 : totK PD2M8K2 D2M8K2.t6816 = [0, 215578233993, 483731748219, 185378522260, 7439461435, 0, 0, 0] := by
  decide +kernel

theorem rows6817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6817 = true := by
  decide +kernel

theorem tot6817 : totK PD2M8K2 D2M8K2.t6817 = [0, 190377182258, 468671618171, 218053058651, 14704558535, 0, 0, 0] := by
  decide +kernel

theorem rows6818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6818 = true := by
  decide +kernel

theorem tot6818 : totK PD2M8K2 D2M8K2.t6818 = [0, 181820956151, 464632072140, 206898216230, 10735115630, 0, 0, 0] := by
  decide +kernel

theorem rows6819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6819 = true := by
  decide +kernel

theorem tot6819 : totK PD2M8K2 D2M8K2.t6819 = [0, 86953184342, 364038121342, 351788912457, 61646385942, 1206465782, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
