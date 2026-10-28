import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10908 = true := by
  decide +kernel

theorem tot10908 : totK PD2M8K2 D2M8K2.t10908 = [0, 0, 244551511857, 448786820250, 195605451899, 21149760195, 0, 0] := by
  decide +kernel

theorem rows10909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10909 = true := by
  decide +kernel

theorem tot10909 : totK PD2M8K2 D2M8K2.t10909 = [0, 0, 154583783201, 482207319795, 239443048265, 6614782499, 0, 0] := by
  decide +kernel

theorem rows10910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10910 = true := by
  decide +kernel

theorem tot10910 : totK PD2M8K2 D2M8K2.t10910 = [0, 117828091628, 341573869117, 316226774216, 116654976835, 8204069046, 0, 0] := by
  decide +kernel

theorem rows10911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10911 = true := by
  decide +kernel

theorem tot10911 : totK PD2M8K2 D2M8K2.t10911 = [0, 159411907155, 438756363055, 272013705575, 28359988553, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
