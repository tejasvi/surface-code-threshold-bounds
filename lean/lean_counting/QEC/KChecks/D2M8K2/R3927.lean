import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15708 = true := by
  decide +kernel

theorem tot15708 : totK PD2M8K2 D2M8K2.t15708 = [0, 0, 87430897285, 415264715611, 369848431555, 41770962014, 0, 0] := by
  decide +kernel

theorem rows15709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15709 = true := by
  decide +kernel

theorem tot15709 : totK PD2M8K2 D2M8K2.t15709 = [0, 0, 0, 276982803485, 493911755838, 127926634058, 4231263225, 0] := by
  decide +kernel

theorem rows15710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15710 = true := by
  decide +kernel

theorem tot15710 : totK PD2M8K2 D2M8K2.t15710 = [0, 0, 176976095158, 452377533578, 278440407584, 33181601786, 0, 0] := by
  decide +kernel

theorem rows15711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15711 = true := by
  decide +kernel

theorem tot15711 : totK PD2M8K2 D2M8K2.t15711 = [0, 0, 260300820902, 495127674847, 164811373215, 9038053038, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
