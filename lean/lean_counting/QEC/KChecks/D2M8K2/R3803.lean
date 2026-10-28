import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15212 = true := by
  decide +kernel

theorem tot15212 : totK PD2M8K2 D2M8K2.t15212 = [0, 0, 180225351207, 477255093705, 209660102276, 7913321096, 0, 0] := by
  decide +kernel

theorem rows15213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15213 = true := by
  decide +kernel

theorem tot15213 : totK PD2M8K2 D2M8K2.t15213 = [0, 0, 63469598011, 335623666581, 409041730735, 78395439385, 1310285577, 0] := by
  decide +kernel

theorem rows15214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15214 = true := by
  decide +kernel

theorem tot15214 : totK PD2M8K2 D2M8K2.t15214 = [0, 0, 56392223216, 355474447831, 435785033154, 43756317456, 0, 0] := by
  decide +kernel

theorem rows15215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15215 = true := by
  decide +kernel

theorem tot15215 : totK PD2M8K2 D2M8K2.t15215 = [0, 0, 179592505694, 451409146756, 271393754707, 25024348245, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
