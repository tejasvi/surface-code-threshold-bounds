import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7888 = true := by
  decide +kernel

theorem tot7888 : totK PD2M8K2 D2M8K2.t7888 = [0, 0, 212258454770, 499766612182, 193844530808, 5430665091, 0, 0] := by
  decide +kernel

theorem rows7889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7889 = true := by
  decide +kernel

theorem tot7889 : totK PD2M8K2 D2M8K2.t7889 = [0, 172450032168, 450092267436, 253597101876, 28253448652, 0, 0, 0] := by
  decide +kernel

theorem rows7890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7890 = true := by
  decide +kernel

theorem tot7890 : totK PD2M8K2 D2M8K2.t7890 = [0, 180676145643, 458770603693, 252389550797, 18035425957, 0, 0, 0] := by
  decide +kernel

theorem rows7891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7891 = true := by
  decide +kernel

theorem tot7891 : totK PD2M8K2 D2M8K2.t7891 = [0, 72819342185, 335042654213, 392240947733, 87012507981, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
