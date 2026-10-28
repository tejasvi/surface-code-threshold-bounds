import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10096 = true := by
  decide +kernel

theorem tot10096 : totK PD2M8K2 D2M8K2.t10096 = [0, 172950304722, 389692924399, 247547921799, 99682613371, 6799735859, 0, 0] := by
  decide +kernel

theorem rows10097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10097 = true := by
  decide +kernel

theorem tot10097 : totK PD2M8K2 D2M8K2.t10097 = [0, 180284548937, 436769090792, 275142523776, 30437197709, 0, 0, 0] := by
  decide +kernel

theorem rows10098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10098 = true := by
  decide +kernel

theorem tot10098 : totK PD2M8K2 D2M8K2.t10098 = [0, 88383717769, 399192808740, 356019154551, 51319836919, 1198073392, 0, 0] := by
  decide +kernel

theorem rows10099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10099 = true := by
  decide +kernel

theorem tot10099 : totK PD2M8K2 D2M8K2.t10099 = [0, 0, 230569597411, 495471106943, 170214862158, 8470662040, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
