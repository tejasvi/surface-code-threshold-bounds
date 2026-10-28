import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t300 = true := by
  decide +kernel

theorem tot300 : totK PD2M8K2 D2M8K2.t300 = [92230071108, 416825562900, 367495820729, 34966118826, 0, 0, 0, 0] := by
  decide +kernel

theorem rows301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t301 = true := by
  decide +kernel

theorem tot301 : totK PD2M8K2 D2M8K2.t301 = [0, 204721218727, 490415682717, 181141783784, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t302 = true := by
  decide +kernel

theorem tot302 : totK PD2M8K2 D2M8K2.t302 = [0, 190686414619, 458603670596, 217325251249, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t303 = true := by
  decide +kernel

theorem tot303 : totK PD2M8K2 D2M8K2.t303 = [0, 189179843718, 484244509144, 206010149709, 9610913563, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
