import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t996 = true := by
  decide +kernel

theorem tot996 : totK PD2M8K2 D2M8K2.t996 = [186014084210, 443168105665, 258152393815, 29034852161, 0, 0, 0, 0] := by
  decide +kernel

theorem rows997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t997 = true := by
  decide +kernel

theorem tot997 : totK PD2M8K2 D2M8K2.t997 = [188356179627, 477214406067, 226311024085, 12432084775, 0, 0, 0, 0] := by
  decide +kernel

theorem rows998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t998 = true := by
  decide +kernel

theorem tot998 : totK PD2M8K2 D2M8K2.t998 = [0, 207040112285, 440885882062, 227188345923, 24160238051, 0, 0, 0] := by
  decide +kernel

theorem rows999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t999 = true := by
  decide +kernel

theorem tot999 : totK PD2M8K2 D2M8K2.t999 = [0, 204035908957, 481724925816, 204701607658, 6542401075, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
