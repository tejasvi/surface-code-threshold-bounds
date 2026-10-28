import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows72 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t72 = true := by
  decide +kernel

theorem tot72 : totK PD2M8K2 D2M8K2.t72 = [162528288142, 428172589140, 304369303528, 37626210027, 0, 0, 0, 0] := by
  decide +kernel

theorem rows73 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t73 = true := by
  decide +kernel

theorem tot73 : totK PD2M8K2 D2M8K2.t73 = [165324708119, 461212555431, 256453798834, 14570397433, 0, 0, 0, 0] := by
  decide +kernel

theorem rows74 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t74 = true := by
  decide +kernel

theorem tot74 : totK PD2M8K2 D2M8K2.t74 = [0, 199083086374, 453362824020, 229515686522, 22534614033, 0, 0, 0] := by
  decide +kernel

theorem rows75 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t75 = true := by
  decide +kernel

theorem tot75 : totK PD2M8K2 D2M8K2.t75 = [35815623986, 213595887893, 433751750605, 199808010366, 8197853881, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
