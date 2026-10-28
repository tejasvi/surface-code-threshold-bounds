import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16208 = true := by
  decide +kernel

theorem tot16208 : totK PD2M8K2 D2M8K2.t16208 = [0, 122594025680, 436010604634, 322661044380, 26985250065, 0, 0, 0] := by
  decide +kernel

theorem rows16209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16209 = true := by
  decide +kernel

theorem tot16209 : totK PD2M8K2 D2M8K2.t16209 = [0, 0, 205985095841, 490129374448, 181625241743, 9252302862, 0, 0] := by
  decide +kernel

theorem rows16210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16210 = true := by
  decide +kernel

theorem tot16210 : totK PD2M8K2 D2M8K2.t16210 = [0, 96771261634, 348646894798, 356587648255, 86623333783, 1950893645, 0, 0] := by
  decide +kernel

theorem rows16211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16211 = true := by
  decide +kernel

theorem tot16211 : totK PD2M8K2 D2M8K2.t16211 = [0, 164668778926, 445246155094, 276600881337, 30271926621, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
