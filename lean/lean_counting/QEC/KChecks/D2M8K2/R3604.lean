import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14416 = true := by
  decide +kernel

theorem tot14416 : totK PD2M8K2 D2M8K2.t14416 = [0, 0, 259890542740, 487737956008, 149097375653, 8419352411, 0, 0] := by
  decide +kernel

theorem rows14417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14417 = true := by
  decide +kernel

theorem tot14417 : totK PD2M8K2 D2M8K2.t14417 = [0, 166719348841, 446042982377, 275202548977, 35820188896, 0, 0, 0] := by
  decide +kernel

theorem rows14418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14418 = true := by
  decide +kernel

theorem tot14418 : totK PD2M8K2 D2M8K2.t14418 = [0, 178019847832, 452205328366, 271766674189, 19446195151, 0, 0, 0] := by
  decide +kernel

theorem rows14419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14419 = true := by
  decide +kernel

theorem tot14419 : totK PD2M8K2 D2M8K2.t14419 = [0, 0, 284221146599, 502327619573, 107582958835, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
