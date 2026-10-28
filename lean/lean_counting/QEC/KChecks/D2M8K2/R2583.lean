import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10332 = true := by
  decide +kernel

theorem tot10332 : totK PD2M8K2 D2M8K2.t10332 = [0, 14918351735, 6276014511, 274984929960, 461984109278, 111341065102, 3882006667, 0] := by
  decide +kernel

theorem rows10333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10333 = true := by
  decide +kernel

theorem tot10333 : totK PD2M8K2 D2M8K2.t10333 = [0, 203156266160, 482612054584, 197314573092, 8066996984, 0, 0, 0] := by
  decide +kernel

theorem rows10334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10334 = true := by
  decide +kernel

theorem tot10334 : totK PD2M8K2 D2M8K2.t10334 = [0, 189578890932, 472778998186, 214250562520, 12526078277, 0, 0, 0] := by
  decide +kernel

theorem rows10335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10335 = true := by
  decide +kernel

theorem tot10335 : totK PD2M8K2 D2M8K2.t10335 = [0, 0, 282118248384, 501355351790, 105063187050, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
