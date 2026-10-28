import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14424 = true := by
  decide +kernel

theorem tot14424 : totK PD2M8K2 D2M8K2.t14424 = [0, 0, 176903449955, 477848817806, 217204328949, 11102258617, 0, 0] := by
  decide +kernel

theorem rows14425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14425 = true := by
  decide +kernel

theorem tot14425 : totK PD2M8K2 D2M8K2.t14425 = [180272889912, 443704745879, 193466714156, 28888140144, 36254475132, 8576026217, 0, 0] := by
  decide +kernel

theorem rows14426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14426 = true := by
  decide +kernel

theorem tot14426 : totK PD2M8K2 D2M8K2.t14426 = [194053290762, 471439897132, 215179745617, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14427 = true := by
  decide +kernel

theorem tot14427 : totK PD2M8K2 D2M8K2.t14427 = [55093555767, 322505944536, 425077252510, 93805956151, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
