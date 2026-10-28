import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8128 = true := by
  decide +kernel

theorem tot8128 : totK PD2M8K2 D2M8K2.t8128 = [0, 80968783094, 325165023980, 372400645542, 99190265683, 3462014130, 0, 0] := by
  decide +kernel

theorem rows8129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8129 = true := by
  decide +kernel

theorem tot8129 : totK PD2M8K2 D2M8K2.t8129 = [0, 174267827696, 458917057254, 268484546728, 23942580336, 0, 0, 0] := by
  decide +kernel

theorem rows8130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8130 = true := by
  decide +kernel

theorem tot8130 : totK PD2M8K2 D2M8K2.t8130 = [0, 87802588610, 353956342493, 373558189844, 69549274716, 1096505104, 0, 0] := by
  decide +kernel

theorem rows8131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8131 = true := by
  decide +kernel

theorem tot8131 : totK PD2M8K2 D2M8K2.t8131 = [0, 66329892980, 307170906798, 415317175051, 106485490516, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
