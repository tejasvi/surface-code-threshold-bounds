import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14468 = true := by
  decide +kernel

theorem tot14468 : totK PD2M8K2 D2M8K2.t14468 = [107360506841, 325134290648, 353334213748, 95521855046, 3575904516, 0, 0, 0] := by
  decide +kernel

theorem rows14469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14469 = true := by
  decide +kernel

theorem tot14469 : totK PD2M8K2 D2M8K2.t14469 = [186451628852, 453034163951, 261967837267, 29176232699, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14470 = true := by
  decide +kernel

theorem tot14470 : totK PD2M8K2 D2M8K2.t14470 = [88800000258, 392061907433, 335623311186, 54947909636, 1096156699, 0, 0, 0] := by
  decide +kernel

theorem rows14471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14471 = true := by
  decide +kernel

theorem tot14471 : totK PD2M8K2 D2M8K2.t14471 = [0, 312427257466, 521541956221, 84823787886, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
