import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10468 = true := by
  decide +kernel

theorem tot10468 : totK PD2M8K2 D2M8K2.t10468 = [0, 0, 92722817510, 389002326804, 356313084403, 53672195226, 1096505104, 0] := by
  decide +kernel

theorem rows10469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10469 = true := by
  decide +kernel

theorem tot10469 : totK PD2M8K2 D2M8K2.t10469 = [0, 0, 0, 327857825663, 512554967191, 68648488586, 0, 0] := by
  decide +kernel

theorem rows10470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10470 = true := by
  decide +kernel

theorem tot10470 : totK PD2M8K2 D2M8K2.t10470 = [0, 0, 0, 179733555339, 486603554169, 179260403668, 6314610048, 0] := by
  decide +kernel

theorem rows10471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10471 = true := by
  decide +kernel

theorem tot10471 : totK PD2M8K2 D2M8K2.t10471 = [0, 0, 0, 175665226296, 468806355657, 205971615219, 12317960536, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
