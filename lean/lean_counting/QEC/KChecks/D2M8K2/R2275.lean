import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9100 = true := by
  decide +kernel

theorem tot9100 : totK PD2M8K2 D2M8K2.t9100 = [0, 18870634022, 194712701291, 461475747397, 225575492267, 15086715677, 0, 0] := by
  decide +kernel

theorem rows9101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9101 = true := by
  decide +kernel

theorem tot9101 : totK PD2M8K2 D2M8K2.t9101 = [0, 197830181621, 470050363456, 197424864507, 9785860968, 0, 0, 0] := by
  decide +kernel

theorem rows9102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9102 = true := by
  decide +kernel

theorem tot9102 : totK PD2M8K2 D2M8K2.t9102 = [0, 188754091840, 471814894215, 217400173267, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows9103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9103 = true := by
  decide +kernel

theorem tot9103 : totK PD2M8K2 D2M8K2.t9103 = [0, 0, 281998307950, 492781335276, 96582065524, 1310517177, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
