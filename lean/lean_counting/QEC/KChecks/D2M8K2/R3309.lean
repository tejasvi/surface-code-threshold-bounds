import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13236 = true := by
  decide +kernel

theorem tot13236 : totK PD2M8K2 D2M8K2.t13236 = [0, 0, 179910113021, 454918360247, 217623534037, 16632994142, 0, 0] := by
  decide +kernel

theorem rows13237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13237 = true := by
  decide +kernel

theorem tot13237 : totK PD2M8K2 D2M8K2.t13237 = [0, 0, 96978672414, 405913878749, 316847639096, 35860205471, 0, 0] := by
  decide +kernel

theorem rows13238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13238 = true := by
  decide +kernel

theorem tot13238 : totK PD2M8K2 D2M8K2.t13238 = [0, 0, 0, 313529447872, 443843679749, 82561035220, 1369150432, 0] := by
  decide +kernel

theorem rows13239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13239 = true := by
  decide +kernel

theorem tot13239 : totK PD2M8K2 D2M8K2.t13239 = [0, 0, 206785858850, 478399900539, 197961506965, 8224994859, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
