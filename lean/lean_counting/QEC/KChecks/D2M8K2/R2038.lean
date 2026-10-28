import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8152 = true := by
  decide +kernel

theorem tot8152 : totK PD2M8K2 D2M8K2.t8152 = [0, 50536827603, 320161239743, 423068182683, 90665322505, 1369150432, 0, 0] := by
  decide +kernel

theorem rows8153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8153 = true := by
  decide +kernel

theorem tot8153 : totK PD2M8K2 D2M8K2.t8153 = [0, 80771534998, 367428331589, 414021922818, 50964992418, 0, 0, 0] := by
  decide +kernel

theorem rows8154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8154 = true := by
  decide +kernel

theorem tot8154 : totK PD2M8K2 D2M8K2.t8154 = [0, 165889176817, 451158698013, 273999777654, 28915407768, 0, 0, 0] := by
  decide +kernel

theorem rows8155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8155 = true := by
  decide +kernel

theorem tot8155 : totK PD2M8K2 D2M8K2.t8155 = [0, 157705155861, 471561527007, 268658378043, 15336411845, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
