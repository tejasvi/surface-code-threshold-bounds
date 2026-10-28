import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11180 = true := by
  decide +kernel

theorem tot11180 : totK PD2M8K2 D2M8K2.t11180 = [0, 121453431582, 419386685286, 312018686821, 29429923011, 0, 0, 0] := by
  decide +kernel

theorem rows11181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11181 = true := by
  decide +kernel

theorem tot11181 : totK PD2M8K2 D2M8K2.t11181 = [0, 0, 277013133171, 503653303988, 110222175298, 1369150432, 0, 0] := by
  decide +kernel

theorem rows11182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11182 = true := by
  decide +kernel

theorem tot11182 : totK PD2M8K2 D2M8K2.t11182 = [0, 173017097749, 426497678652, 291916686298, 35913947835, 0, 0, 0] := by
  decide +kernel

theorem rows11183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11183 = true := by
  decide +kernel

theorem tot11183 : totK PD2M8K2 D2M8K2.t11183 = [0, 172117742541, 458779389134, 254165050201, 18045717838, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
