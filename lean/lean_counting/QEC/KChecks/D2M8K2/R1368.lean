import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5472 = true := by
  decide +kernel

theorem tot5472 : totK PD2M8K2 D2M8K2.t5472 = [0, 0, 0, 272192520743, 503630447835, 101928121805, 1369150432, 0] := by
  decide +kernel

theorem rows5473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5473 = true := by
  decide +kernel

theorem tot5473 : totK PD2M8K2 D2M8K2.t5473 = [0, 0, 126523862594, 407881134782, 352073819658, 42189980487, 0, 0] := by
  decide +kernel

theorem rows5474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5474 = true := by
  decide +kernel

theorem tot5474 : totK PD2M8K2 D2M8K2.t5474 = [0, 0, 177883144228, 461818175178, 240264393208, 15397324911, 0, 0] := by
  decide +kernel

theorem rows5475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5475 = true := by
  decide +kernel

theorem tot5475 : totK PD2M8K2 D2M8K2.t5475 = [0, 0, 123174868417, 443856569131, 322364054501, 36244227136, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
