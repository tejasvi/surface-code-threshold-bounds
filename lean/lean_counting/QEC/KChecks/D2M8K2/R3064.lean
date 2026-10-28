import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12256 = true := by
  decide +kernel

theorem tot12256 : totK PD2M8K2 D2M8K2.t12256 = [66391032691, 290438360565, 419759446650, 115357001155, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows12257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12257 = true := by
  decide +kernel

theorem tot12257 : totK PD2M8K2 D2M8K2.t12257 = [186757018641, 460981579513, 247671086713, 23038841457, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12258 = true := by
  decide +kernel

theorem tot12258 : totK PD2M8K2 D2M8K2.t12258 = [72979709436, 354496310874, 382769296516, 72670162915, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows12259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12259 = true := by
  decide +kernel

theorem tot12259 : totK PD2M8K2 D2M8K2.t12259 = [0, 244839774218, 496286876274, 151208203056, 3699256714, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
