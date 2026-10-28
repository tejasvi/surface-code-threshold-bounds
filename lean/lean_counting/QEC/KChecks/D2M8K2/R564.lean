import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2256 = true := by
  decide +kernel

theorem tot2256 : totK PD2M8K2 D2M8K2.t2256 = [0, 0, 196670656020, 469551851727, 207472198557, 12421902774, 0, 0] := by
  decide +kernel

theorem rows2257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2257 = true := by
  decide +kernel

theorem tot2257 : totK PD2M8K2 D2M8K2.t2257 = [0, 0, 21476682560, 338834334924, 416092880345, 69882417142, 1138244013, 0] := by
  decide +kernel

theorem rows2258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2258 = true := by
  decide +kernel

theorem tot2258 : totK PD2M8K2 D2M8K2.t2258 = [0, 0, 105778542519, 409853009465, 344114415752, 34218188374, 0, 0] := by
  decide +kernel

theorem rows2259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2259 = true := by
  decide +kernel

theorem tot2259 : totK PD2M8K2 D2M8K2.t2259 = [0, 0, 190859734770, 474289692806, 203896265510, 14633607569, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
