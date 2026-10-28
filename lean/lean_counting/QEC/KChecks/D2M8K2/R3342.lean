import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13368 = true := by
  decide +kernel

theorem tot13368 : totK PD2M8K2 D2M8K2.t13368 = [0, 160444419556, 443293861237, 283197398865, 30374154795, 0, 0, 0] := by
  decide +kernel

theorem rows13369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13369 = true := by
  decide +kernel

theorem tot13369 : totK PD2M8K2 D2M8K2.t13369 = [0, 152795574251, 449534739632, 277642177994, 19753850370, 0, 0, 0] := by
  decide +kernel

theorem rows13370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13370 = true := by
  decide +kernel

theorem tot13370 : totK PD2M8K2 D2M8K2.t13370 = [0, 0, 208503482577, 482079004966, 180182237933, 8214782009, 0, 0] := by
  decide +kernel

theorem rows13371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13371 = true := by
  decide +kernel

theorem tot13371 : totK PD2M8K2 D2M8K2.t13371 = [0, 86527685341, 306674646524, 381498832536, 107197129694, 5035903252, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
