import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13132 = true := by
  decide +kernel

theorem tot13132 : totK PD2M8K2 D2M8K2.t13132 = [0, 91400987495, 389160992184, 352512205811, 52879521635, 1096505104, 0, 0] := by
  decide +kernel

theorem rows13133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13133 = true := by
  decide +kernel

theorem tot13133 : totK PD2M8K2 D2M8K2.t13133 = [0, 0, 313035723022, 519382267843, 84697524980, 0, 0, 0] := by
  decide +kernel

theorem rows13134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13134 = true := by
  decide +kernel

theorem tot13134 : totK PD2M8K2 D2M8K2.t13134 = [0, 171086798616, 391685264013, 247681368253, 76585100507, 3884009855, 0, 0] := by
  decide +kernel

theorem rows13135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13135 = true := by
  decide +kernel

theorem tot13135 : totK PD2M8K2 D2M8K2.t13135 = [0, 145107955828, 431088731438, 298367787060, 27452173878, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
