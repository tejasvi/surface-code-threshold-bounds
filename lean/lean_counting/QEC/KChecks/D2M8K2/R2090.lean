import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8360 = true := by
  decide +kernel

theorem tot8360 : totK PD2M8K2 D2M8K2.t8360 = [173761297534, 446149815429, 271086595261, 28842251569, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8361 = true := by
  decide +kernel

theorem tot8361 : totK PD2M8K2 D2M8K2.t8361 = [125761367476, 434627850289, 318823189611, 27792183132, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8362 = true := by
  decide +kernel

theorem tot8362 : totK PD2M8K2 D2M8K2.t8362 = [0, 199989003655, 489949459171, 189527156586, 9664716404, 0, 0, 0] := by
  decide +kernel

theorem rows8363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8363 = true := by
  decide +kernel

theorem tot8363 : totK PD2M8K2 D2M8K2.t8363 = [87240234242, 349652604442, 359189313450, 96422533218, 3579068459, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
