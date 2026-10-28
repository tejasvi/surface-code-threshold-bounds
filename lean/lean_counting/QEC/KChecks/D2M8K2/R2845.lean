import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11380 = true := by
  decide +kernel

theorem tot11380 : totK PD2M8K2 D2M8K2.t11380 = [0, 0, 238146735209, 485224712608, 140776269177, 4879840392, 0, 0] := by
  decide +kernel

theorem rows11381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11381 = true := by
  decide +kernel

theorem tot11381 : totK PD2M8K2 D2M8K2.t11381 = [0, 139860632777, 433623474297, 292001970898, 27545895622, 0, 0, 0] := by
  decide +kernel

theorem rows11382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11382 = true := by
  decide +kernel

theorem tot11382 : totK PD2M8K2 D2M8K2.t11382 = [0, 170419618972, 437720059473, 274547712257, 28078989698, 0, 0, 0] := by
  decide +kernel

theorem rows11383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11383 = true := by
  decide +kernel

theorem tot11383 : totK PD2M8K2 D2M8K2.t11383 = [0, 88102753241, 371954991923, 351541475119, 59468791708, 1107157161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
