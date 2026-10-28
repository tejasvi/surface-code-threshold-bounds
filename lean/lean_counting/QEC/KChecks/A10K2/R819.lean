import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3276 = true := by
  decide +kernel

theorem tot3276 : totK PA10K2 A10K2.t3276 = [0, 0, 0, 963284681280, 2445651487317, 1158297154375, 83755589175, 0, 0, 0] := by
  decide +kernel

theorem rows3277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3277 = true := by
  decide +kernel

theorem tot3277 : totK PA10K2 A10K2.t3277 = [0, 0, 505556307028, 1616281886856, 1720727797818, 857367637523, 161460762868, 6121173289, 0, 0] := by
  decide +kernel

theorem rows3278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3278 = true := by
  decide +kernel

theorem tot3278 : totK PA10K2 A10K2.t3278 = [0, 336102756353, 1114589462949, 1541485822512, 1293382876268, 534231572874, 42607502534, 0, 0, 0] := by
  decide +kernel

theorem rows3279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3279 = true := by
  decide +kernel

theorem tot3279 : totK PA10K2 A10K2.t3279 = [0, 246696754021, 1303993309153, 1948470374239, 947723401352, 185000989313, 20070762815, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
