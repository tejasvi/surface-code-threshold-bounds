import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11288 = true := by
  decide +kernel

theorem tot11288 : totK PD2M8K2 D2M8K2.t11288 = [0, 168640569889, 453353851096, 269802516525, 25478622528, 0, 0, 0] := by
  decide +kernel

theorem rows11289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11289 = true := by
  decide +kernel

theorem tot11289 : totK PD2M8K2 D2M8K2.t11289 = [85430600343, 268878721348, 337988545601, 184050051328, 16138726361, 0, 0, 0] := by
  decide +kernel

theorem rows11290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11290 = true := by
  decide +kernel

theorem tot11290 : totK PD2M8K2 D2M8K2.t11290 = [174551282529, 475162692039, 236130765240, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11291 = true := by
  decide +kernel

theorem tot11291 : totK PD2M8K2 D2M8K2.t11291 = [62216791299, 330241150420, 409303044905, 94540620190, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
