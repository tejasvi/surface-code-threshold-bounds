import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t944 = true := by
  decide +kernel

theorem tot944 : totK PD2M8K2 D2M8K2.t944 = [0, 0, 172663715731, 449585867906, 248400443229, 25191558099, 0, 0] := by
  decide +kernel

theorem rows945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t945 = true := by
  decide +kernel

theorem tot945 : totK PD2M8K2 D2M8K2.t945 = [0, 0, 213638677403, 491238826495, 179437935884, 5206224793, 0, 0] := by
  decide +kernel

theorem rows946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t946 = true := by
  decide +kernel

theorem tot946 : totK PD2M8K2 D2M8K2.t946 = [0, 155604478123, 370052385652, 262054297297, 104228241566, 6524090962, 0, 0] := by
  decide +kernel

theorem rows947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t947 = true := by
  decide +kernel

theorem tot947 : totK PD2M8K2 D2M8K2.t947 = [0, 176905722824, 459916704639, 240015762330, 15210095333, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
