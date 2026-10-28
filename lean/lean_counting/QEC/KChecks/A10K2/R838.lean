import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3352 = true := by
  decide +kernel

theorem tot3352 : totK PA10K2 A10K2.t3352 = [0, 0, 0, 763761551482, 2230245663684, 1644663626173, 277379288745, 7047025452, 0, 0] := by
  decide +kernel

theorem rows3353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3353 = true := by
  decide +kernel

theorem tot3353 : totK PA10K2 A10K2.t3353 = [0, 0, 542492176839, 1777402633985, 1829613860247, 693557249232, 62302928520, 0, 0, 0] := by
  decide +kernel

theorem rows3354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3354 = true := by
  decide +kernel

theorem tot3354 : totK PA10K2 A10K2.t3354 = [0, 0, 330021797788, 1559912989645, 2207428409858, 849912027720, 49003888095, 0, 0, 0] := by
  decide +kernel

theorem rows3355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3355 = true := by
  decide +kernel

theorem tot3355 : totK PA10K2 A10K2.t3355 = [0, 0, 0, 589167308627, 1979387786199, 1874405975812, 409643572889, 12224107035, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
