import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8152 = true := by
  decide +kernel

theorem tot8152 : totK PA10K2 A10K2.t8152 = [0, 0, 0, 496219520495, 1851429702767, 1962725785917, 520333247050, 18637293326, 0, 0] := by
  decide +kernel

theorem rows8153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8153 = true := by
  decide +kernel

theorem tot8153 : totK PA10K2 A10K2.t8153 = [0, 0, 0, 0, 678657787139, 2046938459661, 1681378375488, 320237769092, 12477124820, 0] := by
  decide +kernel

theorem rows8154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8154 = true := by
  decide +kernel

theorem tot8154 : totK PA10K2 A10K2.t8154 = [0, 0, 0, 310892274646, 1321181888425, 2101226512770, 1064068406472, 99071138215, 0, 0] := by
  decide +kernel

theorem rows8155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8155 = true := by
  decide +kernel

theorem tot8155 : totK PA10K2 A10K2.t8155 = [0, 0, 0, 420070776803, 1674127850682, 1980793516591, 674834634601, 37734873630, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
