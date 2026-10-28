import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6360 = true := by
  decide +kernel

theorem tot6360 : totK PA10K2 A10K2.t6360 = [0, 186831734348, 993222941684, 1950425245508, 1273091057790, 201606526995, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows6361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6361 = true := by
  decide +kernel

theorem tot6361 : totK PA10K2 A10K2.t6361 = [0, 405971821304, 1685338497119, 2201190031482, 790624349356, 44333731153, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6362 = true := by
  decide +kernel

theorem tot6362 : totK PA10K2 A10K2.t6362 = [561156172308, 1897247409065, 1780670408956, 487428769351, 115205925761, 31937898706, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6363 = true := by
  decide +kernel

theorem tot6363 : totK PA10K2 A10K2.t6363 = [0, 691572700432, 2067992323187, 1581284766648, 367057885610, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
