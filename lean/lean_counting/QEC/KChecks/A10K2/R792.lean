import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3168 = true := by
  decide +kernel

theorem tot3168 : totK PA10K2 A10K2.t3168 = [0, 0, 0, 381257964670, 1540350612581, 2027215414283, 761571768683, 60880363483, 0, 0] := by
  decide +kernel

theorem rows3169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3169 = true := by
  decide +kernel

theorem tot3169 : totK PA10K2 A10K2.t3169 = [0, 0, 0, 338939569013, 1568074621708, 2119947250462, 786509949775, 62156421873, 0, 0] := by
  decide +kernel

theorem rows3170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3170 = true := by
  decide +kernel

theorem tot3170 : totK PA10K2 A10K2.t3170 = [0, 0, 0, 293226264709, 1199765663729, 1938846569171, 1195579434004, 208668881916, 6318667960, 0] := by
  decide +kernel

theorem rows3171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3171 = true := by
  decide +kernel

theorem tot3171 : totK PA10K2 A10K2.t3171 = [0, 0, 0, 465176945695, 1814348697232, 2065242270867, 580263272060, 24692530783, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
