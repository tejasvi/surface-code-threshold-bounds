import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6452 = true := by
  decide +kernel

theorem tot6452 : totK PA10K2 A10K2.t6452 = [0, 201614550383, 1284787686704, 2184082370136, 917566782662, 66002183783, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6453 = true := by
  decide +kernel

theorem tot6453 : totK PA10K2 A10K2.t6453 = [0, 501990865574, 1666705237823, 1814693629776, 849385306452, 163719576738, 6239673734, 0, 0, 0] := by
  decide +kernel

theorem rows6454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6454 = true := by
  decide +kernel

theorem tot6454 : totK PA10K2 A10K2.t6454 = [0, 319364795913, 1561475386778, 2246698163600, 924764486178, 73823416362, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6455 = true := by
  decide +kernel

theorem tot6455 : totK PA10K2 A10K2.t6455 = [0, 0, 567922412531, 2038657485357, 2018386172155, 452728349072, 13242594235, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
