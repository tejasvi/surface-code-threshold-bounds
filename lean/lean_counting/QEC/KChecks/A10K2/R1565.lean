import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6260 = true := by
  decide +kernel

theorem tot6260 : totK PA10K2 A10K2.t6260 = [0, 0, 534631070386, 2017664592331, 1979684116168, 435075108747, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows6261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6261 = true := by
  decide +kernel

theorem tot6261 : totK PA10K2 A10K2.t6261 = [0, 0, 629900304297, 1931544560853, 1801485173946, 585949031447, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows6262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6262 = true := by
  decide +kernel

theorem tot6262 : totK PA10K2 A10K2.t6262 = [0, 0, 476236816663, 1895173066133, 2004070392816, 496800224984, 25462924663, 0, 0, 0] := by
  decide +kernel

theorem rows6263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6263 = true := by
  decide +kernel

theorem tot6263 : totK PA10K2 A10K2.t6263 = [0, 0, 0, 666258452375, 2201436511345, 1666626093695, 273717982724, 6904928264, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
