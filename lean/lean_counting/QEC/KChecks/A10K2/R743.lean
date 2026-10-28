import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2972 = true := by
  decide +kernel

theorem tot2972 : totK PA10K2 A10K2.t2972 = [0, 0, 0, 533731985815, 1924154644649, 1928284547577, 477824822196, 17686732349, 0, 0] := by
  decide +kernel

theorem rows2973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2973 = true := by
  decide +kernel

theorem tot2973 : totK PA10K2 A10K2.t2973 = [0, 552620952940, 1685270906194, 1508898807854, 516451890125, 337031596566, 227949815647, 37310410385, 0, 0] := by
  decide +kernel

theorem rows2974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2974 = true := by
  decide +kernel

theorem tot2974 : totK PA10K2 A10K2.t2974 = [0, 292098887399, 1535087049595, 2165068254555, 875326353204, 76460609536, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2975 = true := by
  decide +kernel

theorem tot2975 : totK PA10K2 A10K2.t2975 = [0, 0, 527150834538, 1833747784646, 1756120945598, 474517969233, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
