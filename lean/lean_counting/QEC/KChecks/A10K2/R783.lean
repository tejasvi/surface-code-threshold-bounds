import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3132 = true := by
  decide +kernel

theorem tot3132 : totK PA10K2 A10K2.t3132 = [0, 0, 277872468536, 1316478711291, 2001666853062, 1138485391920, 194718966749, 7047025452, 0, 0] := by
  decide +kernel

theorem rows3133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3133 = true := by
  decide +kernel

theorem tot3133 : totK PA10K2 A10K2.t3133 = [0, 0, 614163989865, 1985636297951, 1864197344777, 473600554835, 11925330097, 0, 0, 0] := by
  decide +kernel

theorem rows3134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3134 = true := by
  decide +kernel

theorem tot3134 : totK PA10K2 A10K2.t3134 = [0, 0, 0, 817731544681, 2251143883043, 1601116366132, 256641719044, 6066958478, 0, 0] := by
  decide +kernel

theorem rows3135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3135 = true := by
  decide +kernel

theorem tot3135 : totK PA10K2 A10K2.t3135 = [0, 0, 0, 496006671583, 1908506076488, 2002053376835, 504266990138, 17732757243, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
