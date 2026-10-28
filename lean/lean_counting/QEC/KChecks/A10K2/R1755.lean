import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7020 = true := by
  decide +kernel

theorem tot7020 : totK PA10K2 A10K2.t7020 = [0, 444538933688, 1734835054909, 1949149793817, 633706007444, 58916283068, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7021 = true := by
  decide +kernel

theorem tot7021 : totK PA10K2 A10K2.t7021 = [0, 397842162880, 1573492728191, 2038401808943, 856037176889, 76936840205, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7022 = true := by
  decide +kernel

theorem tot7022 : totK PA10K2 A10K2.t7022 = [0, 434930329847, 1764746462464, 2153903274333, 700878917106, 39446437729, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7023 = true := by
  decide +kernel

theorem tot7023 : totK PA10K2 A10K2.t7023 = [0, 0, 554886651303, 2039179281306, 1999955650689, 462901005056, 13814447077, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
