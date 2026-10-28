import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2108 = true := by
  decide +kernel

theorem tot2108 : totK PA10K2 A10K2.t2108 = [0, 165736271258, 1079879269928, 2085562959108, 1390765217805, 239836176890, 6281495166, 0, 0, 0] := by
  decide +kernel

theorem rows2109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2109 = true := by
  decide +kernel

theorem tot2109 : totK PA10K2 A10K2.t2109 = [0, 0, 583573700628, 2052899129102, 1934542197887, 438368770071, 12813073358, 0, 0, 0] := by
  decide +kernel

theorem rows2110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2110 = true := by
  decide +kernel

theorem tot2110 : totK PA10K2 A10K2.t2110 = [494676569003, 1526342412142, 1447139060822, 564928584235, 507358954491, 337104436601, 43287591117, 0, 0, 0] := by
  decide +kernel

theorem rows2111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2111 = true := by
  decide +kernel

theorem tot2111 : totK PA10K2 A10K2.t2111 = [66305273135, 892379810354, 1963652150360, 1423998581551, 361228191433, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
