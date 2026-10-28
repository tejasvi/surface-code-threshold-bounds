import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3992 = true := by
  decide +kernel

theorem tot3992 : totK PA10K2 A10K2.t3992 = [0, 0, 0, 681414718774, 2111060049258, 1733447641501, 411069168153, 25660650750, 0, 0] := by
  decide +kernel

theorem rows3993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3993 = true := by
  decide +kernel

theorem tot3993 : totK PA10K2 A10K2.t3993 = [0, 0, 246819733237, 1152219016382, 1957274940389, 1269109804856, 211556299429, 5624717336, 0, 0] := by
  decide +kernel

theorem rows3994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3994 = true := by
  decide +kernel

theorem tot3994 : totK PA10K2 A10K2.t3994 = [0, 0, 615112866711, 2035238746356, 1884866710307, 477933706741, 25536903856, 0, 0, 0] := by
  decide +kernel

theorem rows3995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3995 = true := by
  decide +kernel

theorem tot3995 : totK PA10K2 A10K2.t3995 = [0, 0, 0, 764700987738, 2225474687236, 1649215218759, 267371741743, 6281495166, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
