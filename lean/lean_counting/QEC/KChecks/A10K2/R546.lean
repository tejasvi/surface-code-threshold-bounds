import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2184 = true := by
  decide +kernel

theorem tot2184 : totK PA10K2 A10K2.t2184 = [0, 432071612789, 1754704429607, 1934297968277, 518328656496, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2185 = true := by
  decide +kernel

theorem tot2185 : totK PA10K2 A10K2.t2185 = [364599868439, 1516551107400, 2077861611509, 930186014598, 91924354856, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2186 = true := by
  decide +kernel

theorem tot2186 : totK PA10K2 A10K2.t2186 = [192106291078, 1353945884746, 2208140132846, 930796356192, 79426192974, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2187 = true := by
  decide +kernel

theorem tot2187 : totK PA10K2 A10K2.t2187 = [495771531347, 1612300301130, 1780863091674, 865024053334, 178480763224, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
