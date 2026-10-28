import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2440 = true := by
  decide +kernel

theorem tot2440 : totK PA10K2 A10K2.t2440 = [0, 110180265545, 881695544153, 1992819685492, 1422198059208, 342971015804, 25239774317, 0, 0, 0] := by
  decide +kernel

theorem rows2441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2441 = true := by
  decide +kernel

theorem tot2441 : totK PA10K2 A10K2.t2441 = [0, 252055886529, 1118526769997, 1888929772581, 1200226707363, 206831905036, 5410721913, 0, 0, 0] := by
  decide +kernel

theorem rows2442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2442 = true := by
  decide +kernel

theorem tot2442 : totK PA10K2 A10K2.t2442 = [0, 491424974411, 1801827817798, 1869132665156, 513050364014, 31608797364, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2443 = true := by
  decide +kernel

theorem tot2443 : totK PA10K2 A10K2.t2443 = [0, 0, 1016459491855, 2427716732791, 1107425569088, 77639916951, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
