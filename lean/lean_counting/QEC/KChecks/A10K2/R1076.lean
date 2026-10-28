import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4304 = true := by
  decide +kernel

theorem tot4304 : totK PA10K2 A10K2.t4304 = [0, 267823935912, 1515557657379, 2176143548124, 744503014756, 44706179341, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4305 = true := by
  decide +kernel

theorem tot4305 : totK PA10K2 A10K2.t4305 = [0, 367584626119, 1268834557401, 1792942174667, 1097145619755, 189184544053, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows4306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4306 = true := by
  decide +kernel

theorem tot4306 : totK PA10K2 A10K2.t4306 = [0, 421076849351, 1737675074896, 1901363295310, 510930675099, 32442760180, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4307 = true := by
  decide +kernel

theorem tot4307 : totK PA10K2 A10K2.t4307 = [0, 0, 744156912725, 2243691794393, 1442735073826, 162552891131, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
