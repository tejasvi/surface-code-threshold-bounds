import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2408 = true := by
  decide +kernel

theorem tot2408 : totK PA10K2 A10K2.t2408 = [0, 0, 421128020257, 1767111284356, 2044515644893, 644236624423, 40353100526, 0, 0, 0] := by
  decide +kernel

theorem rows2409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2409 = true := by
  decide +kernel

theorem tot2409 : totK PA10K2 A10K2.t2409 = [0, 0, 0, 521015557847, 1878041419326, 1733377635648, 423183790501, 25565504801, 0, 0] := by
  decide +kernel

theorem rows2410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2410 = true := by
  decide +kernel

theorem tot2410 : totK PA10K2 A10K2.t2410 = [0, 0, 388125177966, 1520697935944, 1929654144553, 882023711760, 138122309559, 5517381808, 0, 0] := by
  decide +kernel

theorem rows2411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2411 = true := by
  decide +kernel

theorem tot2411 : totK PA10K2 A10K2.t2411 = [0, 0, 165933947252, 1325885248060, 2237513038641, 876455178615, 65953746422, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
