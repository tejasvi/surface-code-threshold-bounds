import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1192 = true := by
  decide +kernel

theorem tot1192 : totK PA10K2 A10K2.t1192 = [0, 0, 581035684948, 1999793000935, 1989895605932, 510028479479, 25574931378, 0, 0, 0] := by
  decide +kernel

theorem rows1193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1193 = true := by
  decide +kernel

theorem tot1193 : totK PA10K2 A10K2.t1193 = [0, 0, 0, 781279015241, 2260885963047, 1689456980363, 282967859575, 6853348008, 0, 0] := by
  decide +kernel

theorem rows1194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1194 = true := by
  decide +kernel

theorem tot1194 : totK PA10K2 A10K2.t1194 = [0, 0, 0, 682750230217, 2074635262658, 1723849799354, 439326946310, 28177825909, 0, 0] := by
  decide +kernel

theorem rows1195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1195 = true := by
  decide +kernel

theorem tot1195 : totK PA10K2 A10K2.t1195 = [0, 0, 0, 448634485212, 1769541447284, 1952403260008, 513093673129, 31222411477, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
