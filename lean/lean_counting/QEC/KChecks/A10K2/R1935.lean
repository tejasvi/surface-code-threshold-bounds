import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7740 = true := by
  decide +kernel

theorem tot7740 : totK PA10K2 A10K2.t7740 = [0, 0, 0, 295617904848, 1515034167474, 2201952085179, 839505488351, 61631511384, 0, 0] := by
  decide +kernel

theorem rows7741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7741 = true := by
  decide +kernel

theorem tot7741 : totK PA10K2 A10K2.t7741 = [0, 0, 0, 0, 618526611147, 2045359197008, 1704586245418, 366370176044, 13576218110, 0] := by
  decide +kernel

theorem rows7742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7742 = true := by
  decide +kernel

theorem tot7742 : totK PA10K2 A10K2.t7742 = [0, 0, 0, 521968057584, 1853987469978, 1802399547670, 566424014726, 50246248178, 0, 0] := by
  decide +kernel

theorem rows7743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7743 = true := by
  decide +kernel

theorem tot7743 : totK PA10K2 A10K2.t7743 = [0, 0, 0, 266548699858, 1376946421231, 2269829334604, 940922678880, 64877900538, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
