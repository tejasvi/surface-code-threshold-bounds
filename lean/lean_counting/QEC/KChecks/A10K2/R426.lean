import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1704 = true := by
  decide +kernel

theorem tot1704 : totK PA10K2 A10K2.t1704 = [0, 0, 0, 459857692214, 1763467168702, 1843729577726, 481122934420, 25454126167, 0, 0] := by
  decide +kernel

theorem rows1705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1705 = true := by
  decide +kernel

theorem tot1705 : totK PA10K2 A10K2.t1705 = [0, 0, 0, 0, 813269021243, 2179436354830, 1320952295267, 174073996660, 0, 0] := by
  decide +kernel

theorem rows1706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1706 = true := by
  decide +kernel

theorem tot1706 : totK PA10K2 A10K2.t1706 = [0, 0, 582837918917, 1903340916741, 1699579409909, 412476515465, 119526147129, 91540553519, 6354482628, 0] := by
  decide +kernel

theorem rows1707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1707 = true := by
  decide +kernel

theorem tot1707 : totK PA10K2 A10K2.t1707 = [0, 0, 274878282901, 1442326722363, 2208550083287, 908064414776, 68064188553, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
