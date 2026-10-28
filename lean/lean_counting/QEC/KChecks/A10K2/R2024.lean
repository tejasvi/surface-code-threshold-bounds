import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8096 = true := by
  decide +kernel

theorem tot8096 : totK PA10K2 A10K2.t8096 = [0, 0, 0, 0, 678636832212, 2177599934781, 1831824306522, 362137274207, 12677188408, 0] := by
  decide +kernel

theorem rows8097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8097 = true := by
  decide +kernel

theorem tot8097 : totK PA10K2 A10K2.t8097 = [0, 0, 0, 442678411980, 1451407628663, 1633348145684, 1052371017505, 363624117887, 31276155898, 0] := by
  decide +kernel

theorem rows8098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8098 = true := by
  decide +kernel

theorem tot8098 : totK PA10K2 A10K2.t8098 = [0, 0, 0, 588224598170, 1976343785999, 1862809964035, 482251678642, 19138079192, 0, 0] := by
  decide +kernel

theorem rows8099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8099 = true := by
  decide +kernel

theorem tot8099 : totK PA10K2 A10K2.t8099 = [0, 0, 0, 562410119031, 2013387116432, 1780733975982, 415851826927, 18830549753, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
