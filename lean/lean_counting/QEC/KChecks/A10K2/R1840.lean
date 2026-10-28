import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7360 = true := by
  decide +kernel

theorem tot7360 : totK PA10K2 A10K2.t7360 = [0, 0, 0, 178971957751, 1145161521389, 2107777788870, 1262322356335, 215863098285, 6853348008, 0] := by
  decide +kernel

theorem rows7361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7361 = true := by
  decide +kernel

theorem tot7361 : totK PA10K2 A10K2.t7361 = [0, 0, 176847655326, 382331208921, 749044891352, 1763900059361, 1589372288261, 416951685699, 28650013862, 0] := by
  decide +kernel

theorem rows7362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7362 = true := by
  decide +kernel

theorem tot7362 : totK PA10K2 A10K2.t7362 = [0, 0, 445830515697, 1772287592553, 1980536218816, 540030451317, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows7363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7363 = true := by
  decide +kernel

theorem tot7363 : totK PA10K2 A10K2.t7363 = [0, 0, 216114254040, 1214211045671, 2054502325041, 1188066301956, 203628431834, 14945844243, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
