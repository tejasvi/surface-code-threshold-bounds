import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7548 = true := by
  decide +kernel

theorem tot7548 : totK PA10K2 A10K2.t7548 = [0, 0, 0, 500060686216, 1826815651467, 1853168609408, 447527659369, 31690778550, 0, 0] := by
  decide +kernel

theorem rows7549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7549 = true := by
  decide +kernel

theorem tot7549 : totK PA10K2 A10K2.t7549 = [0, 0, 0, 594710831977, 2095056437074, 1749240159360, 280400475027, 6354609102, 0, 0] := by
  decide +kernel

theorem rows7550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7550 = true := by
  decide +kernel

theorem tot7550 : totK PA10K2 A10K2.t7550 = [0, 0, 0, 570545335347, 1855544793951, 1720006602320, 430768320286, 30874154442, 0, 0] := by
  decide +kernel

theorem rows7551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7551 = true := by
  decide +kernel

theorem tot7551 : totK PA10K2 A10K2.t7551 = [0, 0, 0, 0, 999257118274, 2382675061782, 1047019663121, 82048001207, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
