import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t428 = true := by
  decide +kernel

theorem tot428 : totK PA10K2 A10K2.t428 = [276704929378, 1435484433696, 2186111647605, 1075663667553, 115851531222, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t429 = true := by
  decide +kernel

theorem tot429 : totK PA10K2 A10K2.t429 = [0, 507866417312, 1929948714062, 2125913302149, 572752833126, 19708922258, 0, 0, 0, 0] := by
  decide +kernel

theorem rows430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t430 = true := by
  decide +kernel

theorem tot430 : totK PA10K2 A10K2.t430 = [0, 489137510380, 1701599355094, 1947944345781, 732550469795, 68815120782, 0, 0, 0, 0] := by
  decide +kernel

theorem rows431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t431 = true := by
  decide +kernel

theorem tot431 : totK PA10K2 A10K2.t431 = [0, 319196630146, 1586508737935, 2176506817132, 869799507919, 75547870091, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
