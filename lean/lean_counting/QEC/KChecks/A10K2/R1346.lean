import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5384 = true := by
  decide +kernel

theorem tot5384 : totK PA10K2 A10K2.t5384 = [0, 0, 183530997116, 1011152891972, 2038799220844, 1237660674081, 186160117918, 6121173289, 0, 0] := by
  decide +kernel

theorem rows5385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5385 = true := by
  decide +kernel

theorem tot5385 : totK PA10K2 A10K2.t5385 = [0, 0, 557658487079, 1931400055609, 1870627841515, 489283706958, 25852139541, 0, 0, 0] := by
  decide +kernel

theorem rows5386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5386 = true := by
  decide +kernel

theorem tot5386 : totK PA10K2 A10K2.t5386 = [0, 468537272203, 1441172957973, 1454508691333, 958818695355, 437978844523, 42699564825, 0, 0, 0] := by
  decide +kernel

theorem rows5387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5387 = true := by
  decide +kernel

theorem tot5387 : totK PA10K2 A10K2.t5387 = [0, 0, 704097017616, 2086192466832, 1493991734970, 328756617435, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
