import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1488 = true := by
  decide +kernel

theorem tot1488 : totK PA10K2 A10K2.t1488 = [0, 0, 171987311886, 899431885075, 1921321360882, 1461927732080, 283388518400, 10760911071, 0, 0] := by
  decide +kernel

theorem rows1489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1489 = true := by
  decide +kernel

theorem tot1489 : totK PA10K2 A10K2.t1489 = [0, 0, 381054811864, 1731723460358, 2034629532645, 553608998837, 31688770306, 0, 0, 0] := by
  decide +kernel

theorem rows1490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1490 = true := by
  decide +kernel

theorem tot1490 : totK PA10K2 A10K2.t1490 = [0, 0, 293915060262, 1150689753616, 1841169394918, 1162021679079, 188826031564, 5976421810, 0, 0] := by
  decide +kernel

theorem rows1491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1491 = true := by
  decide +kernel

theorem tot1491 : totK PA10K2 A10K2.t1491 = [0, 0, 520346738218, 1934605636833, 2072209482817, 573584509229, 33503013619, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
