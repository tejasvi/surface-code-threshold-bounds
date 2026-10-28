import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1548 = true := by
  decide +kernel

theorem tot1548 : totK PA10K2 A10K2.t1548 = [0, 0, 534745239593, 1984810088799, 1842376791767, 476701846063, 30810868011, 0, 0, 0] := by
  decide +kernel

theorem rows1549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1549 = true := by
  decide +kernel

theorem tot1549 : totK PA10K2 A10K2.t1549 = [0, 480589018088, 1789805160588, 2042727021529, 757605886729, 70355432620, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1550 = true := by
  decide +kernel

theorem tot1550 : totK PA10K2 A10K2.t1550 = [0, 316669361890, 1531752656264, 2228890947855, 922766850771, 76896540718, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1551 = true := by
  decide +kernel

theorem tot1551 : totK PA10K2 A10K2.t1551 = [0, 0, 507866417312, 2002677870903, 2133671648299, 481909022752, 12746179907, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
