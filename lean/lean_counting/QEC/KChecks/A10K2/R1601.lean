import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6404 = true := by
  decide +kernel

theorem tot6404 : totK PA10K2 A10K2.t6404 = [0, 284564927155, 1335032964683, 1999499493206, 1091257812753, 178282913760, 5410721913, 0, 0, 0] := by
  decide +kernel

theorem rows6405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6405 = true := by
  decide +kernel

theorem tot6405 : totK PA10K2 A10K2.t6405 = [0, 541147644138, 1965514790272, 2129253576966, 595868936713, 19876255495, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6406 = true := by
  decide +kernel

theorem tot6406 : totK PA10K2 A10K2.t6406 = [542450728586, 1668437325803, 1617391578819, 723775195736, 258894648784, 37674914273, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6407 = true := by
  decide +kernel

theorem tot6407 : totK PA10K2 A10K2.t6407 = [296440474885, 1535961658085, 2171634694542, 886385851480, 78220832122, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
