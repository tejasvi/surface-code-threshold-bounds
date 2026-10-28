import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5496 = true := by
  decide +kernel

theorem tot5496 : totK PA10K2 A10K2.t5496 = [0, 0, 129432687776, 897047252284, 2017838615242, 1425247517750, 248488922356, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5497 = true := by
  decide +kernel

theorem tot5497 : totK PA10K2 A10K2.t5497 = [0, 0, 412764019084, 1724797213420, 2086230134452, 716709404414, 32873769222, 0, 0, 0] := by
  decide +kernel

theorem rows5498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5498 = true := by
  decide +kernel

theorem tot5498 : totK PA10K2 A10K2.t5498 = [0, 0, 172208915647, 945400605252, 1999876869977, 1545723305304, 284083433504, 6962742351, 0, 0] := by
  decide +kernel

theorem rows5499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5499 = true := by
  decide +kernel

theorem tot5499 : totK PA10K2 A10K2.t5499 = [0, 0, 478870728265, 1816409543322, 1926954825985, 530002602387, 32040661968, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
