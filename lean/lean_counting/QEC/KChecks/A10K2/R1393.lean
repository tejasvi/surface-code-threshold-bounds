import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5572 = true := by
  decide +kernel

theorem tot5572 : totK PA10K2 A10K2.t5572 = [0, 0, 633720618867, 2015487159977, 1808780441251, 511772896710, 35785166118, 0, 0, 0] := by
  decide +kernel

theorem rows5573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5573 = true := by
  decide +kernel

theorem tot5573 : totK PA10K2 A10K2.t5573 = [0, 0, 480010975637, 1779945728077, 1918127092261, 513423261079, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows5574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5574 = true := by
  decide +kernel

theorem tot5574 : totK PA10K2 A10K2.t5574 = [0, 0, 44706116827, 832030216877, 2023793949071, 1470236945501, 359204035189, 25239774317, 0, 0] := by
  decide +kernel

theorem rows5575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5575 = true := by
  decide +kernel

theorem tot5575 : totK PA10K2 A10K2.t5575 = [0, 0, 291230149053, 1172205632414, 1828402774452, 1144064950119, 190598885651, 5410721913, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
