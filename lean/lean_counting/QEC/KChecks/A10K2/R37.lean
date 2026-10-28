import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t148 = true := by
  decide +kernel

theorem tot148 : totK PA10K2 A10K2.t148 = [319203061299, 1467982195471, 2174061829403, 1030672386490, 89637159001, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t149 = true := by
  decide +kernel

theorem tot149 : totK PA10K2 A10K2.t149 = [0, 518300834245, 1999128777377, 2104711233724, 481242248398, 13814455608, 0, 0, 0, 0] := by
  decide +kernel

theorem rows150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t150 = true := by
  decide +kernel

theorem tot150 : totK PA10K2 A10K2.t150 = [0, 421501596606, 1575578103702, 2005177311829, 831145898903, 74832387466, 0, 0, 0, 0] := by
  decide +kernel

theorem rows151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t151 = true := by
  decide +kernel

theorem tot151 : totK PA10K2 A10K2.t151 = [0, 422195114974, 1791125386688, 2038478551490, 584219748459, 34548791282, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
