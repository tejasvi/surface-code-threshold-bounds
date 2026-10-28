import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6344 = true := by
  decide +kernel

theorem tot6344 : totK PA10K2 A10K2.t6344 = [0, 490045717571, 1826224459215, 2042159460298, 614636036642, 37421449257, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6345 = true := by
  decide +kernel

theorem tot6345 : totK PA10K2 A10K2.t6345 = [0, 122360162702, 1045684848970, 2166969829239, 1439347899042, 246143359286, 6281495166, 0, 0, 0] := by
  decide +kernel

theorem rows6346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6346 = true := by
  decide +kernel

theorem tot6346 : totK PA10K2 A10K2.t6346 = [0, 0, 499150688341, 1955719184919, 2041577916840, 518159588342, 18776452511, 0, 0, 0] := by
  decide +kernel

theorem rows6347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6347 = true := by
  decide +kernel

theorem tot6347 : totK PA10K2 A10K2.t6347 = [506965099532, 1612968115968, 1547409761951, 547721358714, 380331255891, 257313618330, 37324211964, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
