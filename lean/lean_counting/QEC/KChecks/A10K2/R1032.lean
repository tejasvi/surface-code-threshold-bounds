import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4128 = true := by
  decide +kernel

theorem tot4128 : totK PA10K2 A10K2.t4128 = [0, 513572489737, 1802485013906, 1824877495791, 520582670419, 31614405859, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4129 = true := by
  decide +kernel

theorem tot4129 : totK PA10K2 A10K2.t4129 = [0, 0, 1043991719735, 2397643789053, 1085294008371, 77248038420, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4130 = true := by
  decide +kernel

theorem tot4130 : totK PA10K2 A10K2.t4130 = [0, 439577309324, 1485618464433, 1824066151445, 938163040662, 154481227852, 5705019915, 0, 0, 0] := by
  decide +kernel

theorem rows4131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4131 = true := by
  decide +kernel

theorem tot4131 : totK PA10K2 A10K2.t4131 = [0, 301022667366, 1462441925618, 2109967605044, 897967334272, 75767311358, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
