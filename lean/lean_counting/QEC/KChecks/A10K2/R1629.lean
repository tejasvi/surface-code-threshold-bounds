import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6516 = true := by
  decide +kernel

theorem tot6516 : totK PA10K2 A10K2.t6516 = [0, 0, 45277493360, 904234569311, 2200400473786, 1575576479595, 262663623850, 7047025452, 0, 0] := by
  decide +kernel

theorem rows6517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6517 = true := by
  decide +kernel

theorem tot6517 : totK PA10K2 A10K2.t6517 = [0, 0, 343933301626, 1534472120637, 2119571062757, 875523393135, 60822888598, 0, 0, 0] := by
  decide +kernel

theorem rows6518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6518 = true := by
  decide +kernel

theorem tot6518 : totK PA10K2 A10K2.t6518 = [0, 0, 501550152162, 1870373711679, 2036554801330, 559352736332, 18355813117, 0, 0, 0] := by
  decide +kernel

theorem rows6519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6519 = true := by
  decide +kernel

theorem tot6519 : totK PA10K2 A10K2.t6519 = [0, 0, 0, 675296630147, 2184570823866, 1856776900291, 332308940619, 6157148557, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
