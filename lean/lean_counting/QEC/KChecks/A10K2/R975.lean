import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3900 = true := by
  decide +kernel

theorem tot3900 : totK PA10K2 A10K2.t3900 = [0, 0, 327234200007, 1482121491638, 2114914717783, 931745612720, 74648740952, 0, 0, 0] := by
  decide +kernel

theorem rows3901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3901 = true := by
  decide +kernel

theorem tot3901 : totK PA10K2 A10K2.t3901 = [0, 0, 0, 602330931574, 2038288049239, 1889932082611, 394059991116, 12224107035, 0, 0] := by
  decide +kernel

theorem rows3902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3902 = true := by
  decide +kernel

theorem tot3902 : totK PA10K2 A10K2.t3902 = [0, 0, 317619887890, 1080766465879, 1566061305687, 1388225652683, 532119649544, 48886019071, 0, 0] := by
  decide +kernel

theorem rows3903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3903 = true := by
  decide +kernel

theorem tot3903 : totK PA10K2 A10K2.t3903 = [0, 0, 527099952449, 1941627853724, 1933778296462, 406610083890, 11647900320, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
