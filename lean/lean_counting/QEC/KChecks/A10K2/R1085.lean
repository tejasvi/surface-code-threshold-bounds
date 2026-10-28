import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4340 = true := by
  decide +kernel

theorem tot4340 : totK PA10K2 A10K2.t4340 = [0, 0, 0, 621338303964, 2119760243273, 1837456757721, 394022091489, 16166423876, 0, 0] := by
  decide +kernel

theorem rows4341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4341 = true := by
  decide +kernel

theorem tot4341 : totK PA10K2 A10K2.t4341 = [0, 0, 510744180543, 1597883971903, 1677231245251, 781865152226, 221033202262, 22228207860, 0, 0] := by
  decide +kernel

theorem rows4342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4342 = true := by
  decide +kernel

theorem tot4342 : totK PA10K2 A10K2.t4342 = [0, 0, 282182245847, 1530740818055, 2175784206790, 812978264209, 61713325141, 0, 0, 0] := by
  decide +kernel

theorem rows4343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4343 = true := by
  decide +kernel

theorem tot4343 : totK PA10K2 A10K2.t4343 = [0, 0, 0, 506715899615, 1839678238312, 1802156157620, 485089514470, 30831673886, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
