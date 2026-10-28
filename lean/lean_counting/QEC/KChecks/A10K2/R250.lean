import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1000 = true := by
  decide +kernel

theorem tot1000 : totK PA10K2 A10K2.t1000 = [0, 0, 558204839642, 1828982315351, 1875549651707, 680348269749, 57873648507, 0, 0, 0] := by
  decide +kernel

theorem rows1001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1001 = true := by
  decide +kernel

theorem tot1001 : totK PA10K2 A10K2.t1001 = [0, 0, 0, 798066900110, 2298978929865, 1661614863394, 241799411125, 6860445330, 0, 0] := by
  decide +kernel

theorem rows1002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1002 = true := by
  decide +kernel

theorem tot1002 : totK PA10K2 A10K2.t1002 = [0, 0, 534468218564, 1862234890485, 1928170424909, 620689575593, 56285200856, 0, 0, 0] := by
  decide +kernel

theorem rows1003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1003 = true := by
  decide +kernel

theorem tot1003 : totK PA10K2 A10K2.t1003 = [0, 0, 327737319032, 1518704818958, 2153057864428, 854999691109, 63206717419, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
