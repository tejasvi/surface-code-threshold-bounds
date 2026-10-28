import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6032 = true := by
  decide +kernel

theorem tot6032 : totK PA10K2 A10K2.t6032 = [0, 531361740084, 2015930644959, 2087120267658, 476746754285, 13814455608, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6033 = true := by
  decide +kernel

theorem tot6033 : totK PA10K2 A10K2.t6033 = [0, 633236995965, 1944197195677, 1808530557462, 584422858854, 49165311630, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6034 = true := by
  decide +kernel

theorem tot6034 : totK PA10K2 A10K2.t6034 = [0, 475637919915, 1769293513594, 1902552958951, 515160653112, 31222411477, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6035 = true := by
  decide +kernel

theorem tot6035 : totK PA10K2 A10K2.t6035 = [0, 44706116827, 846879579197, 2082010347914, 1485984453593, 358957085100, 25239774317, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
