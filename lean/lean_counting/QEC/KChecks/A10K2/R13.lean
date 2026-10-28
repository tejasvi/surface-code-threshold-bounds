import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows52 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t52 = true := by
  decide +kernel

theorem tot52 : totK PA10K2 A10K2.t52 = [0, 0, 623184743407, 2014471978765, 1817118954461, 454043148242, 28177825909, 0, 0, 0] := by
  decide +kernel

theorem rows53 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t53 = true := by
  decide +kernel

theorem tot53 : totK PA10K2 A10K2.t53 = [0, 0, 545524790434, 1828999068426, 1802806207523, 483693437538, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows54 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t54 = true := by
  decide +kernel

theorem tot54 : totK PA10K2 A10K2.t54 = [0, 0, 0, 832720736367, 2090918566179, 1454935508956, 358352176653, 25239774317, 0, 0] := by
  decide +kernel

theorem rows55 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t55 = true := by
  decide +kernel

theorem tot55 : totK PA10K2 A10K2.t55 = [0, 0, 287930791013, 1205021937526, 1801100524865, 1099157824882, 186084294959, 5365973533, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
