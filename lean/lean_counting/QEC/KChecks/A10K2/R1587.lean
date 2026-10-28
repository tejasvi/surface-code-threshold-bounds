import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6348 = true := by
  decide +kernel

theorem tot6348 : totK PA10K2 A10K2.t6348 = [335061730634, 1576797555139, 2107769543351, 811304235239, 70805483902, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6349 = true := by
  decide +kernel

theorem tot6349 : totK PA10K2 A10K2.t6349 = [0, 464767173811, 1810932934610, 1909966607447, 503905259535, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6350 = true := by
  decide +kernel

theorem tot6350 : totK PA10K2 A10K2.t6350 = [461452330429, 1649725353428, 1878480023817, 771093605440, 83765364636, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6351 = true := by
  decide +kernel

theorem tot6351 : totK PA10K2 A10K2.t6351 = [289345254879, 1480789859000, 2124552886571, 773284264579, 53383554103, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
