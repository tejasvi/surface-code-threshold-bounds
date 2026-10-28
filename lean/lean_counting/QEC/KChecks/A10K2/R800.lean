import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3200 = true := by
  decide +kernel

theorem tot3200 : totK PA10K2 A10K2.t3200 = [0, 0, 601643106228, 1978642255682, 1702734001717, 364991485241, 11740596405, 0, 0, 0] := by
  decide +kernel

theorem rows3201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3201 = true := by
  decide +kernel

theorem tot3201 : totK PA10K2 A10K2.t3201 = [0, 0, 434536082435, 1750099487609, 2031710068015, 573929329885, 32470943963, 0, 0, 0] := by
  decide +kernel

theorem rows3202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3202 = true := by
  decide +kernel

theorem tot3202 : totK PA10K2 A10K2.t3202 = [0, 0, 518324616761, 1865666520693, 1828664448371, 452864211396, 17606126119, 0, 0, 0] := by
  decide +kernel

theorem rows3203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3203 = true := by
  decide +kernel

theorem tot3203 : totK PA10K2 A10K2.t3203 = [0, 0, 296309078817, 1550419750738, 2091007107585, 612519957920, 37324864939, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
