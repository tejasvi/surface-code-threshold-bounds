import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3516 = true := by
  decide +kernel

theorem tot3516 : totK PA10K2 A10K2.t3516 = [0, 0, 0, 332818647249, 1641267047940, 2162589842157, 714706833701, 40441619481, 0, 0] := by
  decide +kernel

theorem rows3517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3517 = true := by
  decide +kernel

theorem tot3517 : totK PA10K2 A10K2.t3517 = [0, 0, 0, 0, 511346882100, 1846201252033, 1790130703373, 447087878254, 31003444686, 0] := by
  decide +kernel

theorem rows3518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3518 = true := by
  decide +kernel

theorem tot3518 : totK PA10K2 A10K2.t3518 = [0, 0, 0, 512308510744, 1722804407711, 1766055899203, 528371909984, 38022986322, 0, 0] := by
  decide +kernel

theorem rows3519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3519 = true := by
  decide +kernel

theorem tot3519 : totK PA10K2 A10K2.t3519 = [0, 0, 0, 308174862979, 1561386765855, 2106068159915, 676219620647, 29553209918, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
