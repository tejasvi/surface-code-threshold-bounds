import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t480 = true := by
  decide +kernel

theorem tot480 : totK PA10K2 A10K2.t480 = [0, 460461657366, 1665835060634, 1918404174052, 702441523664, 65037766653, 0, 0, 0, 0] := by
  decide +kernel

theorem rows481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t481 = true := by
  decide +kernel

theorem tot481 : totK PA10K2 A10K2.t481 = [0, 285441611041, 1494027938474, 2085657138384, 739615649683, 44621684296, 0, 0, 0, 0] := by
  decide +kernel

theorem rows482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t482 = true := by
  decide +kernel

theorem tot482 : totK PA10K2 A10K2.t482 = [0, 297225354374, 1192659207796, 1894897798357, 1113706682478, 180624484557, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t483 = true := by
  decide +kernel

theorem tot483 : totK PA10K2 A10K2.t483 = [110684666881, 521544928709, 1494982174170, 2029308987514, 870393588225, 76273455778, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
