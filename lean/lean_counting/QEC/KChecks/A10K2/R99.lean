import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t396 = true := by
  decide +kernel

theorem tot396 : totK PA10K2 A10K2.t396 = [437049832295, 1800093854615, 1985970373592, 518144934515, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t397 = true := by
  decide +kernel

theorem tot397 : totK PA10K2 A10K2.t397 = [274878282901, 1330566550300, 2138496410460, 1136286245038, 114433982405, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t398 = true := by
  decide +kernel

theorem tot398 : totK PA10K2 A10K2.t398 = [0, 535703001359, 1894654372108, 1786381559971, 457853093001, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t399 = true := by
  decide +kernel

theorem tot399 : totK PA10K2 A10K2.t399 = [484363826382, 1665595181162, 1850254358110, 676874600601, 78528389794, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
