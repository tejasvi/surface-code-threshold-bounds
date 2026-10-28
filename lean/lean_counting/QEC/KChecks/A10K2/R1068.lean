import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4272 = true := by
  decide +kernel

theorem tot4272 : totK PA10K2 A10K2.t4272 = [0, 306984983602, 1530656996728, 2242261313825, 940864552992, 77226289175, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4273 = true := by
  decide +kernel

theorem tot4273 : totK PA10K2 A10K2.t4273 = [0, 206605305563, 967634420341, 1883081547489, 1544242168088, 358208156471, 12219140272, 0, 0, 0] := by
  decide +kernel

theorem rows4274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4274 = true := by
  decide +kernel

theorem tot4274 : totK PA10K2 A10K2.t4274 = [0, 475389465529, 1830619564806, 2057222460594, 620571796301, 33478709880, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4275 = true := by
  decide +kernel

theorem tot4275 : totK PA10K2 A10K2.t4275 = [0, 171341018104, 1143730606153, 2124036893734, 1321283336691, 225761236186, 6772895877, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
