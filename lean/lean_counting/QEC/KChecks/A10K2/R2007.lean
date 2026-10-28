import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8028 = true := by
  decide +kernel

theorem tot8028 : totK PA10K2 A10K2.t8028 = [0, 0, 0, 294672725543, 1528486721521, 2080655577868, 724751596710, 44939819202, 0, 0] := by
  decide +kernel

theorem rows8029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8029 = true := by
  decide +kernel

theorem tot8029 : totK PA10K2 A10K2.t8029 = [0, 0, 0, 488352769765, 1774271508188, 1972239082252, 619903081366, 41821164633, 0, 0] := by
  decide +kernel

theorem rows8030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8030 = true := by
  decide +kernel

theorem tot8030 : totK PA10K2 A10K2.t8030 = [0, 0, 0, 314008318368, 1526060905907, 2192608112560, 933992140434, 76123644080, 0, 0] := by
  decide +kernel

theorem rows8031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8031 = true := by
  decide +kernel

theorem tot8031 : totK PA10K2 A10K2.t8031 = [0, 0, 0, 0, 632328956609, 2136513468677, 1937685858448, 346008439559, 6853348008, 0] := by
  decide +kernel

end QECKChecks.A10K2
