import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16332 = true := by
  decide +kernel

theorem tot16332 : totK PD2M8K2 D2M8K2.t16332 = [0, 0, 0, 259696637805, 506146623055, 125814413186, 1268739303, 0] := by
  decide +kernel

theorem rows16333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16333 = true := by
  decide +kernel

theorem tot16333 : totK PD2M8K2 D2M8K2.t16333 = [0, 0, 0, 181019388762, 471349836949, 219276056657, 11099557010, 0] := by
  decide +kernel

theorem rows16334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16334 = true := by
  decide +kernel

theorem tot16334 : totK PD2M8K2 D2M8K2.t16334 = [0, 0, 0, 195313166270, 473228677182, 188681905241, 12126792705, 0] := by
  decide +kernel

theorem rows16335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16335 = true := by
  decide +kernel

theorem tot16335 : totK PD2M8K2 D2M8K2.t16335 = [0, 0, 0, 199738912898, 486065705632, 166232956596, 6446962872, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
