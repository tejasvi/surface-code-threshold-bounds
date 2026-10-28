import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows44 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t44 = true := by
  decide +kernel

theorem tot44 : totK PD2M8K2 D2M8K2.t44 = [42401345032, 230606751301, 425563173844, 173286609423, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows45 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t45 = true := by
  decide +kernel

theorem tot45 : totK PD2M8K2 D2M8K2.t45 = [186856363971, 452384948015, 239531507191, 21461100481, 0, 0, 0, 0] := by
  decide +kernel

theorem rows46 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t46 = true := by
  decide +kernel

theorem tot46 : totK PD2M8K2 D2M8K2.t46 = [176883465228, 460933397341, 235450562666, 17094477172, 0, 0, 0, 0] := by
  decide +kernel

theorem rows47 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t47 = true := by
  decide +kernel

theorem tot47 : totK PD2M8K2 D2M8K2.t47 = [0, 306145811691, 488623008670, 92586679608, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
