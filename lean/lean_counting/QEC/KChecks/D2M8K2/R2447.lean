import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9788 = true := by
  decide +kernel

theorem tot9788 : totK PD2M8K2 D2M8K2.t9788 = [0, 0, 169221212327, 452798205409, 218548052587, 13452000861, 0, 0] := by
  decide +kernel

theorem rows9789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9789 = true := by
  decide +kernel

theorem tot9789 : totK PD2M8K2 D2M8K2.t9789 = [0, 0, 180373369495, 477614657321, 230536011327, 13115571915, 0, 0] := by
  decide +kernel

theorem rows9790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9790 = true := by
  decide +kernel

theorem tot9790 : totK PD2M8K2 D2M8K2.t9790 = [0, 0, 187538156863, 466252737550, 219191299102, 12319708528, 0, 0] := by
  decide +kernel

theorem rows9791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9791 = true := by
  decide +kernel

theorem tot9791 : totK PD2M8K2 D2M8K2.t9791 = [0, 0, 197588290690, 474132059812, 209803914334, 10178307621, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
