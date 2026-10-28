import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2532 = true := by
  decide +kernel

theorem tot2532 : totK PD2M8K2 D2M8K2.t2532 = [0, 223865714898, 495019354087, 173618679561, 4812449420, 0, 0, 0] := by
  decide +kernel

theorem rows2533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2533 = true := by
  decide +kernel

theorem tot2533 : totK PD2M8K2 D2M8K2.t2533 = [0, 192393851955, 459997230063, 214769375943, 17064697274, 0, 0, 0] := by
  decide +kernel

theorem rows2534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2534 = true := by
  decide +kernel

theorem tot2534 : totK PD2M8K2 D2M8K2.t2534 = [0, 171699545304, 470279720034, 226849133088, 11015599377, 0, 0, 0] := by
  decide +kernel

theorem rows2535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2535 = true := by
  decide +kernel

theorem tot2535 : totK PD2M8K2 D2M8K2.t2535 = [0, 82852877396, 358018042549, 363492126848, 68105326137, 1239866073, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
