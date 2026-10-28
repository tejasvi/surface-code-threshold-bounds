import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14932 = true := by
  decide +kernel

theorem tot14932 : totK PD2M8K2 D2M8K2.t14932 = [0, 0, 200333315619, 487644532935, 173496353711, 5106786593, 0, 0] := by
  decide +kernel

theorem rows14933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14933 = true := by
  decide +kernel

theorem tot14933 : totK PD2M8K2 D2M8K2.t14933 = [0, 0, 55283614186, 328043885339, 394504808184, 80879190053, 1369150432, 0] := by
  decide +kernel

theorem rows14934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14934 = true := by
  decide +kernel

theorem tot14934 : totK PD2M8K2 D2M8K2.t14934 = [0, 0, 82823073311, 374615289214, 357016840234, 34818885332, 0, 0] := by
  decide +kernel

theorem rows14935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14935 = true := by
  decide +kernel

theorem tot14935 : totK PD2M8K2 D2M8K2.t14935 = [0, 0, 164574254448, 495610168939, 224151749115, 6798205849, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
