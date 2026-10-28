import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12240 = true := by
  decide +kernel

theorem tot12240 : totK PD2M8K2 D2M8K2.t12240 = [171340971737, 342512148157, 139030686261, 148200176922, 92150948647, 6818291842, 0, 0] := by
  decide +kernel

theorem rows12241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12241 = true := by
  decide +kernel

theorem tot12241 : totK PD2M8K2 D2M8K2.t12241 = [158821362031, 448830287442, 250455996177, 18193274633, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12242 = true := by
  decide +kernel

theorem tot12242 : totK PD2M8K2 D2M8K2.t12242 = [76430122312, 331257120455, 377696407866, 85116755948, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows12243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12243 = true := by
  decide +kernel

theorem tot12243 : totK PD2M8K2 D2M8K2.t12243 = [15921317223, 323791443400, 494308786307, 67427430837, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
