import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2108 = true := by
  decide +kernel

theorem tot2108 : totK PD2M8K2 D2M8K2.t2108 = [0, 171191186072, 457904942021, 256558713575, 15846953961, 0, 0, 0] := by
  decide +kernel

theorem rows2109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2109 = true := by
  decide +kernel

theorem tot2109 : totK PD2M8K2 D2M8K2.t2109 = [0, 0, 280562550838, 507051024479, 113070672658, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2110 = true := by
  decide +kernel

theorem tot2110 : totK PD2M8K2 D2M8K2.t2110 = [0, 123300623570, 415862086927, 337531089630, 34047578314, 0, 0, 0] := by
  decide +kernel

theorem rows2111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2111 = true := by
  decide +kernel

theorem tot2111 : totK PD2M8K2 D2M8K2.t2111 = [0, 176030765525, 446694524582, 249285381102, 25402281015, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
