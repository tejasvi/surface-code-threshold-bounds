import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11440 = true := by
  decide +kernel

theorem tot11440 : totK PD2M8K2 D2M8K2.t11440 = [0, 86646866432, 347160714515, 366128311414, 76055275885, 1164319620, 0, 0] := by
  decide +kernel

theorem rows11441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11441 = true := by
  decide +kernel

theorem tot11441 : totK PD2M8K2 D2M8K2.t11441 = [0, 0, 263164516109, 488924410900, 148421657822, 8423393484, 0, 0] := by
  decide +kernel

theorem rows11442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11442 = true := by
  decide +kernel

theorem tot11442 : totK PD2M8K2 D2M8K2.t11442 = [0, 129200727052, 350152020559, 310065994360, 84075603938, 3462014130, 0, 0] := by
  decide +kernel

theorem rows11443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11443 = true := by
  decide +kernel

theorem tot11443 : totK PD2M8K2 D2M8K2.t11443 = [0, 165226456874, 443220838364, 279113155974, 30386183309, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
