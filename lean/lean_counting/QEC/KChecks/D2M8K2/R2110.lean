import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8440 = true := by
  decide +kernel

theorem tot8440 : totK PD2M8K2 D2M8K2.t8440 = [0, 194430985151, 469375198716, 241519488205, 20718373538, 0, 0, 0] := by
  decide +kernel

theorem rows8441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8441 = true := by
  decide +kernel

theorem tot8441 : totK PD2M8K2 D2M8K2.t8441 = [0, 193763658809, 474203010040, 228451631211, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows8442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8442 = true := by
  decide +kernel

theorem tot8442 : totK PD2M8K2 D2M8K2.t8442 = [0, 52088170802, 330024809407, 429782640884, 88851812383, 1178750802, 0, 0] := by
  decide +kernel

theorem rows8443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8443 = true := by
  decide +kernel

theorem tot8443 : totK PD2M8K2 D2M8K2.t8443 = [0, 0, 196013139453, 483453444937, 186155784122, 10460680991, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
