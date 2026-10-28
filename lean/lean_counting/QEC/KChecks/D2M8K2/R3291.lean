import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13164 = true := by
  decide +kernel

theorem tot13164 : totK PD2M8K2 D2M8K2.t13164 = [0, 88397418417, 356206900521, 365928888327, 72236418601, 1164319620, 0, 0] := by
  decide +kernel

theorem rows13165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13165 = true := by
  decide +kernel

theorem tot13165 : totK PD2M8K2 D2M8K2.t13165 = [0, 0, 240131212419, 487118358039, 154383434181, 9404247146, 0, 0] := by
  decide +kernel

theorem rows13166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13166 = true := by
  decide +kernel

theorem tot13166 : totK PD2M8K2 D2M8K2.t13166 = [0, 173099396876, 423569535041, 251230385906, 51452954970, 2481160468, 0, 0] := by
  decide +kernel

theorem rows13167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13167 = true := by
  decide +kernel

theorem tot13167 : totK PD2M8K2 D2M8K2.t13167 = [0, 180894072074, 467033484545, 246802663468, 15344424258, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
