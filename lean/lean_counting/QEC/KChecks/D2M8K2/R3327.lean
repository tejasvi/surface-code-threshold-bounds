import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13308 = true := by
  decide +kernel

theorem tot13308 : totK PD2M8K2 D2M8K2.t13308 = [0, 0, 166474408260, 436178188129, 284630771248, 28604442929, 0, 0] := by
  decide +kernel

theorem rows13309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13309 = true := by
  decide +kernel

theorem tot13309 : totK PD2M8K2 D2M8K2.t13309 = [0, 0, 166583169131, 493544022137, 232397646761, 11405872210, 0, 0] := by
  decide +kernel

theorem rows13310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13310 = true := by
  decide +kernel

theorem tot13310 : totK PD2M8K2 D2M8K2.t13310 = [0, 0, 199285679702, 478740098640, 206951803682, 7831578770, 0, 0] := by
  decide +kernel

theorem rows13311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13311 = true := by
  decide +kernel

theorem tot13311 : totK PD2M8K2 D2M8K2.t13311 = [0, 0, 175762431387, 460245527579, 255241639512, 21180472961, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
