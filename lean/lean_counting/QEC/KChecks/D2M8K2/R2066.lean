import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8264 = true := by
  decide +kernel

theorem tot8264 : totK PD2M8K2 D2M8K2.t8264 = [37220374354, 311076004377, 446808915603, 100943129216, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows8265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8265 = true := by
  decide +kernel

theorem tot8265 : totK PD2M8K2 D2M8K2.t8265 = [0, 209396785121, 478848564879, 189044236789, 7439461435, 0, 0, 0] := by
  decide +kernel

theorem rows8266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8266 = true := by
  decide +kernel

theorem tot8266 : totK PD2M8K2 D2M8K2.t8266 = [0, 197197273912, 470422255086, 214166599744, 14704558535, 0, 0, 0] := by
  decide +kernel

theorem rows8267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8267 = true := by
  decide +kernel

theorem tot8267 : totK PD2M8K2 D2M8K2.t8267 = [0, 172768843321, 469057118175, 214094679175, 10735115630, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
