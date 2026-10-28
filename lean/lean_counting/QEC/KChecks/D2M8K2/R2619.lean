import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10476 = true := by
  decide +kernel

theorem tot10476 : totK PD2M8K2 D2M8K2.t10476 = [0, 0, 0, 219165804464, 484755271908, 156684390278, 5113379825, 0] := by
  decide +kernel

theorem rows10477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10477 = true := by
  decide +kernel

theorem tot10477 : totK PD2M8K2 D2M8K2.t10477 = [0, 0, 0, 178857416970, 465415489063, 237240265495, 18184677977, 0] := by
  decide +kernel

theorem rows10478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10478 = true := by
  decide +kernel

theorem tot10478 : totK PD2M8K2 D2M8K2.t10478 = [0, 0, 0, 166387965789, 472457735127, 216371028935, 8908887416, 0] := by
  decide +kernel

theorem rows10479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10479 = true := by
  decide +kernel

theorem tot10479 : totK PD2M8K2 D2M8K2.t10479 = [0, 0, 0, 203338070906, 455469504085, 183337582220, 13097073141, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
