import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13540 = true := by
  decide +kernel

theorem tot13540 : totK PD2M8K2 D2M8K2.t13540 = [168291068445, 444947568155, 280750803754, 30345765488, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13541 = true := by
  decide +kernel

theorem tot13541 : totK PD2M8K2 D2M8K2.t13541 = [89460269429, 398447594277, 363653849174, 68140134579, 5319205844, 0, 0, 0] := by
  decide +kernel

theorem rows13542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13542 = true := by
  decide +kernel

theorem tot13542 : totK PD2M8K2 D2M8K2.t13542 = [0, 156235274708, 456273266729, 259766789039, 18236668518, 0, 0, 0] := by
  decide +kernel

theorem rows13543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13543 = true := by
  decide +kernel

theorem tot13543 : totK PD2M8K2 D2M8K2.t13543 = [121298973571, 346769390684, 308893335483, 129038269676, 8200183796, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
