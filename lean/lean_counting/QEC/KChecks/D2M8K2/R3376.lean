import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13504 = true := by
  decide +kernel

theorem tot13504 : totK PD2M8K2 D2M8K2.t13504 = [200166900323, 476418088642, 215538901877, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13505 = true := by
  decide +kernel

theorem tot13505 : totK PD2M8K2 D2M8K2.t13505 = [55608356038, 329135222617, 426726971331, 92788249007, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows13506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13506 = true := by
  decide +kernel

theorem tot13506 : totK PD2M8K2 D2M8K2.t13506 = [37194636605, 344729833936, 475722141907, 62687453828, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13507 = true := by
  decide +kernel

theorem tot13507 : totK PD2M8K2 D2M8K2.t13507 = [198129760449, 465750039244, 222715617929, 18437600341, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
