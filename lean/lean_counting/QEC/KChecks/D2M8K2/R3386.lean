import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13544 = true := by
  decide +kernel

theorem tot13544 : totK PD2M8K2 D2M8K2.t13544 = [170968392381, 450708438545, 268124031582, 28401164684, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13545 = true := by
  decide +kernel

theorem tot13545 : totK PD2M8K2 D2M8K2.t13545 = [138006322631, 447658268672, 289352424766, 23664380677, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13546 = true := by
  decide +kernel

theorem tot13546 : totK PD2M8K2 D2M8K2.t13546 = [0, 221064734849, 499261320781, 167742106527, 7166294683, 0, 0, 0] := by
  decide +kernel

theorem rows13547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13547 = true := by
  decide +kernel

theorem tot13547 : totK PD2M8K2 D2M8K2.t13547 = [83994545022, 293938214701, 376522974079, 117100577287, 4906626486, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
