import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13548 = true := by
  decide +kernel

theorem tot13548 : totK PD2M8K2 D2M8K2.t13548 = [154300243266, 461716415473, 276310195742, 25210004210, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13549 = true := by
  decide +kernel

theorem tot13549 : totK PD2M8K2 D2M8K2.t13549 = [140453221750, 432211921901, 275247620355, 21173232784, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13550 = true := by
  decide +kernel

theorem tot13550 : totK PD2M8K2 D2M8K2.t13550 = [0, 278107075308, 513963416585, 102722732156, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows13551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13551 = true := by
  decide +kernel

theorem tot13551 : totK PD2M8K2 D2M8K2.t13551 = [166769743569, 375655576877, 260140261242, 82236653405, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
