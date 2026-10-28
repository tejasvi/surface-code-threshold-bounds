import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16296 = true := by
  decide +kernel

theorem tot16296 : totK PD2M8K2 D2M8K2.t16296 = [0, 0, 116959095203, 359939678783, 330455923756, 66143222711, 980853662, 0] := by
  decide +kernel

theorem rows16297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16297 = true := by
  decide +kernel

theorem tot16297 : totK PD2M8K2 D2M8K2.t16297 = [0, 0, 198274025156, 472628099519, 232066905724, 18380633500, 0, 0] := by
  decide +kernel

theorem rows16298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16298 = true := by
  decide +kernel

theorem tot16298 : totK PD2M8K2 D2M8K2.t16298 = [0, 0, 7102250273, 332732586825, 476568093149, 67023763061, 1062926506, 0] := by
  decide +kernel

theorem rows16299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16299 = true := by
  decide +kernel

theorem tot16299 : totK PD2M8K2 D2M8K2.t16299 = [0, 0, 172895966458, 446577205394, 258376010064, 23185990291, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
