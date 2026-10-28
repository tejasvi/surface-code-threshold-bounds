import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7608 = true := by
  decide +kernel

theorem tot7608 : totK PD2M8K2 D2M8K2.t7608 = [0, 0, 196393050437, 472329487776, 217663235551, 12370590376, 0, 0] := by
  decide +kernel

theorem rows7609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7609 = true := by
  decide +kernel

theorem tot7609 : totK PD2M8K2 D2M8K2.t7609 = [0, 0, 162910830179, 485715251218, 225800928539, 8523456350, 0, 0] := by
  decide +kernel

theorem rows7610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7610 = true := by
  decide +kernel

theorem tot7610 : totK PD2M8K2 D2M8K2.t7610 = [0, 0, 202036858175, 476506458168, 205680917690, 8947632119, 0, 0] := by
  decide +kernel

theorem rows7611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7611 = true := by
  decide +kernel

theorem tot7611 : totK PD2M8K2 D2M8K2.t7611 = [0, 0, 189225663980, 470039967508, 224428518593, 13828303334, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
