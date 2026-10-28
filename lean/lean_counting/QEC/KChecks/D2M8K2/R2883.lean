import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11532 = true := by
  decide +kernel

theorem tot11532 : totK PD2M8K2 D2M8K2.t11532 = [0, 0, 218570869762, 492405613180, 187232945774, 5358820111, 0, 0] := by
  decide +kernel

theorem rows11533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11533 = true := by
  decide +kernel

theorem tot11533 : totK PD2M8K2 D2M8K2.t11533 = [0, 156085019224, 366370865835, 268833950293, 110708488833, 6804944647, 0, 0] := by
  decide +kernel

theorem rows11534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11534 = true := by
  decide +kernel

theorem tot11534 : totK PD2M8K2 D2M8K2.t11534 = [0, 159148583766, 451075913210, 269060688841, 19870918187, 0, 0, 0] := by
  decide +kernel

theorem rows11535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11535 = true := by
  decide +kernel

theorem tot11535 : totK PD2M8K2 D2M8K2.t11535 = [0, 88225718792, 344460520353, 384273038999, 85446417587, 1129969115, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
