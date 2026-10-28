import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12716 = true := by
  decide +kernel

theorem tot12716 : totK PD2M8K2 D2M8K2.t12716 = [0, 198393219248, 482855718267, 222267975169, 11603562753, 0, 0, 0] := by
  decide +kernel

theorem rows12717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12717 = true := by
  decide +kernel

theorem tot12717 : totK PD2M8K2 D2M8K2.t12717 = [0, 4194847968, 261191521553, 439022390732, 193791001996, 21400436502, 0, 0] := by
  decide +kernel

theorem rows12718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12718 = true := by
  decide +kernel

theorem tot12718 : totK PD2M8K2 D2M8K2.t12718 = [0, 0, 209480197125, 485179995315, 202300572966, 7994456143, 0, 0] := by
  decide +kernel

theorem rows12719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12719 = true := by
  decide +kernel

theorem tot12719 : totK PD2M8K2 D2M8K2.t12719 = [0, 65806493344, 251555630705, 380911117637, 177169055492, 8214505460, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
