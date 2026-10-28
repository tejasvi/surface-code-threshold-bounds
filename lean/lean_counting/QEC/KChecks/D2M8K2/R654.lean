import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2616 = true := by
  decide +kernel

theorem tot2616 : totK PD2M8K2 D2M8K2.t2616 = [0, 170640662805, 446703519288, 271625011074, 24998281750, 0, 0, 0] := by
  decide +kernel

theorem rows2617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2617 = true := by
  decide +kernel

theorem tot2617 : totK PD2M8K2 D2M8K2.t2617 = [0, 164196490766, 468626388564, 264650170797, 19941197807, 0, 0, 0] := by
  decide +kernel

theorem rows2618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2618 = true := by
  decide +kernel

theorem tot2618 : totK PD2M8K2 D2M8K2.t2618 = [0, 0, 240351110931, 486438133176, 139997037444, 3250617816, 0, 0] := by
  decide +kernel

theorem rows2619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2619 = true := by
  decide +kernel

theorem tot2619 : totK PD2M8K2 D2M8K2.t2619 = [0, 0, 176927878249, 459257666736, 213802050307, 12727078017, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
