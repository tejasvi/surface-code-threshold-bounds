import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11044 = true := by
  decide +kernel

theorem tot11044 : totK PD2M8K2 D2M8K2.t11044 = [194734942778, 486372679757, 210011153713, 9852138406, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11045 = true := by
  decide +kernel

theorem tot11045 : totK PD2M8K2 D2M8K2.t11045 = [193256070967, 472573125058, 215958933521, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11046 = true := by
  decide +kernel

theorem tot11046 : totK PD2M8K2 D2M8K2.t11046 = [0, 283652552067, 491671185703, 106855927518, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows11047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11047 = true := by
  decide +kernel

theorem tot11047 : totK PD2M8K2 D2M8K2.t11047 = [89920432300, 380715885067, 396037440924, 55736568444, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
