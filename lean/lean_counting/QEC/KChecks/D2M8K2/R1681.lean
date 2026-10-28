import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6724 = true := by
  decide +kernel

theorem tot6724 : totK PD2M8K2 D2M8K2.t6724 = [0, 0, 161182880140, 465252873786, 251740845704, 16835023946, 0, 0] := by
  decide +kernel

theorem rows6725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6725 = true := by
  decide +kernel

theorem tot6725 : totK PD2M8K2 D2M8K2.t6725 = [0, 0, 0, 289954760370, 464982507655, 93420634960, 1095107716, 0] := by
  decide +kernel

theorem rows6726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6726 = true := by
  decide +kernel

theorem tot6726 : totK PD2M8K2 D2M8K2.t6726 = [124382553361, 269997547520, 86672160103, 96177277362, 222315599035, 89969846568, 3882006667, 0] := by
  decide +kernel

theorem rows6727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6727 = true := by
  decide +kernel

theorem tot6727 : totK PD2M8K2 D2M8K2.t6727 = [181852522852, 448542685514, 236928995662, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
