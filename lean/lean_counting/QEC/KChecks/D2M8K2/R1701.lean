import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6804 = true := by
  decide +kernel

theorem tot6804 : totK PD2M8K2 D2M8K2.t6804 = [0, 163648979780, 493098440936, 234322658600, 7817444069, 0, 0, 0] := by
  decide +kernel

theorem rows6805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6805 = true := by
  decide +kernel

theorem tot6805 : totK PD2M8K2 D2M8K2.t6805 = [112859636424, 343654150534, 314991395157, 124831237126, 8209931632, 0, 0, 0] := by
  decide +kernel

theorem rows6806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6806 = true := by
  decide +kernel

theorem tot6806 : totK PD2M8K2 D2M8K2.t6806 = [168615980266, 445509742463, 276517393205, 30173504110, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6807 = true := by
  decide +kernel

theorem tot6807 : totK PD2M8K2 D2M8K2.t6807 = [155719671090, 465180831419, 274636625616, 19963177022, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
