import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6160 = true := by
  decide +kernel

theorem tot6160 : totK PD2M8K2 D2M8K2.t6160 = [163013524395, 453457109845, 285062734553, 30482942220, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6161 = true := by
  decide +kernel

theorem tot6161 : totK PD2M8K2 D2M8K2.t6161 = [173378866008, 463419127936, 247455798316, 17196359408, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6162 = true := by
  decide +kernel

theorem tot6162 : totK PD2M8K2 D2M8K2.t6162 = [0, 233925183672, 505350328658, 157008599903, 7162567726, 0, 0, 0] := by
  decide +kernel

theorem rows6163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6163 = true := by
  decide +kernel

theorem tot6163 : totK PD2M8K2 D2M8K2.t6163 = [71386502340, 286395266401, 401789837933, 127747877197, 5874298072, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
