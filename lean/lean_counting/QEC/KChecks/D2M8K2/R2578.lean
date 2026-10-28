import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10312 = true := by
  decide +kernel

theorem tot10312 : totK PD2M8K2 D2M8K2.t10312 = [0, 165485407656, 440243352121, 286392042784, 30374593025, 0, 0, 0] := by
  decide +kernel

theorem rows10313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10313 = true := by
  decide +kernel

theorem tot10313 : totK PD2M8K2 D2M8K2.t10313 = [0, 87942599106, 385703584858, 354573921721, 58330415318, 1198073392, 0, 0] := by
  decide +kernel

theorem rows10314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10314 = true := by
  decide +kernel

theorem tot10314 : totK PD2M8K2 D2M8K2.t10314 = [0, 0, 236756570408, 486804127609, 166804570688, 8470662040, 0, 0] := by
  decide +kernel

theorem rows10315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10315 = true := by
  decide +kernel

theorem tot10315 : totK PD2M8K2 D2M8K2.t10315 = [0, 105483684527, 351287840527, 337850316481, 92814658496, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
