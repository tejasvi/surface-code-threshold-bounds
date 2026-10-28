import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12104 = true := by
  decide +kernel

theorem tot12104 : totK PD2M8K2 D2M8K2.t12104 = [0, 0, 179684347898, 481154024072, 203099745640, 6799393473, 0, 0] := by
  decide +kernel

theorem rows12105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12105 = true := by
  decide +kernel

theorem tot12105 : totK PD2M8K2 D2M8K2.t12105 = [0, 0, 205258727145, 467635105462, 178210193118, 11549710348, 0, 0] := by
  decide +kernel

theorem rows12106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12106 = true := by
  decide +kernel

theorem tot12106 : totK PD2M8K2 D2M8K2.t12106 = [0, 0, 183301239626, 464243747586, 204230870381, 12293492090, 0, 0] := by
  decide +kernel

theorem rows12107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12107 = true := by
  decide +kernel

theorem tot12107 : totK PD2M8K2 D2M8K2.t12107 = [0, 0, 19322019972, 321202526590, 425801032960, 77413993151, 1217496766, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
