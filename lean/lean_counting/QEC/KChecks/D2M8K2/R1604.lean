import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6416 = true := by
  decide +kernel

theorem tot6416 : totK PD2M8K2 D2M8K2.t6416 = [0, 0, 190877196834, 454040832517, 219113130913, 17854363044, 0, 0] := by
  decide +kernel

theorem rows6417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6417 = true := by
  decide +kernel

theorem tot6417 : totK PD2M8K2 D2M8K2.t6417 = [0, 0, 121547502611, 441425161678, 273283089236, 18431183488, 0, 0] := by
  decide +kernel

theorem rows6418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6418 = true := by
  decide +kernel

theorem tot6418 : totK PD2M8K2 D2M8K2.t6418 = [0, 0, 0, 320693415884, 437905750944, 76424684246, 1061529118, 0] := by
  decide +kernel

theorem rows6419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6419 = true := by
  decide +kernel

theorem tot6419 : totK PD2M8K2 D2M8K2.t6419 = [0, 175895516967, 395522376646, 145395382123, 100251986538, 59577460383, 3718133097, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
