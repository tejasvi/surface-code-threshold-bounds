import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12384 = true := by
  decide +kernel

theorem tot12384 : totK PD2M8K2 D2M8K2.t12384 = [0, 181720178412, 456649315677, 268203763081, 28066296660, 0, 0, 0] := by
  decide +kernel

theorem rows12385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12385 = true := by
  decide +kernel

theorem tot12385 : totK PD2M8K2 D2M8K2.t12385 = [0, 164871096316, 457183504494, 253652316946, 17788377529, 0, 0, 0] := by
  decide +kernel

theorem rows12386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12386 = true := by
  decide +kernel

theorem tot12386 : totK PD2M8K2 D2M8K2.t12386 = [0, 0, 251801939566, 486070607887, 149054819298, 8464368736, 0, 0] := by
  decide +kernel

theorem rows12387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12387 = true := by
  decide +kernel

theorem tot12387 : totK PD2M8K2 D2M8K2.t12387 = [0, 82003072397, 325457525477, 376163950757, 96310077258, 3575904516, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
