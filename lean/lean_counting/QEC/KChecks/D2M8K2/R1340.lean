import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5360 = true := by
  decide +kernel

theorem tot5360 : totK PD2M8K2 D2M8K2.t5360 = [0, 194379106654, 461005238912, 247226615012, 23058897148, 0, 0, 0] := by
  decide +kernel

theorem rows5361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5361 = true := by
  decide +kernel

theorem tot5361 : totK PD2M8K2 D2M8K2.t5361 = [0, 177865761262, 474053834868, 246622169892, 16574318715, 0, 0, 0] := by
  decide +kernel

theorem rows5362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5362 = true := by
  decide +kernel

theorem tot5362 : totK PD2M8K2 D2M8K2.t5362 = [0, 53308269301, 324871522432, 427920298607, 98191816560, 1268739303, 0, 0] := by
  decide +kernel

theorem rows5363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5363 = true := by
  decide +kernel

theorem tot5363 : totK PD2M8K2 D2M8K2.t5363 = [0, 0, 209301289289, 488564386321, 182200866178, 7442000727, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
