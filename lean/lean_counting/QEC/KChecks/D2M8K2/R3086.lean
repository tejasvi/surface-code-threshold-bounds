import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12344 = true := by
  decide +kernel

theorem tot12344 : totK PD2M8K2 D2M8K2.t12344 = [0, 75082883077, 354538843073, 369161017198, 72198816001, 1095107716, 0, 0] := by
  decide +kernel

theorem rows12345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12345 = true := by
  decide +kernel

theorem tot12345 : totK PD2M8K2 D2M8K2.t12345 = [0, 0, 288195348574, 477053277893, 110725681525, 2156095145, 0, 0] := by
  decide +kernel

theorem rows12346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12346 = true := by
  decide +kernel

theorem tot12346 : totK PD2M8K2 D2M8K2.t12346 = [0, 199648681404, 483667554431, 201140813459, 16305342012, 1725911522, 0, 0] := by
  decide +kernel

theorem rows12347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12347 = true := by
  decide +kernel

theorem tot12347 : totK PD2M8K2 D2M8K2.t12347 = [0, 194946944089, 467325170775, 218576529502, 12534051746, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
