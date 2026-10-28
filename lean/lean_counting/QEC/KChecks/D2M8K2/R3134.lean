import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12536 = true := by
  decide +kernel

theorem tot12536 : totK PD2M8K2 D2M8K2.t12536 = [0, 0, 274946134414, 503932741254, 111690680517, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12537 = true := by
  decide +kernel

theorem tot12537 : totK PD2M8K2 D2M8K2.t12537 = [0, 89157145599, 392083296850, 391004492991, 48081446903, 0, 0, 0] := by
  decide +kernel

theorem rows12538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12538 = true := by
  decide +kernel

theorem tot12538 : totK PD2M8K2 D2M8K2.t12538 = [0, 178266800546, 469128861465, 247080985181, 13836750989, 0, 0, 0] := by
  decide +kernel

theorem rows12539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12539 = true := by
  decide +kernel

theorem tot12539 : totK PD2M8K2 D2M8K2.t12539 = [0, 59941890823, 318690173961, 392436227416, 147131857862, 9977052014, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
