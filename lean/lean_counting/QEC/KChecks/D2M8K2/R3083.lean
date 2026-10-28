import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12332 = true := by
  decide +kernel

theorem tot12332 : totK PD2M8K2 D2M8K2.t12332 = [0, 187932514692, 478235025760, 200653780380, 9740140984, 0, 0, 0] := by
  decide +kernel

theorem rows12333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12333 = true := by
  decide +kernel

theorem tot12333 : totK PD2M8K2 D2M8K2.t12333 = [0, 153585196779, 462178268934, 243509360163, 13678269203, 0, 0, 0] := by
  decide +kernel

theorem rows12334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12334 = true := by
  decide +kernel

theorem tot12334 : totK PD2M8K2 D2M8K2.t12334 = [0, 0, 304792535994, 463132464799, 78734161071, 1138244013, 0, 0] := by
  decide +kernel

theorem rows12335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12335 = true := by
  decide +kernel

theorem tot12335 : totK PD2M8K2 D2M8K2.t12335 = [0, 165681719444, 434015509035, 281956190922, 30870062251, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
