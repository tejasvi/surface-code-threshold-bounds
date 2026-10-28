import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1432 = true := by
  decide +kernel

theorem tot1432 : totK PD2M8K2 D2M8K2.t1432 = [0, 0, 182376504437, 478187757207, 226584833882, 10612771741, 0, 0] := by
  decide +kernel

theorem rows1433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1433 = true := by
  decide +kernel

theorem tot1433 : totK PD2M8K2 D2M8K2.t1433 = [0, 163907467286, 398831611485, 222672367790, 87563783875, 12306479239, 0, 0] := by
  decide +kernel

theorem rows1434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1434 = true := by
  decide +kernel

theorem tot1434 : totK PD2M8K2 D2M8K2.t1434 = [0, 195791637570, 471534419412, 217596466612, 12430109507, 0, 0, 0] := by
  decide +kernel

theorem rows1435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1435 = true := by
  decide +kernel

theorem tot1435 : totK PD2M8K2 D2M8K2.t1435 = [0, 47153889930, 318387010859, 425216031374, 89392008385, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
