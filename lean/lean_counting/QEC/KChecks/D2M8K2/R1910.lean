import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7640 = true := by
  decide +kernel

theorem tot7640 : totK PD2M8K2 D2M8K2.t7640 = [0, 0, 173987639521, 466067971509, 245188395948, 15996054500, 0, 0] := by
  decide +kernel

theorem rows7641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7641 = true := by
  decide +kernel

theorem tot7641 : totK PD2M8K2 D2M8K2.t7641 = [0, 0, 180099788424, 454879535680, 260364513390, 23745513428, 0, 0] := by
  decide +kernel

theorem rows7642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7642 = true := by
  decide +kernel

theorem tot7642 : totK PD2M8K2 D2M8K2.t7642 = [0, 0, 160519261082, 459533474851, 258125506760, 19212449259, 0, 0] := by
  decide +kernel

theorem rows7643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7643 = true := by
  decide +kernel

theorem tot7643 : totK PD2M8K2 D2M8K2.t7643 = [0, 0, 0, 241049832537, 486976368253, 130861940868, 4879840392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
