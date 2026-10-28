import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9616 = true := by
  decide +kernel

theorem tot9616 : totK PD2M8K2 D2M8K2.t9616 = [0, 77417937853, 341763730987, 395130934976, 89874184976, 1369150432, 0, 0] := by
  decide +kernel

theorem rows9617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9617 = true := by
  decide +kernel

theorem tot9617 : totK PD2M8K2 D2M8K2.t9617 = [0, 22235602472, 334677778408, 488724868560, 61833721898, 0, 0, 0] := by
  decide +kernel

theorem rows9618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9618 = true := by
  decide +kernel

theorem tot9618 : totK PD2M8K2 D2M8K2.t9618 = [0, 208205767893, 468176542146, 208768451211, 18297206428, 0, 0, 0] := by
  decide +kernel

theorem rows9619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9619 = true := by
  decide +kernel

theorem tot9619 : totK PD2M8K2 D2M8K2.t9619 = [0, 150890891956, 452507039653, 260406165832, 16206221945, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
