import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1744 = true := by
  decide +kernel

theorem tot1744 : totK PD2M8K2 D2M8K2.t1744 = [0, 0, 84744980936, 377335598308, 349757181946, 62809210044, 1369150432, 0] := by
  decide +kernel

theorem rows1745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1745 = true := by
  decide +kernel

theorem tot1745 : totK PD2M8K2 D2M8K2.t1745 = [0, 0, 0, 298461173994, 503809257619, 81119893347, 0, 0] := by
  decide +kernel

theorem rows1746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1746 = true := by
  decide +kernel

theorem tot1746 : totK PD2M8K2 D2M8K2.t1746 = [0, 0, 185803083612, 457217924626, 233368955103, 19710036796, 0, 0] := by
  decide +kernel

theorem rows1747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1747 = true := by
  decide +kernel

theorem tot1747 : totK PD2M8K2 D2M8K2.t1747 = [0, 0, 203428932208, 475849225846, 206144338210, 12435483790, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
