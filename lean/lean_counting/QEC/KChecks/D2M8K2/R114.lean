import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t456 = true := by
  decide +kernel

theorem tot456 : totK PD2M8K2 D2M8K2.t456 = [0, 173663677193, 471133815084, 233825265735, 13675435283, 0, 0, 0] := by
  decide +kernel

theorem rows457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t457 = true := by
  decide +kernel

theorem tot457 : totK PD2M8K2 D2M8K2.t457 = [0, 0, 292935537064, 500824666478, 105560762363, 1369150432, 0, 0] := by
  decide +kernel

theorem rows458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t458 = true := by
  decide +kernel

theorem tot458 : totK PD2M8K2 D2M8K2.t458 = [0, 87704378323, 382103846950, 387912994936, 46207127548, 0, 0, 0] := by
  decide +kernel

theorem rows459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t459 = true := by
  decide +kernel

theorem tot459 : totK PD2M8K2 D2M8K2.t459 = [0, 164242035733, 452486930265, 265782857297, 23494672053, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
