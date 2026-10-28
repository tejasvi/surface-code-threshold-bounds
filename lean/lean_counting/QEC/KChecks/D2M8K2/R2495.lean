import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9980 = true := by
  decide +kernel

theorem tot9980 : totK PD2M8K2 D2M8K2.t9980 = [0, 0, 19168591844, 328403990107, 456021885029, 72068397727, 1096505104, 0] := by
  decide +kernel

theorem rows9981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9981 = true := by
  decide +kernel

theorem tot9981 : totK PD2M8K2 D2M8K2.t9981 = [0, 0, 72653927075, 299029038843, 408819697611, 96959451906, 3821179711, 0] := by
  decide +kernel

theorem rows9982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9982 = true := by
  decide +kernel

theorem tot9982 : totK PD2M8K2 D2M8K2.t9982 = [0, 0, 166021027570, 462552574461, 270654205613, 19955014179, 0, 0] := by
  decide +kernel

theorem rows9983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9983 = true := by
  decide +kernel

theorem tot9983 : totK PD2M8K2 D2M8K2.t9983 = [0, 0, 169818916261, 460983459066, 264289069060, 20273960764, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
