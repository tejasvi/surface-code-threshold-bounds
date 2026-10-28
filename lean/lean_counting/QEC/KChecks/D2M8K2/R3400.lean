import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13600 = true := by
  decide +kernel

theorem tot13600 : totK PD2M8K2 D2M8K2.t13600 = [0, 149917210474, 444467994773, 287293757364, 25201026942, 0, 0, 0] := by
  decide +kernel

theorem rows13601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13601 = true := by
  decide +kernel

theorem tot13601 : totK PD2M8K2 D2M8K2.t13601 = [0, 208162573894, 457684594113, 199731642893, 12096313584, 0, 0, 0] := by
  decide +kernel

theorem rows13602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13602 = true := by
  decide +kernel

theorem tot13602 : totK PD2M8K2 D2M8K2.t13602 = [0, 19168591844, 325235154410, 430845712685, 67529993068, 1053411165, 0, 0] := by
  decide +kernel

theorem rows13603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13603 = true := by
  decide +kernel

theorem tot13603 : totK PD2M8K2 D2M8K2.t13603 = [0, 85071533861, 314051108605, 368211724811, 93560214925, 3667207281, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
