import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7848 = true := by
  decide +kernel

theorem tot7848 : totK PD2M8K2 D2M8K2.t7848 = [0, 60977065888, 327897176078, 411200059417, 91004026261, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7849 = true := by
  decide +kernel

theorem tot7849 : totK PD2M8K2 D2M8K2.t7849 = [0, 58917073867, 353323204620, 431117556695, 54293519486, 0, 0, 0] := by
  decide +kernel

theorem rows7850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7850 = true := by
  decide +kernel

theorem tot7850 : totK PD2M8K2 D2M8K2.t7850 = [0, 168875497113, 442912358521, 282946250819, 30470231449, 0, 0, 0] := by
  decide +kernel

theorem rows7851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7851 = true := by
  decide +kernel

theorem tot7851 : totK PD2M8K2 D2M8K2.t7851 = [0, 186571542399, 487383562788, 225424514046, 11211226395, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
