import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1524 = true := by
  decide +kernel

theorem tot1524 : totK PD2M8K2 D2M8K2.t1524 = [0, 0, 197284612612, 469832607732, 210370260170, 16687972365, 0, 0] := by
  decide +kernel

theorem rows1525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1525 = true := by
  decide +kernel

theorem tot1525 : totK PD2M8K2 D2M8K2.t1525 = [0, 0, 192353258700, 469082182855, 206020096045, 12206147664, 0, 0] := by
  decide +kernel

theorem rows1526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1526 = true := by
  decide +kernel

theorem tot1526 : totK PD2M8K2 D2M8K2.t1526 = [0, 0, 51735824847, 324193764143, 402869120236, 94081546300, 1369150432, 0] := by
  decide +kernel

theorem rows1527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1527 = true := by
  decide +kernel

theorem tot1527 : totK PD2M8K2 D2M8K2.t1527 = [0, 0, 69176770246, 371156962483, 379107067830, 48586926281, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
