import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9568 = true := by
  decide +kernel

theorem tot9568 : totK PD2M8K2 D2M8K2.t9568 = [0, 0, 215774700155, 472785122992, 177384099363, 9633262574, 0, 0] := by
  decide +kernel

theorem rows9569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9569 = true := by
  decide +kernel

theorem tot9569 : totK PD2M8K2 D2M8K2.t9569 = [0, 80405182910, 325290406169, 360425938709, 90143143518, 3472187823, 0, 0] := by
  decide +kernel

theorem rows9570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9570 = true := by
  decide +kernel

theorem tot9570 : totK PD2M8K2 D2M8K2.t9570 = [0, 173862373540, 472980783626, 260466919055, 18418208341, 0, 0, 0] := by
  decide +kernel

theorem rows9571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9571 = true := by
  decide +kernel

theorem tot9571 : totK PD2M8K2 D2M8K2.t9571 = [0, 87678414668, 365752503141, 356423218671, 59623407289, 1053411165, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
