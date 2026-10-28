import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9780 = true := by
  decide +kernel

theorem tot9780 : totK PD2M8K2 D2M8K2.t9780 = [0, 179285595908, 464195645634, 243721400250, 17143881210, 0, 0, 0] := by
  decide +kernel

theorem rows9781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9781 = true := by
  decide +kernel

theorem tot9781 : totK PD2M8K2 D2M8K2.t9781 = [0, 0, 267800690876, 498565136419, 119157034554, 1268739303, 0, 0] := by
  decide +kernel

theorem rows9782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9782 = true := by
  decide +kernel

theorem tot9782 : totK PD2M8K2 D2M8K2.t9782 = [0, 0, 196811642578, 485444679480, 187898105438, 7442000727, 0, 0] := by
  decide +kernel

theorem rows9783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9783 = true := by
  decide +kernel

theorem tot9783 : totK PD2M8K2 D2M8K2.t9783 = [0, 0, 178382231649, 463599627314, 229486515214, 15860424110, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
