import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9748 = true := by
  decide +kernel

theorem tot9748 : totK PD2M8K2 D2M8K2.t9748 = [0, 0, 0, 280961772419, 473095110338, 81472531016, 1288491354, 0] := by
  decide +kernel

theorem rows9749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9749 = true := by
  decide +kernel

theorem tot9749 : totK PD2M8K2 D2M8K2.t9749 = [0, 0, 177287502842, 434863235039, 273226872364, 32344806501, 0, 0] := by
  decide +kernel

theorem rows9750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9750 = true := by
  decide +kernel

theorem tot9750 : totK PD2M8K2 D2M8K2.t9750 = [0, 0, 230424877673, 495153692417, 172761420542, 5740059145, 0, 0] := by
  decide +kernel

theorem rows9751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9751 = true := by
  decide +kernel

theorem tot9751 : totK PD2M8K2 D2M8K2.t9751 = [0, 0, 176206214376, 474963929999, 218479612791, 17532943104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
