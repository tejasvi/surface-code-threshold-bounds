import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5232 = true := by
  decide +kernel

theorem tot5232 : totK PD2M8K2 D2M8K2.t5232 = [0, 0, 160527235656, 477957465438, 252620413351, 11600771062, 0, 0] := by
  decide +kernel

theorem rows5233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5233 = true := by
  decide +kernel

theorem tot5233 : totK PD2M8K2 D2M8K2.t5233 = [0, 0, 194490787031, 469798220777, 213911810480, 12264129317, 0, 0] := by
  decide +kernel

theorem rows5234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5234 = true := by
  decide +kernel

theorem tot5234 : totK PD2M8K2 D2M8K2.t5234 = [0, 94311201580, 306494519441, 358166292614, 156437570748, 13468148062, 0, 0] := by
  decide +kernel

theorem rows5235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5235 = true := by
  decide +kernel

theorem tot5235 : totK PD2M8K2 D2M8K2.t5235 = [0, 176657828183, 457212346017, 254451064167, 20903957820, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
