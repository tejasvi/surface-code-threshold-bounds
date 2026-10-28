import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9260 = true := by
  decide +kernel

theorem tot9260 : totK PD2M8K2 D2M8K2.t9260 = [0, 167693127223, 502259714439, 226683023532, 6457187392, 0, 0, 0] := by
  decide +kernel

theorem rows9261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9261 = true := by
  decide +kernel

theorem tot9261 : totK PD2M8K2 D2M8K2.t9261 = [175298174919, 431956580851, 237132475434, 63091462182, 5601145729, 0, 0, 0] := by
  decide +kernel

theorem rows9262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9262 = true := by
  decide +kernel

theorem tot9262 : totK PD2M8K2 D2M8K2.t9262 = [181087757825, 479869790979, 238567064823, 15438787667, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9263 = true := by
  decide +kernel

theorem tot9263 : totK PD2M8K2 D2M8K2.t9263 = [84801560820, 334875677990, 393772945137, 88351671553, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
