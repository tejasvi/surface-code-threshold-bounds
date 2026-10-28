import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3932 = true := by
  decide +kernel

theorem tot3932 : totK PD2M8K2 D2M8K2.t3932 = [0, 0, 191711949362, 455796566391, 216719349518, 17008616048, 0, 0] := by
  decide +kernel

theorem rows3933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3933 = true := by
  decide +kernel

theorem tot3933 : totK PD2M8K2 D2M8K2.t3933 = [0, 0, 165781372074, 487789304266, 213602562878, 6605049173, 0, 0] := by
  decide +kernel

theorem rows3934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3934 = true := by
  decide +kernel

theorem tot3934 : totK PD2M8K2 D2M8K2.t3934 = [0, 0, 145247310168, 439949390961, 259932686738, 16489188597, 0, 0] := by
  decide +kernel

theorem rows3935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3935 = true := by
  decide +kernel

theorem tot3935 : totK PD2M8K2 D2M8K2.t3935 = [0, 0, 19982922235, 326207676465, 443920775387, 66555605933, 1166720416, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
