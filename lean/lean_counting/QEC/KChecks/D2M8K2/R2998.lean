import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11992 = true := by
  decide +kernel

theorem tot11992 : totK PD2M8K2 D2M8K2.t11992 = [0, 148608975348, 452926295294, 256434163689, 17029328244, 0, 0, 0] := by
  decide +kernel

theorem rows11993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11993 = true := by
  decide +kernel

theorem tot11993 : totK PD2M8K2 D2M8K2.t11993 = [0, 0, 319434225033, 452215866610, 75816959264, 1138244013, 0, 0] := by
  decide +kernel

theorem rows11994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11994 = true := by
  decide +kernel

theorem tot11994 : totK PD2M8K2 D2M8K2.t11994 = [0, 172254887947, 446900824941, 265771385937, 29137860636, 0, 0, 0] := by
  decide +kernel

theorem rows11995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11995 = true := by
  decide +kernel

theorem tot11995 : totK PD2M8K2 D2M8K2.t11995 = [0, 201828961509, 497031068207, 206118570886, 10179897161, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
