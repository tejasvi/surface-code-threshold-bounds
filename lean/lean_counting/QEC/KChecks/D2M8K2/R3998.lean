import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15992 = true := by
  decide +kernel

theorem tot15992 : totK PD2M8K2 D2M8K2.t15992 = [0, 0, 186752643156, 460319992429, 259696803916, 25870296544, 0, 0] := by
  decide +kernel

theorem rows15993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15993 = true := by
  decide +kernel

theorem tot15993 : totK PD2M8K2 D2M8K2.t15993 = [0, 0, 133038082937, 447774185266, 302786234120, 23448455236, 0, 0] := by
  decide +kernel

theorem rows15994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15994 = true := by
  decide +kernel

theorem tot15994 : totK PD2M8K2 D2M8K2.t15994 = [0, 0, 0, 275241076216, 508202147015, 127573760070, 3718846349, 0] := by
  decide +kernel

theorem rows15995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15995 = true := by
  decide +kernel

theorem tot15995 : totK PD2M8K2 D2M8K2.t15995 = [0, 0, 111472069962, 346925224490, 314280338092, 118360112825, 8913356732, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
