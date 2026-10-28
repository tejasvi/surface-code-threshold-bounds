import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15568 = true := by
  decide +kernel

theorem tot15568 : totK PD2M8K2 D2M8K2.t15568 = [0, 0, 0, 291395196231, 530485924675, 86091413835, 0, 0] := by
  decide +kernel

theorem rows15569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15569 = true := by
  decide +kernel

theorem tot15569 : totK PD2M8K2 D2M8K2.t15569 = [0, 0, 193267952512, 459486958702, 239388153286, 28596125077, 1415142070, 0] := by
  decide +kernel

theorem rows15570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15570 = true := by
  decide +kernel

theorem tot15570 : totK PD2M8K2 D2M8K2.t15570 = [0, 0, 205199207795, 470119941150, 227289394471, 11881054461, 0, 0] := by
  decide +kernel

theorem rows15571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15571 = true := by
  decide +kernel

theorem tot15571 : totK PD2M8K2 D2M8K2.t15571 = [0, 0, 19691318959, 378848255125, 447727736509, 64237448401, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
