import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t536 = true := by
  decide +kernel

theorem tot536 : totK PD2M8K2 D2M8K2.t536 = [0, 54664132033, 228215282854, 397760863698, 205415214026, 13380152877, 0, 0] := by
  decide +kernel

theorem rows537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t537 = true := by
  decide +kernel

theorem tot537 : totK PD2M8K2 D2M8K2.t537 = [0, 194711978880, 475202646628, 206812920895, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t538 = true := by
  decide +kernel

theorem tot538 : totK PD2M8K2 D2M8K2.t538 = [0, 158994253745, 455553192288, 251040794911, 16367381174, 0, 0, 0] := by
  decide +kernel

theorem rows539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t539 = true := by
  decide +kernel

theorem tot539 : totK PD2M8K2 D2M8K2.t539 = [0, 0, 281829790075, 495452782082, 100407136915, 1310166938, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
