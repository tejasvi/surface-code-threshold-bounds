import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11704 = true := by
  decide +kernel

theorem tot11704 : totK PD2M8K2 D2M8K2.t11704 = [176652642738, 457134853474, 266948375994, 20292297169, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11705 = true := by
  decide +kernel

theorem tot11705 : totK PD2M8K2 D2M8K2.t11705 = [138944559242, 443886422990, 297114050686, 35324547668, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11706 = true := by
  decide +kernel

theorem tot11706 : totK PD2M8K2 D2M8K2.t11706 = [0, 175199824869, 446268005322, 257201251878, 25348106850, 0, 0, 0] := by
  decide +kernel

theorem rows11707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11707 = true := by
  decide +kernel

theorem tot11707 : totK PD2M8K2 D2M8K2.t11707 = [0, 175726416288, 482263153723, 237650697936, 7775088342, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
