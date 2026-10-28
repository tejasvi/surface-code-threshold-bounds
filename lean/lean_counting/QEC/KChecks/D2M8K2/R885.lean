import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3540 = true := by
  decide +kernel

theorem tot3540 : totK PD2M8K2 D2M8K2.t3540 = [89005186762, 254618127695, 340327683215, 206295685735, 20790672307, 0, 0, 0] := by
  decide +kernel

theorem rows3541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3541 = true := by
  decide +kernel

theorem tot3541 : totK PD2M8K2 D2M8K2.t3541 = [168727792346, 465572889451, 231007475302, 14566626306, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3542 = true := by
  decide +kernel

theorem tot3542 : totK PD2M8K2 D2M8K2.t3542 = [138678414711, 432154478285, 284567556598, 22496290624, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3543 = true := by
  decide +kernel

theorem tot3543 : totK PD2M8K2 D2M8K2.t3543 = [0, 268733945137, 499011273299, 111162358622, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
