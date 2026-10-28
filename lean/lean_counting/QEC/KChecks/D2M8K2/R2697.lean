import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10788 = true := by
  decide +kernel

theorem tot10788 : totK PD2M8K2 D2M8K2.t10788 = [0, 0, 171302389518, 468841783067, 217638537887, 11100847513, 0, 0] := by
  decide +kernel

theorem rows10789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10789 = true := by
  decide +kernel

theorem tot10789 : totK PD2M8K2 D2M8K2.t10789 = [0, 0, 168849847679, 456233369600, 227889791670, 17079186840, 0, 0] := by
  decide +kernel

theorem rows10790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10790 = true := by
  decide +kernel

theorem tot10790 : totK PD2M8K2 D2M8K2.t10790 = [0, 0, 0, 282546261372, 466501518584, 98040785082, 1369150432, 0] := by
  decide +kernel

theorem rows10791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10791 = true := by
  decide +kernel

theorem tot10791 : totK PD2M8K2 D2M8K2.t10791 = [0, 0, 140854072676, 448432734844, 275164515029, 22695287968, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
