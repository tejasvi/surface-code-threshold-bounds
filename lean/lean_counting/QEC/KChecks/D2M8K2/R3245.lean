import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12980 = true := by
  decide +kernel

theorem tot12980 : totK PD2M8K2 D2M8K2.t12980 = [0, 0, 180100867441, 451920643995, 264778523598, 23282239808, 0, 0] := by
  decide +kernel

theorem rows12981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12981 = true := by
  decide +kernel

theorem tot12981 : totK PD2M8K2 D2M8K2.t12981 = [0, 0, 87927492280, 411644236796, 330145786034, 43515171751, 1162935789, 0] := by
  decide +kernel

theorem rows12982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12982 = true := by
  decide +kernel

theorem tot12982 : totK PD2M8K2 D2M8K2.t12982 = [0, 0, 0, 229828757431, 479153443927, 161365516697, 8416438934, 0] := by
  decide +kernel

theorem rows12983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12983 = true := by
  decide +kernel

theorem tot12983 : totK PD2M8K2 D2M8K2.t12983 = [0, 0, 103178256370, 356227401721, 315794892140, 77710606393, 3436822651, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
