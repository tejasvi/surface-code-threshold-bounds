import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10836 = true := by
  decide +kernel

theorem tot10836 : totK PD2M8K2 D2M8K2.t10836 = [0, 0, 92755880245, 449588454278, 337049886982, 32314611394, 0, 0] := by
  decide +kernel

theorem rows10837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10837 = true := by
  decide +kernel

theorem tot10837 : totK PD2M8K2 D2M8K2.t10837 = [0, 0, 0, 227849975538, 501544180783, 146424813023, 2484078857, 0] := by
  decide +kernel

theorem rows10838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10838 = true := by
  decide +kernel

theorem tot10838 : totK PD2M8K2 D2M8K2.t10838 = [0, 122183948241, 263383200859, 165033099843, 222496457868, 109855808566, 6818291842, 0] := by
  decide +kernel

theorem rows10839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10839 = true := by
  decide +kernel

theorem tot10839 : totK PD2M8K2 D2M8K2.t10839 = [0, 186965082593, 464885175789, 216420312258, 12781111781, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
