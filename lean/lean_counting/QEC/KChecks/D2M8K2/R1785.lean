import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7140 = true := by
  decide +kernel

theorem tot7140 : totK PD2M8K2 D2M8K2.t7140 = [0, 0, 188867506370, 458395206761, 218331894733, 13500916298, 0, 0] := by
  decide +kernel

theorem rows7141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7141 = true := by
  decide +kernel

theorem tot7141 : totK PD2M8K2 D2M8K2.t7141 = [0, 0, 201546577488, 488707847719, 192437266863, 5242142951, 0, 0] := by
  decide +kernel

theorem rows7142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7142 = true := by
  decide +kernel

theorem tot7142 : totK PD2M8K2 D2M8K2.t7142 = [0, 0, 163595355595, 460333487287, 260379377158, 15321024391, 0, 0] := by
  decide +kernel

theorem rows7143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7143 = true := by
  decide +kernel

theorem tot7143 : totK PD2M8K2 D2M8K2.t7143 = [0, 90861460542, 307766189846, 335698300392, 159772340425, 13566916688, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
