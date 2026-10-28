import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13168 = true := by
  decide +kernel

theorem tot13168 : totK PD2M8K2 D2M8K2.t13168 = [0, 71891312889, 325805918788, 401543009931, 89710572759, 1198073392, 0, 0] := by
  decide +kernel

theorem rows13169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13169 = true := by
  decide +kernel

theorem tot13169 : totK PD2M8K2 D2M8K2.t13169 = [0, 0, 217857896764, 488046168175, 171750822490, 9482920370, 0, 0] := by
  decide +kernel

theorem rows13170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13170 = true := by
  decide +kernel

theorem tot13170 : totK PD2M8K2 D2M8K2.t13170 = [0, 174538732713, 424243767411, 247458700423, 54381886137, 2569691499, 0, 0] := by
  decide +kernel

theorem rows13171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13171 = true := by
  decide +kernel

theorem tot13171 : totK PD2M8K2 D2M8K2.t13171 = [0, 172144443738, 440457087826, 273384082986, 30211850834, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
