import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13340 = true := by
  decide +kernel

theorem tot13340 : totK PD2M8K2 D2M8K2.t13340 = [0, 0, 153675688372, 478772654253, 231467037655, 11083510705, 0, 0] := by
  decide +kernel

theorem rows13341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13341 = true := by
  decide +kernel

theorem tot13341 : totK PD2M8K2 D2M8K2.t13341 = [0, 0, 161194675879, 456554367058, 232193374989, 10278483041, 0, 0] := by
  decide +kernel

theorem rows13342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13342 = true := by
  decide +kernel

theorem tot13342 : totK PD2M8K2 D2M8K2.t13342 = [0, 0, 0, 285788898968, 477224135606, 80017602818, 1239866073, 0] := by
  decide +kernel

theorem rows13343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13343 = true := by
  decide +kernel

theorem tot13343 : totK PD2M8K2 D2M8K2.t13343 = [0, 0, 161997361240, 448388604323, 285387543958, 25860252009, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
