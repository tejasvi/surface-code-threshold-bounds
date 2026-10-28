import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12952 = true := by
  decide +kernel

theorem tot12952 : totK PD2M8K2 D2M8K2.t12952 = [0, 90523122812, 245296541287, 345992974718, 210621214547, 16217208973, 0, 0] := by
  decide +kernel

theorem rows12953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12953 = true := by
  decide +kernel

theorem tot12953 : totK PD2M8K2 D2M8K2.t12953 = [0, 153243741451, 455129465587, 255183057919, 16935871064, 0, 0, 0] := by
  decide +kernel

theorem rows12954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12954 = true := by
  decide +kernel

theorem tot12954 : totK PD2M8K2 D2M8K2.t12954 = [0, 169434610987, 449861056150, 242599992721, 17180360061, 0, 0, 0] := by
  decide +kernel

theorem rows12955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12955 = true := by
  decide +kernel

theorem tot12955 : totK PD2M8K2 D2M8K2.t12955 = [0, 0, 276040396822, 505865261632, 105740450029, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
