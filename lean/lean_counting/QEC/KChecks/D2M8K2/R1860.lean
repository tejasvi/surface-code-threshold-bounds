import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7440 = true := by
  decide +kernel

theorem tot7440 : totK PD2M8K2 D2M8K2.t7440 = [0, 157218413465, 465419614429, 274291119625, 15290387421, 0, 0, 0] := by
  decide +kernel

theorem rows7441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7441 = true := by
  decide +kernel

theorem tot7441 : totK PD2M8K2 D2M8K2.t7441 = [0, 0, 284270245545, 509314881210, 105519785122, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7442 = true := by
  decide +kernel

theorem tot7442 : totK PD2M8K2 D2M8K2.t7442 = [0, 180953379104, 420247405978, 295032940114, 39456001480, 0, 0, 0] := by
  decide +kernel

theorem rows7443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7443 = true := by
  decide +kernel

theorem tot7443 : totK PD2M8K2 D2M8K2.t7443 = [0, 158125970852, 466418076057, 251072204991, 15737892132, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
