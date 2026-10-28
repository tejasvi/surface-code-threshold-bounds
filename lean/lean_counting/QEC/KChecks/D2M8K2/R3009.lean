import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12036 = true := by
  decide +kernel

theorem tot12036 : totK PD2M8K2 D2M8K2.t12036 = [0, 192219954314, 469000382057, 218363853894, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows12037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12037 = true := by
  decide +kernel

theorem tot12037 : totK PD2M8K2 D2M8K2.t12037 = [0, 8088239131, 296560978394, 473676677052, 103705836644, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12038 = true := by
  decide +kernel

theorem tot12038 : totK PD2M8K2 D2M8K2.t12038 = [0, 86666238437, 371467917509, 400807951697, 47912029575, 0, 0, 0] := by
  decide +kernel

theorem rows12039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12039 = true := by
  decide +kernel

theorem tot12039 : totK PD2M8K2 D2M8K2.t12039 = [0, 168967398609, 471281317570, 231255721971, 10927086812, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
