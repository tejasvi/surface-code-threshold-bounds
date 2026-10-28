import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6396 = true := by
  decide +kernel

theorem tot6396 : totK PD2M8K2 D2M8K2.t6396 = [0, 182588644530, 458721125276, 249557705933, 22726924806, 0, 0, 0] := by
  decide +kernel

theorem rows6397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6397 = true := by
  decide +kernel

theorem tot6397 : totK PD2M8K2 D2M8K2.t6397 = [0, 160752486511, 476705498524, 249003786247, 13602665780, 0, 0, 0] := by
  decide +kernel

theorem rows6398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6398 = true := by
  decide +kernel

theorem tot6398 : totK PD2M8K2 D2M8K2.t6398 = [0, 0, 287327388311, 499794623924, 105695615615, 1164319620, 0, 0] := by
  decide +kernel

theorem rows6399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6399 = true := by
  decide +kernel

theorem tot6399 : totK PD2M8K2 D2M8K2.t6399 = [0, 25587054555, 205544173742, 450717148850, 185028407073, 11885407614, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
