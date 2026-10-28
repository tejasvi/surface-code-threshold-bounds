import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8636 = true := by
  decide +kernel

theorem tot8636 : totK PD2M8K2 D2M8K2.t8636 = [46397323223, 226532758853, 428366210417, 197982622197, 8213711289, 0, 0, 0] := by
  decide +kernel

theorem rows8637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8637 = true := by
  decide +kernel

theorem tot8637 : totK PD2M8K2 D2M8K2.t8637 = [196266983687, 456146671247, 244130943021, 23219762177, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8638 = true := by
  decide +kernel

theorem tot8638 : totK PD2M8K2 D2M8K2.t8638 = [142717529808, 459172173815, 281209357387, 17596233253, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8639 = true := by
  decide +kernel

theorem tot8639 : totK PD2M8K2 D2M8K2.t8639 = [0, 241026577979, 509227862246, 144892091717, 2309606161, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
