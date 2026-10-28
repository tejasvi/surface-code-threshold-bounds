import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10812 = true := by
  decide +kernel

theorem tot10812 : totK PD2M8K2 D2M8K2.t10812 = [0, 158714876269, 429849597617, 314241210696, 46604352594, 0, 0, 0] := by
  decide +kernel

theorem rows10813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10813 = true := by
  decide +kernel

theorem tot10813 : totK PD2M8K2 D2M8K2.t10813 = [0, 171371160503, 480778845023, 243551680392, 13049501762, 0, 0, 0] := by
  decide +kernel

theorem rows10814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10814 = true := by
  decide +kernel

theorem tot10814 : totK PD2M8K2 D2M8K2.t10814 = [0, 0, 327704851186, 528594751263, 76390392530, 0, 0, 0] := by
  decide +kernel

theorem rows10815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10815 = true := by
  decide +kernel

theorem tot10815 : totK PD2M8K2 D2M8K2.t10815 = [0, 161977806534, 399024851707, 276940730236, 74442847502, 2804045914, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
