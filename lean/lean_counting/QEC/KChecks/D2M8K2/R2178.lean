import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8712 = true := by
  decide +kernel

theorem tot8712 : totK PD2M8K2 D2M8K2.t8712 = [0, 161325574683, 414796082551, 260574337550, 73826202790, 5570701333, 0, 0] := by
  decide +kernel

theorem rows8713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8713 = true := by
  decide +kernel

theorem tot8713 : totK PD2M8K2 D2M8K2.t8713 = [0, 194515884192, 461080683416, 222881468766, 15584516250, 0, 0, 0] := by
  decide +kernel

theorem rows8714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8714 = true := by
  decide +kernel

theorem tot8714 : totK PD2M8K2 D2M8K2.t8714 = [0, 70856345395, 345141364360, 395648243265, 86867580341, 1164319620, 0, 0] := by
  decide +kernel

theorem rows8715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8715 = true := by
  decide +kernel

theorem tot8715 : totK PD2M8K2 D2M8K2.t8715 = [0, 0, 206154852512, 488375190994, 175170034252, 9404247146, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
