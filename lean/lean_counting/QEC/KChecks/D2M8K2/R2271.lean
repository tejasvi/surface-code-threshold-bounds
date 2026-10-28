import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9084 = true := by
  decide +kernel

theorem tot9084 : totK PD2M8K2 D2M8K2.t9084 = [0, 0, 244272056564, 499389560381, 146548775474, 2006349614, 0, 0] := by
  decide +kernel

theorem rows9085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9085 = true := by
  decide +kernel

theorem tot9085 : totK PD2M8K2 D2M8K2.t9085 = [0, 0, 181714325826, 465449432751, 215745337405, 14203274020, 0, 0] := by
  decide +kernel

theorem rows9086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9086 = true := by
  decide +kernel

theorem tot9086 : totK PD2M8K2 D2M8K2.t9086 = [0, 0, 198619319696, 474328201706, 181426656599, 9656040098, 0, 0] := by
  decide +kernel

theorem rows9087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9087 = true := by
  decide +kernel

theorem tot9087 : totK PD2M8K2 D2M8K2.t9087 = [0, 0, 118166825879, 436994905793, 283271107264, 22503552676, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
