import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7636 = true := by
  decide +kernel

theorem tot7636 : totK PD2M8K2 D2M8K2.t7636 = [0, 0, 154385446764, 465043378175, 244336020324, 13914497796, 0, 0] := by
  decide +kernel

theorem rows7637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7637 = true := by
  decide +kernel

theorem tot7637 : totK PD2M8K2 D2M8K2.t7637 = [0, 0, 0, 288361362435, 488068728099, 77933743035, 1310285577, 0] := by
  decide +kernel

theorem rows7638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7638 = true := by
  decide +kernel

theorem tot7638 : totK PD2M8K2 D2M8K2.t7638 = [0, 0, 145053680410, 404406412432, 338595536395, 37915137667, 0, 0] := by
  decide +kernel

theorem rows7639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7639 = true := by
  decide +kernel

theorem tot7639 : totK PD2M8K2 D2M8K2.t7639 = [0, 0, 183193667686, 481521346841, 229594089851, 10527926217, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
