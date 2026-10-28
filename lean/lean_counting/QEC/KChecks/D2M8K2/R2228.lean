import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8912 = true := by
  decide +kernel

theorem tot8912 : totK PD2M8K2 D2M8K2.t8912 = [117781926523, 442920129660, 318191926025, 36304934618, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8913 = true := by
  decide +kernel

theorem tot8913 : totK PD2M8K2 D2M8K2.t8913 = [0, 177076015427, 453699532096, 254165417724, 25137448963, 0, 0, 0] := by
  decide +kernel

theorem rows8914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8914 = true := by
  decide +kernel

theorem tot8914 : totK PD2M8K2 D2M8K2.t8914 = [0, 173894418214, 491288860986, 221275363906, 6590159625, 0, 0, 0] := by
  decide +kernel

theorem rows8915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8915 = true := by
  decide +kernel

theorem tot8915 : totK PD2M8K2 D2M8K2.t8915 = [176600050142, 434902365243, 235294761946, 66840183499, 5616265657, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
