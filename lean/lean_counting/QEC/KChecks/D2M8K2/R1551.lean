import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6204 = true := by
  decide +kernel

theorem tot6204 : totK PD2M8K2 D2M8K2.t6204 = [181097966188, 471711452847, 245517039678, 15394402876, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6205 = true := by
  decide +kernel

theorem tot6205 : totK PD2M8K2 D2M8K2.t6205 = [88921332855, 345635814770, 390355930586, 77137393632, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows6206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6206 = true := by
  decide +kernel

theorem tot6206 : totK PD2M8K2 D2M8K2.t6206 = [0, 248286548411, 497580828221, 151231210238, 8423393484, 0, 0, 0] := by
  decide +kernel

theorem rows6207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6207 = true := by
  decide +kernel

theorem tot6207 : totK PD2M8K2 D2M8K2.t6207 = [135752362032, 370034148099, 302002933690, 78641480028, 3462014130, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
