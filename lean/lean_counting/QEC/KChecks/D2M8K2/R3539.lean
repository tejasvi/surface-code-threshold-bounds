import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14156 = true := by
  decide +kernel

theorem tot14156 : totK PD2M8K2 D2M8K2.t14156 = [39845626551, 219536972771, 439062913763, 197200149302, 8214505460, 0, 0, 0] := by
  decide +kernel

theorem rows14157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14157 = true := by
  decide +kernel

theorem tot14157 : totK PD2M8K2 D2M8K2.t14157 = [191652004934, 465397549771, 248174947577, 23388038350, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14158 = true := by
  decide +kernel

theorem tot14158 : totK PD2M8K2 D2M8K2.t14158 = [190243527887, 467113495230, 221089241565, 12346377983, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14159 = true := by
  decide +kernel

theorem tot14159 : totK PD2M8K2 D2M8K2.t14159 = [0, 300896399688, 494454765401, 104650060123, 1163840124, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
