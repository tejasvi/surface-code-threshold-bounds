import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10052 = true := by
  decide +kernel

theorem tot10052 : totK PD2M8K2 D2M8K2.t10052 = [0, 0, 116727487741, 353422240086, 337957907627, 75471430882, 1186940923, 0] := by
  decide +kernel

theorem rows10053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10053 = true := by
  decide +kernel

theorem tot10053 : totK PD2M8K2 D2M8K2.t10053 = [0, 0, 163336150152, 438602973794, 275292079044, 28775531976, 0, 0] := by
  decide +kernel

theorem rows10054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10054 = true := by
  decide +kernel

theorem tot10054 : totK PD2M8K2 D2M8K2.t10054 = [0, 0, 131561998149, 454843406536, 282485002914, 14851306715, 0, 0] := by
  decide +kernel

theorem rows10055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10055 = true := by
  decide +kernel

theorem tot10055 : totK PD2M8K2 D2M8K2.t10055 = [0, 0, 0, 326784439456, 518530052955, 69430606912, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
