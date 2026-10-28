import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10240 = true := by
  decide +kernel

theorem tot10240 : totK PD2M8K2 D2M8K2.t10240 = [0, 174023580011, 450228203540, 266797051394, 28509510902, 0, 0, 0] := by
  decide +kernel

theorem rows10241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10241 = true := by
  decide +kernel

theorem tot10241 : totK PD2M8K2 D2M8K2.t10241 = [0, 144648173219, 441712580477, 300996738900, 24569542896, 0, 0, 0] := by
  decide +kernel

theorem rows10242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10242 = true := by
  decide +kernel

theorem tot10242 : totK PD2M8K2 D2M8K2.t10242 = [0, 0, 228751337716, 493636444766, 163749518410, 3685198665, 0, 0] := by
  decide +kernel

theorem rows10243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10243 = true := by
  decide +kernel

theorem tot10243 : totK PD2M8K2 D2M8K2.t10243 = [0, 0, 189906924946, 458054407838, 228801651303, 16839034386, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
