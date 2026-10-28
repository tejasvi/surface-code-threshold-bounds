import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4824 = true := by
  decide +kernel

theorem tot4824 : totK PD2M8K2 D2M8K2.t4824 = [0, 0, 172244599083, 464059447943, 234603334241, 11901139752, 0, 0] := by
  decide +kernel

theorem rows4825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4825 = true := by
  decide +kernel

theorem tot4825 : totK PD2M8K2 D2M8K2.t4825 = [0, 0, 84849439192, 335371636527, 379175269507, 81441961362, 1369150432, 0] := by
  decide +kernel

theorem rows4826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4826 = true := by
  decide +kernel

theorem tot4826 : totK PD2M8K2 D2M8K2.t4826 = [0, 0, 32409089365, 351901250023, 459648771684, 46382894935, 0, 0] := by
  decide +kernel

theorem rows4827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4827 = true := by
  decide +kernel

theorem tot4827 : totK PD2M8K2 D2M8K2.t4827 = [0, 0, 201227763105, 478713402932, 224084140765, 11807338046, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
