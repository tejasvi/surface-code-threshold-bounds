import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15872 = true := by
  decide +kernel

theorem tot15872 : totK PD2M8K2 D2M8K2.t15872 = [0, 0, 152509749079, 475015528176, 237754980209, 11083510705, 0, 0] := by
  decide +kernel

theorem rows15873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15873 = true := by
  decide +kernel

theorem tot15873 : totK PD2M8K2 D2M8K2.t15873 = [0, 0, 168562286304, 453580026833, 236323480705, 14052954032, 0, 0] := by
  decide +kernel

theorem rows15874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15874 = true := by
  decide +kernel

theorem tot15874 : totK PD2M8K2 D2M8K2.t15874 = [0, 0, 0, 282080650634, 472838436973, 86160447772, 1239866073, 0] := by
  decide +kernel

theorem rows15875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15875 = true := by
  decide +kernel

theorem tot15875 : totK PD2M8K2 D2M8K2.t15875 = [0, 0, 160967727169, 427324783263, 305729611764, 33716455807, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
