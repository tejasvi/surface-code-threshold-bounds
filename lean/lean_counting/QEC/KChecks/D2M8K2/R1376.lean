import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5504 = true := by
  decide +kernel

theorem tot5504 : totK PD2M8K2 D2M8K2.t5504 = [0, 0, 0, 0, 228202433141, 499512594235, 139707263523, 2679002914] := by
  decide +kernel

theorem rows5505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5505 = true := by
  decide +kernel

theorem tot5505 : totK PD2M8K2 D2M8K2.t5505 = [180062721715, 379215245065, 113678248214, 1369820453, 16078056222, 118146809879, 95785489326, 7618107313] := by
  decide +kernel

theorem rows5506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5506 = true := by
  decide +kernel

theorem tot5506 : totK PD2M8K2 D2M8K2.t5506 = [173837684314, 450066076718, 249000339987, 18197172049, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5507 = true := by
  decide +kernel

theorem tot5507 : totK PD2M8K2 D2M8K2.t5507 = [88524686467, 383727810808, 365785546545, 67186051885, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
