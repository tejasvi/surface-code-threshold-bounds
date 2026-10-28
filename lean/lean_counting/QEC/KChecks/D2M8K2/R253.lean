import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1012 = true := by
  decide +kernel

theorem tot1012 : totK PD2M8K2 D2M8K2.t1012 = [0, 212324399813, 504167351060, 169635503369, 2519015093, 0, 0, 0] := by
  decide +kernel

theorem rows1013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1013 = true := by
  decide +kernel

theorem tot1013 : totK PD2M8K2 D2M8K2.t1013 = [0, 163642876377, 460040463607, 242858076363, 13621712409, 0, 0, 0] := by
  decide +kernel

theorem rows1014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1014 = true := by
  decide +kernel

theorem tot1014 : totK PD2M8K2 D2M8K2.t1014 = [0, 0, 285532765421, 483719042947, 88008631996, 1239866073, 0, 0] := by
  decide +kernel

theorem rows1015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1015 = true := by
  decide +kernel

theorem tot1015 : totK PD2M8K2 D2M8K2.t1015 = [0, 109618812264, 393722964811, 358280345598, 41018192558, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
