import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13196 = true := by
  decide +kernel

theorem tot13196 : totK PD2M8K2 D2M8K2.t13196 = [0, 179555626722, 461270061255, 244712389342, 22743451038, 0, 0, 0] := by
  decide +kernel

theorem rows13197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13197 = true := by
  decide +kernel

theorem tot13197 : totK PD2M8K2 D2M8K2.t13197 = [0, 200949843092, 471516856802, 221592603690, 12499826157, 0, 0, 0] := by
  decide +kernel

theorem rows13198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13198 = true := by
  decide +kernel

theorem tot13198 : totK PD2M8K2 D2M8K2.t13198 = [0, 30623113973, 315536150318, 452904614077, 95290297502, 1198073392, 0, 0] := by
  decide +kernel

theorem rows13199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13199 = true := by
  decide +kernel

theorem tot13199 : totK PD2M8K2 D2M8K2.t13199 = [0, 0, 198740966866, 472844574198, 195642170702, 12045711471, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
