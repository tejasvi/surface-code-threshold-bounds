import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7256 = true := by
  decide +kernel

theorem tot7256 : totK PD2M8K2 D2M8K2.t7256 = [0, 0, 173142159459, 447943089850, 272058003495, 21017471343, 0, 0] := by
  decide +kernel

theorem rows7257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7257 = true := by
  decide +kernel

theorem tot7257 : totK PD2M8K2 D2M8K2.t7257 = [0, 0, 73377429009, 332794529533, 406258215397, 80043950196, 1232398321, 0] := by
  decide +kernel

theorem rows7258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7258 = true := by
  decide +kernel

theorem tot7258 : totK PD2M8K2 D2M8K2.t7258 = [0, 0, 0, 285089669838, 493956168779, 121046649519, 3699256714, 0] := by
  decide +kernel

theorem rows7259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7259 = true := by
  decide +kernel

theorem tot7259 : totK PD2M8K2 D2M8K2.t7259 = [0, 0, 160226755552, 391912291377, 233457401253, 75474362161, 8752647282, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
