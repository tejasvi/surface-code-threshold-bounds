import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16088 = true := by
  decide +kernel

theorem tot16088 : totK PD2M8K2 D2M8K2.t16088 = [0, 0, 179602898640, 481864337993, 231611724168, 10560497678, 0, 0] := by
  decide +kernel

theorem rows16089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16089 = true := by
  decide +kernel

theorem tot16089 : totK PD2M8K2 D2M8K2.t16089 = [0, 182603865993, 404524700632, 258152873283, 80100112965, 9677292770, 0, 0] := by
  decide +kernel

theorem rows16090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16090 = true := by
  decide +kernel

theorem tot16090 : totK PD2M8K2 D2M8K2.t16090 = [0, 171993451033, 476876491540, 242591463844, 15430950145, 0, 0, 0] := by
  decide +kernel

theorem rows16091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16091 = true := by
  decide +kernel

theorem tot16091 : totK PD2M8K2 D2M8K2.t16091 = [0, 89733435092, 354186682504, 363763917414, 106038648647, 13136570770, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
