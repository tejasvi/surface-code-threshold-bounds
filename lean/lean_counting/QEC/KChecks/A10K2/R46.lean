import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t184 = true := by
  decide +kernel

theorem tot184 : totK PA10K2 A10K2.t184 = [0, 0, 645244210315, 2064810750482, 1738983085273, 403471499908, 25333254304, 0, 0, 0] := by
  decide +kernel

theorem rows185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t185 = true := by
  decide +kernel

theorem tot185 : totK PA10K2 A10K2.t185 = [0, 291577383370, 1235126376005, 1892177775195, 1158398602727, 198442422119, 5447185874, 0, 0, 0] := by
  decide +kernel

theorem rows186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t186 = true := by
  decide +kernel

theorem tot186 : totK PA10K2 A10K2.t186 = [0, 263367341472, 1450037255000, 2125514519369, 789133949720, 58289032897, 0, 0, 0, 0] := by
  decide +kernel

theorem rows187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t187 = true := by
  decide +kernel

theorem tot187 : totK PA10K2 A10K2.t187 = [0, 293915060262, 1198735680608, 1903681326718, 1137860868589, 181023944460, 5705019915, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
