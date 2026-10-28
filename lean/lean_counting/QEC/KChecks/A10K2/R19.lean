import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows76 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t76 = true := by
  decide +kernel

theorem tot76 : totK PA10K2 A10K2.t76 = [0, 548287642785, 1896253722859, 1908856437438, 516000415687, 30598719114, 0, 0, 0, 0] := by
  decide +kernel

theorem rows77 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t77 = true := by
  decide +kernel

theorem tot77 : totK PA10K2 A10K2.t77 = [0, 0, 709414485822, 2218286361474, 1701989266065, 300336370451, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows78 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t78 = true := by
  decide +kernel

theorem tot78 : totK PA10K2 A10K2.t78 = [42994989285, 71340434420, 420064092154, 1661105669585, 2033879037397, 714845821510, 55515214941, 0, 0, 0] := by
  decide +kernel

theorem rows79 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t79 = true := by
  decide +kernel

theorem tot79 : totK PA10K2 A10K2.t79 = [526620714587, 1938506384969, 1872529144903, 456436485893, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
