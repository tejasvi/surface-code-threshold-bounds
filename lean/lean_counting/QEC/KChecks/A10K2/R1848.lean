import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7392 = true := by
  decide +kernel

theorem tot7392 : totK PA10K2 A10K2.t7392 = [0, 0, 537014838795, 1929516833115, 2012281049519, 587692933760, 37716629692, 0, 0, 0] := by
  decide +kernel

theorem rows7393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7393 = true := by
  decide +kernel

theorem tot7393 : totK PA10K2 A10K2.t7393 = [0, 0, 256434192103, 1364044019058, 2217348013844, 1135493006832, 125681223029, 0, 0, 0] := by
  decide +kernel

theorem rows7394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7394 = true := by
  decide +kernel

theorem tot7394 : totK PA10K2 A10K2.t7394 = [0, 0, 0, 524584402786, 1965620620162, 2119085064315, 525558464382, 19436041613, 0, 0] := by
  decide +kernel

theorem rows7395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7395 = true := by
  decide +kernel

theorem tot7395 : totK PA10K2 A10K2.t7395 = [0, 0, 0, 434624185532, 1648257067782, 1999436012795, 753957894972, 68939555567, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
